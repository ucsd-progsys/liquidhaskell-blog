--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Text.Pandoc
import           Data.Maybe (fromMaybe)
import           Data.Monoid (mappend)
import           Hakyll
import           System.FilePath ( (</>), (<.>)
                                 , splitExtension, splitFileName
                                 , takeDirectory )

import Data.Typeable

tagItems :: Tags -> [Item String]
tagItems tags = [ Item "tag" s | (s,_) <- tagsMap tags]
  where
    f         = tagsMakeId tags

tagCtx :: Context String
tagCtx = field "tag" (return . itemBody)

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
  copyStatic
  makePosts >>= makeBlog
  makeAbout
  makeArchive
  makeIndex
  makeTemplates
  makeAtom

copyStatic =
  match "static/*/*" $ do
    route idRoute
    compile copyFileCompiler

makePosts = do
  -- build up tags
  tags <- buildTags "posts/*" (fromCapture "tags/*.html")
  makeTags tags
  match "posts/*" $ do
    route $ setExtension "html" `composeRoutes`
            dateFolders         `composeRoutes`
            dropPostsPrefix     `composeRoutes`
            appendIndex
    compile $ pandocCompiler
        >>= loadAndApplyTemplate "templates/post.html"    (postCtxWithTags tags)
        >>= saveSnapshot "content"
        >>= loadAndApplyTemplate "templates/default.html" (postCtxWithTags tags)
        >>= relativizeUrls
  return tags

makeTags tags =
  tagsRules tags $ \tag pattern -> do
    let title = "Posts tagged \"" ++ tag ++ "\""
    route idRoute
    compile $ do
        posts <- recentFirst =<< loadAll pattern
        let ctx = constField "title" title
                  `mappend` listField "posts" postCtx (return posts)
                  `mappend` pageCtx

        makeItem ""
            >>= loadAndApplyTemplate "templates/tags.html" ctx
            >>= loadAndApplyTemplate "templates/default.html" ctx
            >>= relativizeUrls

makeAbout =
  match "about.md" $ do
    route   $ setExtension "html"
    compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/page.html"    siteCtx
            >>= loadAndApplyTemplate "templates/default.html" siteCtx
            >>= relativizeUrls

makeBlog tags =
  match "blog.md" $ do
    let tags' = tagItems tags
    route $ setExtension "html"
    compile $ do
      posts <- (fmap (take 5) . recentFirst) =<< loadAll "posts/*"
      let blogCtx = listField "posts" postCtx (return posts)  `mappend`
                    listField "tags"  tagCtx  (return tags')  `mappend`
                    pageCtx
      pandocCompiler
        >>= loadAndApplyTemplate "templates/blog.html"    blogCtx
        >>= loadAndApplyTemplate "templates/default.html" blogCtx
        >>= relativizeUrls

makeArchive =
  match "archive.md" $ do
    route $ setExtension "html"
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let ctx = listField "posts" postCtx (return posts)  `mappend`
                pageCtx
      pandocCompiler
        >>= loadAndApplyTemplate "templates/archive.html" ctx
        >>= loadAndApplyTemplate "templates/default.html" ctx
        >>= relativizeUrls

makeIndex =
  match "index.md" $ do
    route $ setExtension "html"
    compile $
      pandocCompiler -- makeItem ""
        >>= loadAndApplyTemplate "templates/index.html"   pageCtx
        >>= relativizeUrls

makeTemplates =
  match "templates/*" $ compile templateCompiler

makeAtom =
  create ["atom.xml"] $ do
    route idRoute
    compile $ do
        let feedCtx = postCtx `mappend` bodyField "description"
        posts <- fmap (take 10) . recentFirst =<<
            loadAllSnapshots "posts/*" "content"
        renderAtom myFeedConfiguration feedCtx posts

myFeedConfiguration :: FeedConfiguration
myFeedConfiguration = FeedConfiguration
  { feedTitle       = "LiquidHaskell Blog"
  , feedDescription = "This feed provides recipes for safe code!"
  , feedAuthorName  = "Ranjit Jhala"
  , feedAuthorEmail = "rjhala@eng.ucsd.edu"
  , feedRoot        = "https://ucsd-progsys.github.io/liquidhaskell-blog"
  }

appendIndex :: Routes
appendIndex = customRoute $ (\(p, e) -> p </> "index" <.> e) . splitExtension . toFilePath

transform :: String -> String
transform url = case splitFileName url of
                  (p, "index.html") -> takeDirectory p
                  _                 -> url

dropIndexHtml :: String -> Context a
dropIndexHtml key = mapContext transform (urlField key)
  where
    transform url = case splitFileName url of
                      (p, "index.html") -> takeDirectory p
                      _                 -> url

dateFolders :: Routes
dateFolders =
  gsubRoute "/[0-9]{4}-[0-9]{2}-[0-9]{2}-" $ replaceAll "-" (const "/")

dropPostsPrefix :: Routes
dropPostsPrefix = gsubRoute "posts/" $ const ""

--------------------------------------------------------------------------------
postCtxWithTags :: Tags -> Context String
postCtxWithTags tags =
  tagsField "tags" tags `mappend`
  postCtx

postCtx :: Context String
postCtx =
  dateField "date" "%b %e, %Y" `mappend`
  dropIndexHtml "url"          `mappend`
  siteCtx

pageCtx :: Context String
pageCtx =
  constField "demo"  "SimpleRefinements.hs" `mappend`
  dropIndexHtml "url"                       `mappend`
  siteCtx
-- http://goto.ucsd.edu:8090/index.html#?demo=ANF.hs

siteCtx :: Context String
siteCtx =
    -- constField "baseUrl"            "http://localhost:8000"     `mappend`
    constField "baseUrl"            "https://ucsd-progsys.github.io/liquidhaskell-blog"     `mappend`
    constField "demoUrl"            "http://goto.ucsd.edu:8090/index.html#?demo=" `mappend`
    constField "tutorialUrl"        "http://ucsd-progsys.github.io/lh-workshop"  `mappend`
    constField "bookUrl"            "http://ucsd-progsys.github.io/liquidhaskell-tutorial"  `mappend`
    constField "codeUrl"            "http://www.github.com/ucsd-progsys/liquidhaskell"  `mappend`
    constField "site_name"          "LiquidHaskell"             `mappend`
    constField "site_description"   "LiquidHaskell Blog"        `mappend`
    constField "site_username"      "Ranjit Jhala"              `mappend`
    constField "twitter_username"   "ranjitjhala"               `mappend`
    constField "github_username"    "ucsd-progsys"              `mappend`
    constField "google_username"    "rjhala@eng.ucsd.edu"       `mappend`
    constField "google_userid"      "u/0/106612421534244742464" `mappend`
    -- constField "demo"               "SimpleRefinements.hs"      `mappend`
    constField "headerImg"          "sea.jpg"                   `mappend`
    constField "summary"            "todo"                      `mappend`
    constField "disqus_short_name"  "liquidhaskell"             `mappend`
    defaultContext
