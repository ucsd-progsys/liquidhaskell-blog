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

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
  match "static/*/*" $ do
    route idRoute
    compile copyFileCompiler

  match "posts/*" $ do
    route $ setExtension "html" `composeRoutes`
            dateFolders         `composeRoutes`
            dropPostsPrefix     `composeRoutes`
            appendIndex
    compile $ pandocCompiler
        >>= loadAndApplyTemplate "templates/post.html"    postCtx
        >>= loadAndApplyTemplate "templates/default.html" postCtx
        >>= relativizeUrls

  match "about.md" $ do
    route   $ setExtension "html"
    compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/page.html"    siteCtx
            >>= loadAndApplyTemplate "templates/default.html" siteCtx
            >>= relativizeUrls

  create ["blog.html"] $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let blogCtx = listField "posts" postCtx (return posts)  `mappend`
                    constField "title" "Blog"                 `mappend`
                    constField "demo"  "SimpleRefinements.hs" `mappend`
                    dropIndexHtml "url"                       `mappend`
                    siteCtx

      makeItem ""
        >>= loadAndApplyTemplate "templates/blog.html"    blogCtx
        >>= loadAndApplyTemplate "templates/default.html" blogCtx
        >>= relativizeUrls

  create ["index.html"] $ do
    route   idRoute
    compile $ do
      let indexCtx = constField "demo"  "SimpleRefinements.hs" `mappend`
                     dropIndexHtml "url"                       `mappend`
                     siteCtx

      makeItem ""
        >>= loadAndApplyTemplate "templates/index.html"   indexCtx
        >>= loadAndApplyTemplate "templates/default.html" indexCtx
        >>= relativizeUrls

  match "templates/*" $ compile templateCompiler

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

-- prependCategory :: Routes
-- prependCategory = metadataRoute $ \md -> customRoute $
--     let mbCategory = lookupString "category" md
--        category   = fromMaybe (error "Posts: Post without category") mbCategory
--    in  (category </>) . toFilePath

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
  dateField "date" "%b %e, %Y" `mappend`
  dropIndexHtml "url"          `mappend`
  siteCtx


-- http://goto.ucsd.edu:8090/index.html#?demo=ANF.hs

siteCtx :: Context String
siteCtx =
    -- constField "baseUrl"            "http://localhost:8000"     `mappend`
    constField "baseUrl"            "https://ucsd-progsys.github.io/liquidhaskell-blog"     `mappend`
    constField "demoUrl"            "http://goto.ucsd.edu:8090/index.html#?demo=" `mappend`
    constField "tutorialUrl"        "http://ucsd-progsys.github.io/lh-workshop"  `mappend`
    constField "bookUrl"            "http://ucsd-progsys.github.io/lh-tutorial"  `mappend`
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
