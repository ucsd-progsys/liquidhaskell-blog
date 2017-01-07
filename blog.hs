--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import Data.Monoid (mappend)
import Hakyll
import Text.Pandoc

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
  match "static/*/*" $ do
    route idRoute
    compile copyFileCompiler

  match (fromList tops) $ do
    route   $ setExtension "html"
    compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/page.html"    siteCtx
            >>= loadAndApplyTemplate "templates/default.html" siteCtx
            >>= relativizeUrls

  match "posts/*" $ do
    route $ setExtension "html"
    compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

  create ["archive.html"] $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let archiveCtx = listField "posts" postCtx (return posts) `mappend`
                       constField "title" "Archives"            `mappend`
                       siteCtx

      makeItem ""
            >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
            >>= loadAndApplyTemplate "templates/default.html" archiveCtx
            >>= relativizeUrls

  match "templates/*" $ compile templateCompiler

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    siteCtx


-- http://goto.ucsd.edu:8090/index.html#?demo=ANF.hs

siteCtx :: Context String
siteCtx =
    -- constField "baseUrl"            "http://localhost:8000"     `mappend`
    constField "baseUrl"            "https://ucsd-progsys.github.io/liquidhaskell-blog"     `mappend`
    constField "demoUrl"            "http://goto.ucsd.edu:8090/index.html#?demo=" `mappend`
    constField "tutorialUrl"        "http://ucsd-progsys.github.io/lh-workshop"  `mappend`
    constField "codeUrl"            "http://www.github.com/ucsd-progsys/liquidhaskell"  `mappend`
    constField "site_name"          "LiquidHaskell"             `mappend`
    constField "site_description"   "LiquidHaskell Blog"        `mappend`
    constField "site_username"      "Ranjit Jhala"              `mappend`
    constField "twitter_username"   "ranjitjhala"               `mappend`
    constField "github_username"    "ucsd-progsys"              `mappend`
    constField "google_username"    "rjhala@eng.ucsd.edu"       `mappend`
    constField "google_userid"      "u/0/106612421534244742464" `mappend`
    constField "demo"               "SimpleRefinements.hs"      `mappend`
    constField "headerImg"          "sea.jpg"                   `mappend`
    defaultContext

tops :: [Identifier]
tops = [ "index.md" , "about.md" ]
