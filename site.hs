--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.Monoid         (mappend)
import           Hakyll
import           System.Process

coqdoc :: Compiler (Item String)
coqdoc = do
  inputFile <- toFilePath <$> getUnderlying
  unsafeCompiler $
    readProcess "coqc" [ inputFile ] ""
  output <- unsafeCompiler $
            readProcess "coqdoc" [ "--no-index"
                                 , "--stdout"
                                 , "--body-only"
                                 , "--parse-comments"
                                 , "-s"
                                 , inputFile ] ""
  makeItem output

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "posts/*.v" $ do
        route $ setExtension "html"
        compile $ coqdoc
          >>= loadAndApplyTemplate "templates/post.html" defaultContext

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = field "posts" $ \_ -> postList (take 3 . recentFirst)

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/post.html" postCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext


--------------------------------------------------------------------------------
postList :: ([Item String] -> [Item String]) -> Compiler String
postList sortFilter = do
    posts   <- sortFilter <$> loadAll "posts/*"
    itemTpl <- loadBody "templates/post-item.html"
    list    <- applyTemplateList itemTpl postCtx posts
    return list
