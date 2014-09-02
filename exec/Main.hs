module Main where

import qualified Data.Text.Lazy.IO as Text
import Morte.Core
import Morte.Parser
import Options.Applicative

options :: Parser (FilePath, FilePath)
options =
        (,)
    <$> argument str (metavar "INFILE")
    <*> argument str (metavar "OUTFILE")

main :: IO ()
main = do
    (inFile, outFile) <- execParser $ info (helper <*> options)
        (   fullDesc
        <>  header "morte - A bare-bones calculus of constructions"
        <>  progDesc "Type-check and normalize a Morte program"
        )
    inText <- Text.readFile inFile
    case exprFromText inText of
        Left  pe   -> Text.putStr (prettyParseError pe)
        Right expr -> case typeOf expr of
            Left  te       -> Text.putStr (prettyTypeError te)
            Right typeExpr -> do
                Text.putStrLn (prettyExpr (normalize typeExpr))
                Text.writeFile outFile (prettyExpr (normalize expr))
