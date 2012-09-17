{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
import Data.Array

import Data.Char
import Data.Maybe
import Control.Monad
import Control.Arrow
import Control.Applicative
import Data.Tree.Game_tree.Negascout
import Data.Tree.Game_tree.Game_tree

data Piece = Pawn | Knight | Bishop | Rook | Queen | King deriving (Show, Eq)
data Player = White | Black deriving (Show, Eq)

type Board = Array (Int, Int) (Maybe (Player, Piece))

initialBoard = listArray ((0,0), (7,7)) $ concat
               [ map (Just . (,) White) pieceRow
               , map (Just . (,) White) pawnRow
               , emptyRow
               , emptyRow
               , emptyRow
               , emptyRow
               , map (Just . (,) Black) pawnRow
               , map (Just . (,) Black) pieceRow
               ] where
  pawnRow = replicate 8 Pawn
  pieceRow = [Rook, Knight, Bishop, Queen, King, Bishop, Knight, Rook]
  emptyRow = replicate 8 Nothing

cellChar piece = case piece of
  Knight -> 'n'
  King -> 'k'
  Queen -> 'q'
  Pawn -> 'p'
  Bishop -> 'b'
  Rook -> 'r'

showBoard board = [[ case board ! (row, col) of  
                        Nothing -> ' '
                        Just (player, value) -> (if player == White then toUpper else id) (cellChar value)
                          |col<-[0..7]]|row <- [7,6..0]]
printBoard :: Board -> IO ()
printBoard = mapM_ putStrLn . showBoard

type GameState = (Player, Board)

allCells = range ((0, 0), (7, 7))

addV (x1, y1) (x2, y2) = (x1+x2, y1+y2)

relocate board from to
  | isNothing (board ! from) = []
  | isJust (board ! to) = []
  | otherwise = [board // [(from, Nothing), (to, board ! from)]]

cellRow (r, _) = r
cellColumn (_, c) = c

basePawnRow White = 1
basePawnRow Black = 6

otherPlayer White = Black
otherPlayer Black = White

inBoard (r, c) = in07 r && in07 c where
  in07 x = x >= 0 && x < 8

promotionRow White = 7
promotionRow Black = 0

type Move = String
type Cell = (Int, Int)

cellName :: Cell -> String
cellName (row, col) = [colName col, rowName row] where
  colName n = toEnum $ fromEnum 'a' + n
  rowName n = toEnum $ fromEnum '1' + n
  
promotionName Pawn = ""
promotionName piece = cellChar piece : ""

pawnMoves :: Player -> Cell -> Board -> [(Move, Board)]
pawnMoves player cell board = moves where
  forward = case player of
    White -> (1, 0)
    Black -> (-1, 0)
  forward1 = addV cell forward
  forward2 = addV forward1 forward
  
  moves = do
    target <- destinations
    piece <- if cellRow target == promotionRow player 
               then morphants else [Pawn]
    [(cellName cell ++ cellName target ++ promotionName piece, 
      board // [(cell, Nothing), (target, Just $ (player, piece))])]
  
  destinations = steps ++ captures
  
  steps =
    guard (isNothing $ board ! forward1)
    >> return forward1 ++ (
      guard (cellRow cell == basePawnRow player)
      >> guard (isNothing $ board ! forward2)
      >> return forward2
      )
  morphants = [Knight, Bishop, Rook, Queen]
  captures = [-1, 1] >>= cap where
    cap dirX = do
      guard (inBoard target)
      guard $ isEnemy $ board ! target
      return target
        where
        target = addV forward1 (0, dirX)
        isEnemy (Just (pl, _)) | pl /= player = True
        isEnemy _ = False
    
initialState :: GameState
initialState = (White, initialBoard)

knightMoves player cell board = do
  (dxm, dym) <- [(1,2), (2,1)]
  [dxs, dys] <- replicateM 2 [1, -1]
  let 
    delta = (dxm * dxs, dym * dys)
    target = addV cell delta
  guard (inBoard target)
  case board ! target of
    Just (pl, _) | pl == player -> mzero
    _ -> return $ board // [(cell, Nothing), (target, Just (player, Knight))]

simpleMove board from to = (cellName from ++ cellName to, 
                            board // [(from, Nothing), (to, board ! from)])

directionalMoves player cell board dir = go (addV cell dir) where
  go c = do 
    guard $ inBoard c
    case board ! c of
      Nothing -> [simpleMove board cell c]
                 ++ go (addV c dir)
      Just (pl, _) -> do
        guard $ pl /= player
        [simpleMove board cell c]

rookDirs = ((,0) <$> [1,-1]) ++ ((0,) <$> [1,-1])
bishopDirs = (,) <$> [1,-1] <*> [1,-1]
queenDirs = rookDirs ++ bishopDirs

dirsMoves dirs player cell board = dirs 
                                   >>= directionalMoves player cell board

moves :: GameState -> [(Move, GameState)]
moves (player, board) = map (second $ (,) (otherPlayer player))
                        $ castle ++ enpassant ++ normalMoves where
  castle = []
  enpassant = []
  normalMoves = do
    cell <- allCells 
    case board ! cell of
      Just (p, val) | p == player -> case val of
        Pawn -> pawnMoves player cell board
        Bishop -> dirsMoves bishopDirs player cell board
        Rook -> dirsMoves rookDirs player cell board
        Queen -> dirsMoves queenDirs player cell board
        _ -> []
      _ -> []

printMoves = mapM_ (print . fst) . moves

play :: GameState -> IO ()
play = playNormal where
  playNormal state = prompt state >> playSilent state
  prompt (player, board) = do
    printBoard board
    print player
  playSilent state = do
    move <- getLine
    case move of
      ":moves" -> printMoves state >> playSilent state
      _ -> 
        case lookup move (moves state) of
          Just state -> playNormal state
          Nothing -> putStrLn "Invalid Move!" >> playSilent state
gogo = play initialState

pieceValue p = case p of
  Pawn -> 100
  Knight -> 320
  Bishop -> 330
  Rook -> 500
  Queen -> 900
  King -> 50000

instance Game_tree GameState where
  children = map snd . moves
  is_terminal = (<2) . length . filter (maybe False ((==King) . snd)) . elems . snd
  node_value state@(pl, board) = total + length (moves state) where
    total = sum $ map eval (Data.Array.elems board) where
      eval Nothing = 0
      eval (Just (pl', val)) | pl' == pl = pieceValue val
        | otherwise = - pieceValue val

playItself :: GameState -> [GameState]
playItself state = state : case negascout state 5 of
  ((_ : state' : _), _) -> playItself state'
  _ -> error "negascout gave a list too short"

strangeBoard = [
  "rnbqkbnr"
  , "  pppppp"
  , " p      "
  , "        "
  , "p       "
  , " P      "
  , "PBPPPPPP"
  , "RN QKBNR"
  ]

parsePiece ' ' = Nothing
parsePiece p = Just pp where
  pp | isUpper p = (White, lcpiece (toLower p))
     | otherwise = (Black, lcpiece p)
  lcpiece 'p' = Pawn
  lcpiece 'n' = Knight
  lcpiece 'b' = Bishop
  lcpiece 'r' = Rook
  lcpiece 'k' = King
  lcpiece 'q' = Queen
  lcpiece ch = error $ "Bad piece: " ++ show ch

parseBoard = listArray ((0 :: Int,0 :: Int), (7,7)) . map parsePiece . concat . reverse

entertain :: IO () 
entertain = mapM_ printBoard $ map snd $ playItself $ initialState
