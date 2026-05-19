import Chess.MoveGeneration

section Evalutation

/-- Value from the Perspective of White (black gets counted negatively)-/
def Board.valueWhite (b : Board) : Int :=
  (b.board.foldl (fun acc s ↦ acc + match s with
    | Square.Empty => 0
    | .Black p => -(p.value : Int)
    | .White p => p.value
  ) 0 )

def Board.evaluate (b : Board) (t : Turn) : Int :=
  match t with
  | .White =>  b.valueWhite
  | .Black => -b.valueWhite


end Evalutation

inductive MoveTree where
  | leaf (score : Int)
  | node (t : Turn) (children : Array MoveTree)

structure MoveTreeRoot where
  moves : List (Move × MoveTree)

def getMoveTree (b : Board) (player : Turn) (t : Turn) (depth : Nat) : MoveTree :=
  match depth with
  | 0 => .leaf <| b.evaluate player
  | .succ n => .node t <| ((b.possibleMoves t).toArray.map (fun m ↦ getMoveTree (b.applyMove m) player t.next n))

def startMoveTree (b : Board) (t : Turn) (depth : Nat) : MoveTreeRoot where
  moves := (b.possibleMoves t).map <| fun m ↦ (m, getMoveTree (b.applyMove m) t t.next depth)

/-- TODO was wenn keine züge übrig?? -/
def collapseMoveTree (player : Turn) (mt : MoveTree) : Int :=
  match mt with
  | .leaf s => s
  | .node t children =>
    if t = player then
      children.map (collapseMoveTree player) |>.max?.getD 0
    else
      children.map (collapseMoveTree player) |>.min?.getD 0


def Board.bestMove (b : Board) (t : Turn) (depth : Nat) : Move × Int :=
  startMoveTree b t depth |>.moves.map
    (fun mt ↦ (mt.1, collapseMoveTree t mt.2)) |>.maxOn? (fun mt ↦ mt.2) |>.get!

def TestBoard1 := FENtoBoard (parseFenString "4k3/2pp3p/4b3/1np1p1q1/1N1P3P/4BPP1/P3P3/R2QKBNR test")

-- TODO insgesamt DFS und dann alle mit schlechterem Score wegschmeißen

def main : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout

  stdout.putStr "FEN String: "
  --let fen <- stdin.getLine
  let fen := "4k3/2pp3p/4b3/1np1p1q1/1N1P3P/4BPP1/P3P3/R2QKBNR test"
  let board := FENtoBoard (parseFenString fen)

  stdout.putStr board.toString

  stdout.putStr "SearchDepth?"

  --let depth <- stdin.getLine
  --let depth := (depth.dropEnd 1).toNat!

  let bestMove := board.bestMove .White 4
  stdout.putStr (toString bestMove)
