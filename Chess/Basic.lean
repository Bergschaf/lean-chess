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

def bigScore := 200

structure CounterM (α : Type) where
  val : α
  count : Nat := 0
deriving Repr

instance : Monad CounterM where
  pure a := ⟨a, 1⟩
  bind ma f := let x := f ma.val; ⟨x.val, x.count + ma.count⟩


def getScore (b : Board) (player : Turn) (t : Turn) (depth : Nat) : CounterM Int := do
  match depth with
  | 0 => pure <| b.evaluate player
  | .succ n =>
    if t = player then
      (b.possibleMoves t).foldlM (fun (acc : Int) (m : Move) ↦
      if acc > bigScore then pure acc else (max acc) <$> (getScore (b.applyMove m) player t.next n)) (-1000 : Int)
    else
      (b.possibleMoves t).foldlM (fun acc m ↦
      if -acc > bigScore then pure acc else (min acc) <$> (getScore (b.applyMove m) player t.next n)) (1000 : Int)

/-- TODO Was wenn keine Moves -/
def Board.bestMove (b : Board) (t : Turn) (depth : Nat) : Move × (CounterM Int) :=
  (b.possibleMoves t).map (fun m ↦ (m,getScore (b.applyMove m) t t.next depth)) |>.maxOn? (fun mt ↦ mt.2.val) |>.get!

def TestBoard1 := FENtoBoard (parseFenString "4k3/2pp3p/4b3/1np1p1q1/1N1P3P/4BPP1/P3P3/R2QKBNR test")

#time #eval (Board.bestMove TestBoard1 .Black 3).2

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
