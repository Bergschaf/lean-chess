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

abbrev CounterM := StateM Nat

def tick : CounterM Unit := do
  modify (· + 1)

def α₀ := -10000000
def β₀ :=  10000000

/--
α: Sicheres Maximum für Player
β: Sichers Minimum für Gegner
-/
def getScore (b : Board) (player : Turn) (t : Turn) (α β : Int) (depth : Nat) : CounterM Int := do
  tick
  match depth with
  | 0 =>
      return b.evaluate player
  | n + 1 =>
      let moves := b.possibleMoves t
      if moves.isEmpty then
        return b.evaluate player
      else
        if t = player then
          moves.foldlM (fun acc m ↦ do
            if acc > β then pure acc else
            let s ← getScore (b.applyMove m) player t.next (max α acc) β n
            pure (max acc s)
          ) α₀
        else
          moves.foldlM (fun acc m ↦ do
            if acc < α then pure acc else
            let s ← getScore (b.applyMove m) player t.next α (min β acc) n
            pure (min acc s)
          ) β₀

def TestBoard1 := FENtoBoard (parseFenString "4k3/2pp3p/4b3/1np1p1q1/1N1P3P/4BPP1/P3P3/R2QKBNR test")
#time #eval (getScore TestBoard1 .White .White  α₀ β₀ 4).run 0


/--/
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
