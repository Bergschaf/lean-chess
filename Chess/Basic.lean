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
  (match t with
  | .White =>  b.valueWhite
  | .Black => -b.valueWhite) + (b.isInCheck t).toInt * (-100)


end Evalutation

abbrev CounterM := StateM Nat

def tick : CounterM Unit := do
  modify (· + 1)

def α₀ := -10000000
def β₀ :=  10000000
def drawScore := -100

/--
α: Sicheres Maximum für Player
β: Sichers Minimum für Gegner
-/
def getScore_count (b : Board) (player : Turn) (t : Turn) (α β : Int) (depth : Nat) : CounterM Int := do
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
            let s ← getScore_count (b.applyMove m) player t.next (max α acc) β n
            pure (max acc s)
          ) α₀
        else
          moves.foldlM (fun acc m ↦ do
            if acc < α then pure acc else
            let s ← getScore_count (b.applyMove m) player t.next α (min β acc) n
            pure (min acc s)
          ) β₀

/--
α: Sicheres Maximum für Player
β: Sichers Minimum für Gegner
-/
def getScore (b : Board) (player : Turn) (t : Turn) (α β : Int) (depth : Nat) : Int :=
  match depth with
  | 0 =>
      b.evaluate player
  | n + 1 =>
      let moves := b.possibleMoves t
      match moves with
      | [] => if b.isInCheck player then α₀ else drawScore
      | _ =>
        if t = player then
          moves.foldl (fun acc m ↦
            if acc > β then acc else
            max acc <| getScore (b.applyMove m) player t.next (max α acc) β n
          ) α₀
        else
          moves.foldl (fun acc m ↦
            if acc < α then acc else
            min acc <| getScore (b.applyMove m) player t.next α (min β acc) n
          ) β₀
def TestBoard1 := FENtoBoard (parseFenString "1rb2bnr/2ppnkpp/p1p1p3/5pq1/8/BP2P1PB/P2P1P1P/RN1QK1NR w KQ - 2 10")
--#time #eval (getScore TestBoard1 .White .White  α₀ β₀ 3).run 0


/- TODO Was wenn keine Moves -/
/-- TODO sort moves by score more efficiently -/
def Board.bestMove (b : Board) (t : Turn) (depth : Nat) : Move × Int :=
  let moves := (b.possibleMoves t)
  (moves.mergeSort (fun m1 m2 ↦ (b.applyMove m1).evaluate t ≤ (b.applyMove m2).evaluate t)).foldl (fun acc m ↦
            let score := getScore (b.applyMove m) t t.next acc.2 β₀ depth
            if score > acc.2 then (m, score) else acc) (Move.empty,α₀)


--- TODO interator verwenden???
--- TODO nicht Fin sondern Uint8 verwenden für location


def main : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout

  stdout.putStr "FEN String: "
  --let fen <- stdin.getLine
  let fen := "1rb2bnr/2ppnkpp/p1p1p3/5pq1/8/BP2P1PB/P2P1P1P/RN1QK1NR w KQ - 2 10"
  let board := FENtoBoard (parseFenString fen)

  stdout.putStr board.toString

  stdout.putStr "SearchDepth?"

  --let depth <- stdin.getLine
  --let depth := (depth.dropEnd 1).toNat!

  let bestMove := board.bestMove .White 4
  stdout.putStr (toString bestMove)
