import Chess.Profiling
import Chess.MoveGeneration
import Chess.CachingM

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
      match moves with
      | [] => if b.isInCheck player then pure α₀ else pure drawScore
      | _ =>
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
def getScore (b : Board) (player : Turn) (t : Turn) (α β : Int) (depth : Nat) : CacheM Int := do
  if let .some value ← lookUpCache b then
    if let .some s := value.score then
      return s

  if depth = 0 then
    return b.evaluate player
  else
      let moves := b.possibleMoves t
      if moves.isEmpty then
         return if b.isInCheck player then α₀ else drawScore
      if t = player then
        let s ← (moves.foldlM (fun acc m ↦ if acc > β then pure acc else
          (max acc) <$> (getScore (b.applyMove m) player t.next (max α acc) β depth.pred)) α₀)
        insertScore b s
        pure s
      else
        let s ← (moves.foldlM (fun acc m ↦
          if acc < α then pure acc else
          (min acc) <$> (getScore (b.applyMove m) player t.next α (min β acc) depth.pred)) β₀)
        insertScore b s
        pure s
termination_by depth

def TestBoard1 := FENtoBoard (parseFenString "1rb2bnr/2ppnkpp/p1p1p3/5pq1/8/BP2P1PB/P2P1P1P/RN1QK1NR w KQ - 2 10")

--#time #eval! ((getScore TestBoard1 .White .White α₀ β₀ 3).run ∅).2.size

--#time #eval! (getScore_count TestBoard1 .White .White  α₀ β₀ 3).run 0
--#time #eval! (getScore TestBoard1 .White .White α₀ β₀ 3)


/- TODO Was wenn keine Moves -/
/-- TODO sort moves by score more efficiently -/
def Board.bestMoveM (b : Board) (t : Turn) (depth : Nat) : CacheM (Move × Int) := do
  let moves := (b.possibleMoves t)
  (moves.mergeSort (fun m1 m2 ↦ (b.applyMove m1).evaluate t ≤ (b.applyMove m2).evaluate t)).foldlM (fun acc m ↦ do
            let score ← getScore (b.applyMove m) t t.next acc.2 β₀ depth
            let cache ← get
            dbg_trace cache.size
            if score > acc.2 then pure (m, score) else pure acc) (Move.empty,α₀)


def Board.bestMove (b : Board) (t : Turn) (depth : Nat) : Move × Int :=
  b.bestMoveM t depth |>.run' ∅

--- TODO interator verwenden (INSBESONDERE FÜR MOVE GENERATION???
--- TODO lazy evaluatoin/caching für attack bitboards


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

  let bestMove := board.bestMove .White 6
  stdout.putStr (toString bestMove)
