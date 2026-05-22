import Chess.Profiling
import Chess.MoveGeneration
import Chess.CachingM

section Evalutation

/-- Value from the Perspective of White (black gets counted negatively)-/
def Board.valueForWhite (b : Board) : Int :=
  (b.board.foldl (fun acc s ↦ acc + match s.toColorPiece with
    | .none => 0
    | .some (.Black, p) => -(p.value : Int)
    | .some (.White, p) => p.value
  ) 0 )

-- TODO vlt wert der attackierten Pieces mit einbeziehena
def Board.evaluate (b : Board) (t : Turn) : CacheM Int := do
  pure <| (match t with
  | .White =>  b.valueForWhite
  | .Black => -b.valueForWhite) + (← b.isInCheck t).toInt * (-100)


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
def getScore (b : Board) (player : Turn) (t : Turn) (α β : Int) (depth : Nat) : CacheM Int := do
  if let .some value ← lookUpCache b then
    if let .some s := value.score then
      return s

  if depth = 0 then
    b.evaluate player
  else
      let moves ← b.possibleMoves t
      if moves.isEmpty then
         return if ← b.isInCheck player then α₀ else drawScore
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



#time #eval! ((Board.possibleMoves TestBoard1 .White).run ∅).1
#eval! TestBoard1
#eval! Board.displayUInt64 ((TestBoard1.getAttackBitVec .Black).run' ∅)
--#time #eval! ((getScore TestBoard1 .White .White α₀ β₀ 3).run ∅).1

--#time #eval! (getScore_count TestBoard1 .White .White  α₀ β₀ 3).run 0
--#time #eval! (getScore TestBoard1 .White .White α₀ β₀ 3)


/- TODO Was wenn keine Moves -/
/-- TODO sort moves by score more efficiently -/
def Board.bestMoveM (b : Board) (t : Turn) (depth : Nat) : CacheM (Move × Int) := do
  let moves ← (b.possibleMoves t)
  (moves.mergeSort (fun m1 m2 ↦ ((((b.applyMove m1).evaluate t).run' ∅).run ≤ ((b.applyMove m2).evaluate t).run' ∅))).foldlM (fun acc m ↦ do
            let score ← getScore (b.applyMove m) t t.next acc.2 β₀ depth
--            let cache ← get
--            dbg_trace "Max Bucket Size: "
--            dbg_trace ← checkHealth
--            dbg_trace cache.size
            if score > acc.2 then pure (m, score) else pure acc) (Move.empty,α₀)


def Board.bestMove (b : Board) (t : Turn) (depth : Nat) : Move × Int :=
  b.bestMoveM t depth |>.run' freshHashMap

--- TODO interator verwenden (INSBESONDERE FÜR MOVE GENERATION???
--- TODO lazy evaluatoin/caching für attack bitboards

--- TODO promoten5
