import Chess.Parsing
import Batteries.Data.BitVec.Basic
import Chess.CachingM


/-- TODO edge cases (TODO check for promotion)-/
def Board.applyMove (b : Board) (m : Move)  : Board :=
  match m with
  | Move.move m => b.ReplaceSquareAt m.1 0 |>.ReplaceSquareAt m.2 (b.SquareAt m.1)
  | _ => 1

def Board.getPawnMovesAt (b : Board) (t : Turn) (location : Location)
    (h : b.SquareAt location = Square.ofTurn t Piece.Pawn) : List Move := Id.run do
  let mut moves : List Move := []
  -- Ein Bauer der Richtigen Farbe steht in location
  match location.forward t with
  | none => panic! "Bauer auf letztem Rang" -- es geht nicht vorwärts (das sollte eig nicht passieren)
  | some forward_location =>
    if b.SquareAt forward_location |>.IsEmpty then
      moves := (.move ⟨location, forward_location⟩)::moves
      if (if t = .Black then location.row = 1 else location.row = 6) then -- TODO zahlen überprüfen
        -- Wenn bauer auf dem zweiten Rang ist darf er zwei vor
        match forward_location.forward t with
        | none => panic! "Macht keinen sinn hier zu sein" -- todo proof by contradiction, dass muss man garnicht testen hier
        | some forward_forward_location =>
          if b.SquareAt forward_forward_location |>.IsEmpty then
            moves := (.move (location, forward_forward_location))::moves
    match forward_location.shift .zero_pos with
    | none => pure ()
    | some side_location =>
      if (if t = Turn.Black then Square.IsWhite else Square.IsBlack) <| b.SquareAt side_location then
        moves := (.move (location, side_location))::moves
    match forward_location.shift .zero_neg with
    | none => pure ()
    | some side_location =>
      if (if t = Turn.Black then Square.IsWhite else Square.IsBlack) <| b.SquareAt side_location then
        moves := (.move (location, side_location))::moves
  return moves


/-- Wie kann das pferd springen -/
private def shifts : List (Int × Int) := [⟨2, 1⟩, ⟨2,-1⟩, ⟨-2,1⟩, ⟨-2,-1⟩, ⟨1, 2⟩, ⟨1,-2⟩, ⟨-1,2⟩, ⟨-1, -2⟩]

def Board.getKnightMovesAt (b : Board) (t : Turn) (location : Location)
    (h : b.SquareAt location = Square.ofTurn t Piece.Knight) : List Move := Id.run do
  let mut moves : List Move := []
  -- Ein Springer der richtigen Farbe steht in location
  for target in shifts.filterMap (fun s ↦ location.shift' s.1 s.2) do
    if (b.SquareAt target).CanMoveTo t then
      moves := (.move (location, target))::moves
  return moves


def Board.moveUntilFailTr (b : Board) (t : Turn) (base_location : Location) (location : Location) (direction : Direction) (moves : List Move) : List Move :=
  let new_location' := location.shift direction
  match hn : new_location' with
  | none => moves
  | some new_location =>
    have h : new_location.distance_to_edge direction < location.distance_to_edge direction := by
      simp [Location.distance_to_edge] --, Location.row, Location.col]
      subst new_location'
      simp [Location.shift] at hn
      sorry
      --cases direction <;> simp at * <;> simp [← hn.right, Location.row, Location.col]
    match b.SquareAt new_location|>.color with
    | .none => b.moveUntilFailTr t base_location new_location direction ((.move (base_location, new_location))::moves)
    | .some .Black  => if t = .Black then moves else (.move (base_location, new_location))::moves
    | .some .White => if t = .White then moves else (.move (base_location, new_location))::moves
termination_by location.distance_to_edge direction

def Board.moveUntilFailDirectionsTr (b : Board) (t : Turn) (location : Location) (directions : List Direction) (moves : List Move) : List Move :=
  match directions with
  | [] => moves
  | direction::directions' => b.moveUntilFailDirectionsTr t location directions' (b.moveUntilFailTr t location location direction moves)

def Board.getRookMovesAt (b : Board) (t : Turn) (location : Location) (h : b.SquareAt location = Square.ofTurn t Piece.Rook) : List Move := Id.run do
  b.moveUntilFailDirectionsTr t location [.zero_neg, .zero_pos, .pos_zero, .neg_zero] []

def Board.getBishopMovesAt (b : Board) (t : Turn) (location : Location)
  (h : b.SquareAt location = Square.ofTurn t Piece.Bishop) : List Move := Id.run do
  b.moveUntilFailDirectionsTr t location [.neg_neg, .pos_pos, .pos_neg, .neg_pos] []

def Board.getQueenMovesAt (b : Board) (t : Turn)  (location : Location)
  (h : b.SquareAt location = Square.ofTurn t Piece.Queen) : List Move := Id.run do
  b.moveUntilFailDirectionsTr t location [.neg_neg, .pos_pos, .pos_neg, .neg_pos, .zero_neg, .zero_pos, .pos_zero, .neg_zero] []

def Board.getKingMovesAt (b : Board) (t : Turn) (location : Location)
    (h : b.SquareAt location = Square.ofTurn t Piece.King) : List Move := Id.run do
  let mut moves : List Move := []
  for direction in [(1,1),(-1,-1),(-1,1),(1,-1),(1,0),(-1,0),(0,1),(0,-1)] do
    match location.shift' direction.1 direction.2 with
    | none => continue
    | some new_location =>
      if b.SquareAt new_location |>.CanMoveTo t then
        moves := (.move (location, new_location))::moves
  return moves

def Board.getSpecialMoves (b : Board) (t : Turn) : List Move := Id.run do sorry


private def Board.possibleMovesAt (b : Board) (t : Turn) (square : Fin 64) : CacheM (List Move) := do
  let location : Location := square
    match hb : b.SquareAt location |>.toColorPiece with
    | .none => pure []
    | .some (.White, p) =>
      if hw : t = Turn.White then
        pure <| match p with
        | .Pawn => getPawnMovesAt b t location (by sorry) -- über injektivit#t von toColorPiece
        | .Knight => getKnightMovesAt b t location (by sorry)
        | .Bishop => getBishopMovesAt b t location (by sorry)
        | .Rook =>  getRookMovesAt b t location (by sorry)
        | .Queen => getQueenMovesAt b t location (by sorry)
        | .King => getKingMovesAt b t location (by sorry) else pure []
    | .some (.Black, p) =>
      if hw : t = Turn.Black then
        pure <| match p with
        | .Pawn => getPawnMovesAt b t location (by sorry)
        | .Knight => getKnightMovesAt b t location (by sorry)
        | .Bishop => getBishopMovesAt b t location (by sorry)
        | .Rook =>  getRookMovesAt b t location (by sorry)
        | .Queen => getQueenMovesAt b t location (by sorry)
        | .King => getKingMovesAt b t location (by sorry)
      else pure  []

private def Board.possibleMovesTr (b : Board) (t : Turn) (square : Fin 64) (moves : List Move) : CacheM (List Move) := do
  let new_moves ← (let location : Location := square
    match hb : b.SquareAt location |>.toColorPiece with
    | .none => pure moves
    | .some (.White, p) =>
      if hw : t = Turn.White then
        pure <| moves ++ match p with
        | .Pawn => getPawnMovesAt b t location (by sorry) -- über injektivit#t von toColorPiece
        | .Knight => getKnightMovesAt b t location (by sorry)
        | .Bishop => getBishopMovesAt b t location (by sorry)
        | .Rook =>  getRookMovesAt b t location (by sorry)
        | .Queen => getQueenMovesAt b t location (by sorry)
        | .King => getKingMovesAt b t location (by sorry) else pure moves
    | .some (.Black, p) =>
      if hw : t = Turn.Black then
        pure <| moves ++ match p with
        | .Pawn => getPawnMovesAt b t location (by sorry)
        | .Knight => getKnightMovesAt b t location (by sorry)
        | .Bishop => getBishopMovesAt b t location (by sorry)
        | .Rook =>  getRookMovesAt b t location (by sorry)
        | .Queen => getQueenMovesAt b t location (by sorry)
        | .King => getKingMovesAt b t location (by sorry)
      else pure moves)
  if hi : square = 0 then pure new_moves else b.possibleMovesTr t (square.pred' hi) new_moves


def Board.getKingBitVec (b : Board) (t : Turn) : UInt64 :=
  match (b.board.toArray.findIdx? (· = Square.ofTurn t Piece.King)) with
  | .none => dbg_trace "No King"; dbg_trace b.toString; panic! ""
  | .some n => (1 : UInt64) <<< (UInt64.ofNat n)


def dist_in_direction (l : Location) (d : Direction) :=
  match d with
  | .neg_neg | .neg_pos | .zero_neg | .neg_zero => l.toFin
  | _ => 63 - l.toFin

def Board.attackUntilFail (b : Board) (location : Location) (direction : Direction) (pieces soFar : UInt64) : UInt64 :=
  match hl : location.shift direction with
  | none => soFar
  | some new_location =>

    have h : ↑(dist_in_direction new_location direction) < ↑(dist_in_direction location direction) := by
      simp [dist_in_direction, Location.toFin]
      simp [Location.shift, Location.row, Location.col] at hl
      cases direction <;> grind

    let i := new_location.toFin
    if pieces.getBitAt i = true then soFar ||| UInt64.bitAt i
    else b.attackUntilFail new_location direction pieces (soFar ||| UInt64.bitAt i)
termination_by dist_in_direction location direction


def Board.attackUntilFailDirections (b : Board) (location : Location) (directions : List Direction) (pieces soFar : UInt64) :=
  match directions with
  | [] => soFar
  | direction::directions' =>
    b.attackUntilFailDirections location directions' pieces (b.attackUntilFail location direction pieces soFar)

def Board.getPawnAttackAt  (location : Location) (t : Turn) : UInt64 :=
  match location.forward t with
  | none => panic! "Bauer auf letztem Rang" -- es geht nicht vorwärts (das sollte eig nicht passieren)
  | some forward_location =>
    (match forward_location.shift .zero_pos with
    | none => 0
    | some side_location => UInt64.bitAt side_location.toFin) |||
    (match forward_location.shift .zero_neg with
    | none => 0
    | some side_location => UInt64.bitAt side_location.toFin)

def Board.getKnightAttackAt (location : Location) : UInt64 := knightAttackTable[location.toFin]
def Board.getKingAttackAt (location : Location) : UInt64 := kingAttackTable[location.toFin]

/-- Assumes there is a Rook at location -/
def Board.getRookAttackAt (b : Board) (location : Location) (pieces : UInt64) : UInt64 :=
  b.attackUntilFailDirections location [.zero_neg, .zero_pos, .neg_zero, .pos_zero] pieces 0

def Board.getBishopAttackAt (b : Board) (location : Location) (pieces : UInt64) : UInt64 :=
  b.attackUntilFailDirections location [.neg_neg, .pos_pos, .neg_pos, .pos_neg] pieces 0

def Board.getQueenAttackAt (b : Board) (location : Location) (pieces : UInt64) : UInt64 :=
  b.attackUntilFailDirections location [.neg_neg, .pos_pos, .neg_pos, .pos_neg, .zero_neg, .zero_pos, .neg_zero, .pos_zero] pieces 0


/-- boardBitVec in monaden? -/
private def Board.whiteAttackBitVecTr (b : Board) (t : Turn) (square : Fin 64) (soFar boardBitVec : UInt64) :=
  let newAttack := (let location : Location := square
    match hb : (b.SquareAt location).toColorPiece with
    | .some (.White, p)  =>
        soFar ||| match p with
        | .Pawn => getPawnAttackAt location t
        | .Knight => getKnightAttackAt location
        | .Bishop => b.getBishopAttackAt location boardBitVec
        | .Rook =>  b.getRookAttackAt location boardBitVec
        | .Queen => b.getQueenAttackAt location boardBitVec
        | .King => getKingAttackAt location
      | _ => soFar)
  if hi : square = 0 then newAttack else b.whiteAttackBitVecTr t (square.pred' hi) newAttack boardBitVec

/-- boardBitVec in monaden? -/
private def Board.blackAttackBitVecTr (b : Board) (t : Turn) (square : Fin 64) (soFar boardBitVec : UInt64) :=
  let newAttack := (let location : Location := square
    match hb : (b.SquareAt location).toColorPiece with
    | .some (.Black, p)  =>
        soFar ||| match p with
        | .Pawn => getPawnAttackAt location t
        | .Knight => getKnightAttackAt location
        | .Bishop => b.getBishopAttackAt location boardBitVec
        | .Rook =>  b.getRookAttackAt location boardBitVec
        | .Queen => b.getQueenAttackAt location boardBitVec
        | .King => getKingAttackAt location
      | _ => soFar )
  if hi : square = 0 then newAttack else b.blackAttackBitVecTr t (square.pred' hi) newAttack boardBitVec
/-TODO make more efficient -/ -- TODO ist es schlimm wenn man sich selber attacked?
--- TODO überlegen entweder Ja oder Nein
--- Man kann sich selber attacken
/-- All the squares attacked by the Player t  -/
def Board.getAttackBitVec (b : Board) (t : Turn) : CacheM UInt64 := do
/-
  if let Option.some value ← lookUpCache b then
    if t = .Black then
      if let Option.some bitVec := value.blackAttackBitMap then
        return bitVec
    else
      if let Option.some bitVec := value.whiteAttackBitMap then
        return bitVec-/
  let bitVec :=  (match t with
  | .White => b.whiteAttackBitVecTr t 63 0 b.getBitVec
  | .Black => b.blackAttackBitVecTr t 63 0 b.getBitVec)
  --insertAttackBitVec b t bitVec
  return bitVec

def TestBoard := FENtoBoard (parseFenString "8/2K/3NP3/8/2r1R3/8/4q3/8 test")
/-abbrev CounterM := StateM Nat

def tick : CounterM Unit := do
  modify (· + 1)
#eval TestBoard
#eval Board.displayUInt64 <| TestBoard.getAttackBitVec .Black -/
/-- True if the Player t is in check -/
def Board.isInCheck (b : Board) (t : Turn) : CacheM Bool := do
  pure (0 < ((← b.getAttackBitVec t.next) &&& b.getKingBitVec t))

/- TODO nicht list sonder iterator -/
/-- TODO effizienter wenn König im schach steht -/
def Board.possibleMoves (b : Board) (t : Turn) := -- : Std.IterM CacheM (List Move) := mit Type gehts nicht??
  (0...63).iter.flatMapM (fun i ↦ do return (← b.possibleMovesAt t i).iterM _) |>.filterM (fun m ↦ do return (⟨(← Board.isInCheck (b.applyMove m) t).not⟩ : ULift Bool))
--- TODO mit flatMap einen Iter Move draus machen

#check Board.possibleMoves

def Board.isValidMove (b : Board) (t : Turn) (m : Move) : CacheM Bool := do
  pure <| (← (b.possibleMoves t).toList).contains m
--(fun i ↦ (← b.possibleMovesTr t 63 []).filterM (fun m ↦ do pure ¬(← (b.applyMove m).isInCheck t))




--def TestBoard := FENtoBoard (parseFenString "8/8/3NP3/8/2r1R3/8/4q3/8 test")
