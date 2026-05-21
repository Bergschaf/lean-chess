import Chess.Parsing
import Batteries.Data.BitVec.Basic


/-- TODO En passant nicht beachtet und Casteln nicht beachtet -/
def Move.IsValidMove (b : Board) (m : Move) : Prop :=
  match m with
  | Move.move m => (b.SquareAt m.1).IsNonempty ∧ ((b.SquareAt m.2).IsNonempty ∨ (b.SquareAt m.1).IsOppositeColor (b.SquareAt m.2))
  | _ => sorry

/-- TODO edge cases (TODO check for promotion)-/
def Board.applyMove (b : Board) (m : Move)  : Board :=
  match m with
  | Move.move m => b.ReplaceSquareAt m.1 .Empty |>.ReplaceSquareAt m.2 (b.SquareAt m.1)
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
    match b.SquareAt new_location with
    | .Empty => b.moveUntilFailTr t base_location new_location direction ((.move (location, new_location))::moves)
    | .Black _ => if t = .Black then moves else (.move (base_location, new_location))::moves
    | .White _ => if t = .White then moves else (.move (base_location, new_location))::moves
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


private def Board.possibleMovesTr (b : Board) (t : Turn) (square : Fin 64) (moves : List Move) :=
  let new_moves := (let location : Location := square
    match hb : b.SquareAt location with
    | .Empty => moves
    | .White p =>
      if hw : t = Turn.White then
        moves ++ match p with
        | .Pawn => getPawnMovesAt b t location (by rw [hb, hw]; rfl)
        | .Knight => getKnightMovesAt b t location (by rw [hb, hw]; rfl)
        | .Bishop => getBishopMovesAt b t location (by rw [hb, hw]; rfl)
        | .Rook =>  getRookMovesAt b t location (by rw [hb, hw]; rfl)
        | .Queen => getQueenMovesAt b t location (by rw [hb, hw]; rfl)
        | .King => getKingMovesAt b t location (by rw [hb, hw]; rfl) else moves
    | .Black p =>
      if hw : t = Turn.Black then
        moves ++ match p with
        | .Pawn => getPawnMovesAt b t location (by rw [hb, hw]; rfl)
        | .Knight => getKnightMovesAt b t location (by rw [hb, hw]; rfl)
        | .Bishop => getBishopMovesAt b t location (by rw [hb, hw]; rfl)
        | .Rook =>  getRookMovesAt b t location (by rw [hb, hw]; rfl)
        | .Queen => getQueenMovesAt b t location (by rw [hb, hw]; rfl)
        | .King => getKingMovesAt b t location (by rw [hb, hw]; rfl)
      else moves)
  if square = 0 then new_moves else b.possibleMovesTr t (square - 1) new_moves


def Board.getKingBitVec (b : Board) (t : Turn) : UInt64 :=
  match (b.board.toArray.findIdx? (· = Square.ofTurn t Piece.King)) with
  | .none => dbg_trace "No King"; 0
  | .some n => (1 : UInt64) <<< (UInt64.ofNat n)



@[inline]
def UInt64.ofFin64 (i : Fin 64) : UInt64 := .ofFin <| i.castLT <| by grind


/-- todo da wird zuviel konvertiert -/
@[inline]
def UInt64.getBitAt (x : UInt64) (i : Fin 64) : Bool := (x >>> .ofFin64 i) &&& 1 = 1

@[inline]
def UInt64.bitAt (i : Fin 64) : UInt64 := (1 : UInt64) <<< .ofFin64 i

@[inline]
def UInt64.ofFnTr (f : Fin 64 → Bool) (i : Fin 64) (soFar : UInt64) :=
  if hi : i = 0 then soFar ||| (if f 0 then 1 else 0) else .ofFnTr f (i.pred' hi) (soFar ||| (if f i then (UInt64.bitAt ⟨i, by grind⟩) else 0))

def Board.getPlayerBitVec (b : Board) (p : Turn) : UInt64 :=
  UInt64.ofFnTr (fun i ↦ if p = .Black then (b.SquareAt i).IsBlack else (b.SquareAt i).IsWhite) 63 0

/-- All the pieces -/
def Board.getBitVec (b : Board) : UInt64 := .ofFnTr (fun i ↦ (b.SquareAt i).IsNonempty) 63 0


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
    match hb : b.SquareAt location with
    | .White p  =>
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
    match hb : b.SquareAt location with
    | .Black p  =>
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
def Board.getAttackBitVec (b : Board) (t : Turn) : UInt64 :=
  match t with
  | .White => b.whiteAttackBitVecTr t 63 0 b.getBitVec
  | .Black => b.blackAttackBitVecTr t 63 0 b.getBitVec

def TestBoard := FENtoBoard (parseFenString "8/2K/3NP3/8/2r1R3/8/4q3/8 test")
#eval TestBoard
#eval Board.displayUInt64 <| TestBoard.getAttackBitVec .Black
/-- True if the Player t is in check -/
def Board.isInCheck (b : Board) (t : Turn) : Bool :=
  (b.getAttackBitVec t.next &&& b.getKingBitVec t).toNat > 0

/-- TODO effizienter wenn König im schach steht -/
def Board.possibleMoves (b : Board) (t : Turn) : List Move :=
  (b.possibleMovesTr t 63 []).filter (fun m ↦ ¬(b.applyMove m).isInCheck t)




--def TestBoard := FENtoBoard (parseFenString "8/8/3NP3/8/2r1R3/8/4q3/8 test")
