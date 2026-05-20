import Chess.Parsing

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

def Board.moveUntilFailTr (b : Board) (t : Turn) (location : Location) (direction : Direction) (moves : List Move) : List Move :=
  let new_location' := location.shift direction
  match hn : new_location' with
  | none => moves
  | some new_location =>
    have h : new_location.distance_to_edge direction < location.distance_to_edge direction := by
      simp [Location.distance_to_edge]
      subst new_location'
      simp [Location.shift] at hn
      cases direction <;> grind
    match b.SquareAt new_location with
    | .Empty => b.moveUntilFailTr t new_location direction ((.move (location, new_location))::moves)
    | .Black _ => if t = .Black then moves else (.move (location, new_location))::moves
    | .White _ => if t = .White then moves else (.move (location, new_location))::moves
termination_by location.distance_to_edge direction

def Board.moveUntilFailDirectionsTr (b : Board) (t : Turn) (location : Location) (directions : List Direction) (moves : List Move) : List Move :=
  match directions with
  | [] => moves
  | direction::directions' => b.moveUntilFailDirectionsTr t location directions' (b.moveUntilFailTr t location direction moves)

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


def Board.getKingBitVec (b : Board) (t : Turn) : BitVec 64 := sorry

/-TODO make more efficient -/
/-- All the squares attacked by the Player t  -/
def Board.getAttackBitVec (b : Board) (t : Turn) : BitVec 64 :=
  b.possibleMovesTr t 63 [] |>.foldl (fun acc m ↦ acc ||| match m with | .move l => l.2.toBitVec | _ => 0) 0

def TestBoard := FENtoBoard (parseFenString "8/8/3NP3/8/2r1R3/8/4q3/8 test")

#eval TestBoard
#eval TestBoard.getAttackBitVec .White

/-- True if the Player t is in check -/
def Board.IsCheck (b : Board) (t : Turn) : Bool :=

/- TODO überprüfe auf gepinnte figuren, dass die nicht weglaufen dürfen -/
def Board.possibleMoves (b : Board) (t : Turn) : List Move :=
  b.possibleMovesTr t 63 []

--def TestBoard := FENtoBoard (parseFenString "8/8/3NP3/8/2r1R3/8/4q3/8 test")
