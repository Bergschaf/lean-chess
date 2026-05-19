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
    match forward_location.shift 0 1 with
    | none => pure ()
    | some side_location =>
      if (if t = Turn.Black then Square.IsWhite else Square.IsBlack) <| b.SquareAt side_location then
        moves := (.move (location, side_location))::moves
    match forward_location.shift 0 (-1) with
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
  for target in shifts.filterMap (fun s ↦ location.shift s.1 s.2) do
    if (b.SquareAt target).CanMoveTo t then
      moves := (.move (location, target))::moves
  return moves

def Board.moveUntilFail (b : Board) (t : Turn) (location : Location) (direction : Int × Int) : List Move := Id.run do
  let mut moves := []
  let mut new_location := location
  repeat
    match new_location.shift direction.1 direction.2 with
    | none => break
    | some new_location' =>
      match b.SquareAt new_location' with
      | Square.Empty =>
        new_location := new_location'
        moves := (.move (location, new_location))::moves
      | Square.Black _ =>
        unless t = .Black do
         moves := (.move (location, new_location'))::moves
        break
      | Square.White _ =>
        unless t = .White do
         moves := (.move (location, new_location'))::moves
        break
  return moves

def Board.getRookMovesAt (b : Board) (t : Turn) (location : Location) (h : b.SquareAt location = Square.ofTurn t Piece.Rook) : List Move := Id.run do
  -- Ein Turm der richtigen Farbe steht in location
  let mut moves := []
  for direction in [(1,0),(-1,0),(0,1),(0,-1)] do
    moves := moves ++ b.moveUntilFail t location direction
  return moves

def Board.getBishopMovesAt (b : Board) (t : Turn) (location : Location)
  (h : b.SquareAt location = Square.ofTurn t Piece.Bishop) : List Move := Id.run do
  let mut moves : List Move := []
  -- Ein Läufer der richtigen Farbe steht in location
  for direction in [(1,1),(-1,-1),(-1,1),(1,-1)] do
    moves := moves ++ b.moveUntilFail t location direction
  return moves

def Board.getQueenMovesAt (b : Board) (t : Turn)  (location : Location)
  (h : b.SquareAt location = Square.ofTurn t Piece.Queen) : List Move := Id.run do
  let mut moves : List Move := []
  -- Eine Dame der richtigen Farbe steht in location
  for direction in [(1,1),(-1,-1),(-1,1),(1,-1),(1,0),(-1,0),(0,1),(0,-1)] do
    moves := moves ++ b.moveUntilFail t location direction
  return moves

def Board.getKingMovesAt (b : Board) (t : Turn) (location : Location)
    (h : b.SquareAt location = Square.ofTurn t Piece.King) : List Move := Id.run do
  let mut moves : List Move := []
  for direction in [(1,1),(-1,-1),(-1,1),(1,-1),(1,0),(-1,0),(0,1),(0,-1)] do
    match location.shift direction.1 direction.2 with
    | none => continue
    | some new_location =>
      if b.SquareAt new_location |>.CanMoveTo t then
        moves := (.move (location, new_location))::moves
  return moves

def Board.getSpecialMoves (b : Board) (t : Turn) : List Move := Id.run do sorry



/- TODO überprüfe auf gepinnte figuren, dass die nicht weglaufen dürfen -/
def Board.possibleMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves : List Move := []
  for hi : i in [:64] do
    let location <- (⟨i,Membership.get_elem_helper hi rfl⟩ : Fin 64)
    match hb : b.SquareAt location with
    | .Empty => pure ()
    | .White p =>
      if hw : t = .White then
        moves := moves ++ match p with
        | .Pawn => getPawnMovesAt b t location (by rw [hb, hw]; rfl)
        | .Knight => getKnightMovesAt b t location (by rw [hb, hw]; rfl)
        | .Bishop => getBishopMovesAt b t location (by rw [hb, hw]; rfl)
        | .Rook =>  getRookMovesAt b t location (by rw [hb, hw]; rfl)
        | .Queen => getQueenMovesAt b t location (by rw [hb, hw]; rfl)
        | .King => getKingMovesAt b t location (by rw [hb, hw]; rfl)
    | .Black p =>
      if hw : t = .Black then
        moves := moves ++ match p with
        | .Pawn => getPawnMovesAt b t location (by rw [hb, hw]; rfl)
        | .Knight => getKnightMovesAt b t location (by rw [hb, hw]; rfl)
        | .Bishop => getBishopMovesAt b t location (by rw [hb, hw]; rfl)
        | .Rook =>  getRookMovesAt b t location (by rw [hb, hw]; rfl)
        | .Queen => getQueenMovesAt b t location (by rw [hb, hw]; rfl)
        | .King => getKingMovesAt b t location (by rw [hb, hw]; rfl)
  return moves
def TestBoard := FENtoBoard (parseFenString "8/8/3NP3/8/2r1R3/8/4q3/8 test")
