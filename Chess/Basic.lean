import Chess.Parsing

/-- TODO En passant nicht beachtet und Casteln nicht beachtet -/
def Move.IsValidMove (b : Board) (m : Move) : Prop :=
  match m with
  | Move.move m => (b.SquareAt m.1).IsNonempty ∧ ((b.SquareAt m.2).IsNonempty ∨ (b.SquareAt m.1).IsOppositeColor (b.SquareAt m.2))
  | _ => sorry

/-- TODO edge cases (TODO check for promotion)-/
def Board.applyMove (b : Board) (m : Move) (h : m.IsValidMove b) : Board :=
  dbg_trace (Repr.reprPrec m 10)
  match m with
  | Move.move m => b.ReplaceSquareAt m.1 .Empty |>.ReplaceSquareAt m.2 (b.SquareAt m.1)
  | _ => 1

def Board.getPawnMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves : List Move := []
  for hi : i in [7:57] do -- todo die zahlen stimmen safe nicht
    let location <- ((⟨i, by grind [Membership.get_elem_helper hi rfl]⟩ : Fin 64) : Location)
    if b.SquareAt location = Square.ofTurn t (Piece.Pawn) then
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
  return moves

/-- Wie kann das pferd springen -/
private def shifts : List (Int × Int) := [⟨2, 1⟩, ⟨2,-1⟩, ⟨-2,1⟩, ⟨-2,-1⟩, ⟨1, 2⟩, ⟨1,-2⟩, ⟨-1,2⟩, ⟨-1, -2⟩]

private def generateKnightMoves (l : Location) : List Location :=
  shifts.filterMap (fun s ↦ l.shift s.1 s.2)

def Board.getKnightMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves : List Move := []
  for hi : i in [:64] do
    let location <- ((⟨i, Membership.get_elem_helper hi rfl⟩ : Fin 64) : Location)
    if b.SquareAt location = Square.ofTurn t Piece.Knight then
      -- Ein Springer der richtigen Farbe steht in location
      for target in generateKnightMoves location do
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

def Board.getRookMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves : List Move := []
  for hi : i in [:64] do
    let location <- ((⟨i, Membership.get_elem_helper hi rfl⟩ : Fin 64) : Location)
    if b.SquareAt location = Square.ofTurn t Piece.Rook then
      -- Ein Turm der richtigen Farbe steht in location
      for direction in [(1,0),(-1,0),(0,1),(0,-1)] do
        moves := moves ++ b.moveUntilFail t location direction
  return moves

def Board.getBishopMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves : List Move := []
  for hi : i in [:64] do
    let location <- ((⟨i, Membership.get_elem_helper hi rfl⟩ : Fin 64) : Location)
    if b.SquareAt location = Square.ofTurn t Piece.Bishop then
      -- Ein Turm der richtigen Farbe steht in location
      for direction in [(1,1),(-1,-1),(-1,1),(1,-1)] do
        moves := moves ++ b.moveUntilFail t location direction
  return moves

def Board.getQueenMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves : List Move := []
  for hi : i in [:64] do
    let location <- ((⟨i, Membership.get_elem_helper hi rfl⟩ : Fin 64) : Location)
    if b.SquareAt location = Square.ofTurn t Piece.Queen then
      -- Ein Turm der richtigen Farbe steht in location
      for direction in [(1,1),(-1,-1),(-1,1),(1,-1),(1,0),(-1,0),(0,1),(0,-1)] do
        moves := moves ++ b.moveUntilFail t location direction
  return moves

def Board.getKingMoves (b : Board) (t : Turn) : List Move := Id.run do sorry

def Board.getSpecialMoves (b : Board) (t : Turn) : List Move := Id.run do sorry

def TestBoard := FENtoBoard (parseFenString "8/8/3NP3/8/2r1R3/8/4q3/8 test")

#eval! TestBoard.applyMove (TestBoard.getQueenMoves .Black)[5]! sorry

/- TODO überprüfe auf gepinnte figuren, dass die nicht weglaufen dürfen -/
/-- TODO bauern in die richtige richtung -/
def Board.possibleMoves (b : Board) (t : Turn) : List Move := sorry

section Evalutation

/-- Value from the Perspective of White (black gets counted negatively)-/
def Board.valueWhite (b : Board) : Int :=
  (b.board.map (fun s ↦ match s with
    | .Empty => 0
    | .Black p => -p.value
    | .White p => p.value
  )).sum

def Board.evaluate (b : Board) (t : Turn) : Int := sorry
