import Chess.Parsing

/-- TODO En passant nicht beachtet und Casteln nicht beachtet -/
def Move.IsValidMove (b : Board) (m : Move) : Prop :=
  match m with
  | Move.move m => (b.SquareAt m.1).IsNonempty ∧ ((b.SquareAt m.2).IsNonempty ∨ (b.SquareAt m.1).IsOppositeColor (b.SquareAt m.2))
  | _ => sorry

/-- TODO edge cases (TODO check for promotion)-/
def Board.ApplyMove (b : Board) (m : Move) (h : m.IsValidMove b) : Board :=
  match m with
  | Move.move m => b.ReplaceSquareAt m.1 .Empty |>.ReplaceSquareAt m.2 (b.SquareAt m.1)
  | _ => sorry

def Board.getPawnMoves (b : Board) (t : Turn) : List Move := Id.run do
  let mut moves := []
  for hi : i in [:64] do
    let l <- ((⟨i, Membership.get_elem_helper hi rfl⟩ : Fin 64) : Location)
    if b.SquareAt l = Square.White (Piece.Pawn) then
      match l.forward t with
      | none => sorry
      | some forward_l =>







    else sorry


  return moves

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
