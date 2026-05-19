import Chess.Defs


def Piece.ofChar (c : Char) : Option Piece :=
  match c with
  | 'p' => some .Pawn
  | 'n' => some .Knight
  | 'b' => some .Bishop
  | 'r' => some .Rook
  | 'q' => some .Queen
  | 'k' => some .King
  | _ => none

def Square.ofChar (c : Char) : Option Square :=
  if c.isUpper then (Piece.ofChar c.toLower).elim none (some ∘ Square.White) else
                  (Piece.ofChar c.toLower).elim none (some ∘ Square.Black)


structure FEN_String where
  figures : Vector String 8
  turn : Turn
deriving Repr
  -- TODO special other stuff

/-- Unidefined Behaviour falls falsch -/
def parseFenString (str : String) : FEN_String := Id.run do
  let split <- str.split " "
  let rows <- split.toList[0]!.split "/" |>.toList
  let mut figures : Vector String 8 := #v["","","","","","","",""]
  for hi : i in [:8] do
    figures := figures.set i rows[i]!.toString
  return ⟨figures,Turn.White⟩

def startString := "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

/-- Undefined behaviour auf falschen fen strings -/
def FENtoBoard (fen : FEN_String) : Board where
  board := Id.run do
    let mut board : Vector Square 64 := Vector.zero
    let mut colPos : Fin 8 := 0
    for hi : i in [:8] do
      colPos := 0
      for c in (fen.figures[i]'(Membership.get_elem_helper hi rfl)).toList do
        match c.toString.toNat? with
        | none =>
          board := board.set (Location.toFin ⟨⟨i, Membership.get_elem_helper hi rfl⟩, colPos⟩) (Square.ofChar c).get!
          colPos := colPos + 1
        | some n => colPos := colPos + (Fin.ofNat 8 n)
    return board

instance : Repr Board where
  reprPrec b n := Id.run do
    let mut res : Std.Format := ""
    for hi : i in [:8] do
      for hj : j in [:8] do
        res := res.append <| Repr.reprPrec (b.SquareAt ⟨⟨i,Membership.get_elem_helper hi rfl⟩, ⟨j, Membership.get_elem_helper hj rfl⟩⟩) 1
      res := res.append "\n"
    return res

instance : One Board where
  one := FENtoBoard (parseFenString startString)
