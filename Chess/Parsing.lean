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
          board := board.set (Location.toFin (Location.ofRowCol ⟨i, Membership.get_elem_helper hi rfl⟩ colPos)) (Square.ofChar c).get!
          colPos := colPos + 1
        | some n => colPos := colPos + (Fin.ofNat 8 n)
    return board


def Board.toString (b : Board) : String := Id.run do
  let header := " a b c d e f g h\n"
  let mut res := ""
  for hi : i in [:8] do
    for hj : j in [:8] do
      res := res ++ " " ++ (b.SquareAt (Location.ofRowCol ⟨i,Membership.get_elem_helper hi rfl⟩ ⟨j, Membership.get_elem_helper hj rfl⟩)).toString
    res := res ++ s!" {i+1} \n"
  return header ++ res ++ header

def Board.displayUInt64 (bv : UInt64) : Std.Format := Id.run do
  let header := " a b c d e f g h\n"
  let mut res := ""
  for hi : i in [:8] do
    for hj : j in [:8] do
      res := res ++ " " ++ if (Location.ofRowCol ⟨i,Membership.get_elem_helper hi rfl⟩ ⟨j, Membership.get_elem_helper hj rfl⟩).toUInt64 &&& bv ≠ 0 then "■" else "·"
    res := res ++ s!" {i+1} \n"
  return header ++ res ++ header


private def Location.letterToRowAux (c : Char) : Option (Fin 8) :=
  match c with
  | 'A' => .some 0
  | 'B' => .some 1
  | 'C' => .some 2
  | 'D' => .some 3
  | 'E' => .some 4
  | 'F' => .some 5
  | 'G' => .some 6
  | 'H' => .some 7
  | _ => .none


private def Location.numberToColAux (c : Char) : Option (Fin 8) :=
  match c with
  | '1' => .some 0
  | '2' => .some 1
  | '3' => .some 2
  | '4' => .some 3
  | '5' => .some 4
  | '6' => .some 5
  | '7' => .some 6
  | '8' => .some 7
  | _ => .none


/-- -/
def Location.fromString (s : String) : Option Location := do
  if s.length ≠ 2 then .none else Location.ofRowCol (← Location.numberToColAux (String.Pos.Raw.get s ⟨1⟩)) (← Location.letterToRowAux (String.Pos.Raw.get s ⟨0⟩))


-- TODO keine special moves mit drin
def Move.fromString (s : String) : Option Move := do
  let splits := (s.split "->")
  match splits.toList with
  | start::target::[] => .some (.move (← Location.fromString start.toString, ← Location.fromString target.toString))
  | _ => .none


instance : ToString Board where
  toString b := b.toString

instance : One Board where
  one := FENtoBoard (parseFenString startString)
