import Lean

inductive Piece where
  | Pawn
  | Rook
  | Knight
  | Queen
  | Bishop
  | King
deriving DecidableEq

def Piece.value (p : Piece) :=
  match p with
  | Pawn => 10
  | Knight => 30
  | Bishop => 35
  | Rook => 50
  | Queen => 90
  | King => 0

inductive Square where
  | Empty
  | Black (piece : Piece)
  | White (piece : Piece)
deriving DecidableEq

instance : Zero Square where
  zero := .Empty

instance : Inhabited Square where
  default := 0

def Square.toString (s : Square) : String :=
  match s with
  | .Empty => "·"
  | .Black p =>
    match p with
    | .Pawn => "♟"
    | .Knight => "♞"
    | .Bishop => "♝"
    | .Rook => "♜"
    | .Queen => "♛"
    | .King => "♚"
  | .White p =>
    match p with
    | .Pawn => "♙"
    | .Knight => "♘"
    | .Bishop => "♗"
    | .Rook => "♖"
    | .Queen => "♕"
    | .King => "♔"

structure Location where
  row : Fin 8
  column : Fin 8


def Location.toBitVec (l : Location) : BitVec 64 := 1 <<< (l.row * 8 + l.column)

def columnMap : List String := ["A","B","C","D","E","F","G","H"]

instance : ToString Location where
  toString l :=
    columnMap[l.column].append (l.row + 1 : Nat).repr

instance : Coe (Fin 64) Location where
  coe x := ⟨⟨x / 8, by grind⟩, ⟨x % 8,by grind⟩⟩

def Location.toFin (l : Location) : Fin 64 where
  val := l.row * 8 + l.column
  isLt := by grind

#eval (⟨1,7⟩ : Location).toFin
#eval ((15 : Fin 64) : Location)

inductive Turn where
  | White
  | Black
deriving Repr, DecidableEq

def Turn.next (t : Turn) : Turn :=
  match t with
  | .White => .Black
  | .Black => .White

def Square.ofTurn (t : Turn) : Piece → Square :=
  match t with
  | .White => Square.White
  | .Black => Square.Black


/-- TODO beachten wer wo steht -/
def Location.forward (l : Location) (t : Turn) : Option Location :=
  match t with
  | Turn.Black => if l.row < 7 then some ⟨l.row + 1, l.column⟩ else none
  | Turn.White => if l.row > 0 then some ⟨l.row - 1, l.column⟩ else none

inductive Direction where
  | neg_neg
  | pos_pos
  | pos_neg
  | neg_pos
  | zero_neg
  | zero_pos
  | pos_zero
  | neg_zero
deriving Repr
def Location.shift (l : Location) (d : Direction) : Option Location :=
  match d with
  | .neg_neg =>
      if h : l.row = 0 ∨ l.column = 0 then none
      else some ⟨⟨l.row - 1, by grind⟩, ⟨l.column - 1, by grind⟩⟩

  | .pos_pos =>
      if h : l.row = 7 ∨ l.column = 7 then none
      else some ⟨⟨l.row + 1, by grind⟩, ⟨l.column + 1, by grind⟩⟩

  | .pos_neg =>
      if h : l.row = 7 ∨ l.column = 0 then none
      else some ⟨⟨l.row + 1, by grind⟩, ⟨l.column - 1, by grind⟩⟩

  | .neg_pos =>
      if h : l.row = 0 ∨ l.column = 7 then none
      else some ⟨⟨l.row - 1, by grind⟩, ⟨l.column + 1, by grind⟩⟩

  | .zero_neg =>
      if h : l.column = 0 then none
      else some ⟨⟨l.row, by grind⟩, ⟨l.column - 1, by grind⟩⟩

  | .zero_pos =>
      if h : l.column = 7 then none
      else some ⟨⟨l.row, by grind⟩, ⟨l.column + 1, by grind⟩⟩

  | .pos_zero =>
      if h : l.row = 7 then none
      else some ⟨⟨l.row + 1, by grind⟩, ⟨l.column, by grind⟩⟩

  | .neg_zero =>
      if h : l.row = 0 then none
      else some ⟨⟨l.row - 1, by grind⟩, ⟨l.column, by grind⟩⟩
/-- TODO effizientere Versionen die nur links rechts oder oben unten macht -/
def Location.shift' (l : Location) (row : Int) (col : Int) : Option Location :=
  if hi : l.row + row < 0 ∨ l.row + row > 7 ∨ l.column + col < 0 ∨ l.column + col > 7 then none else
    some ⟨⟨(l.row + row).toNat, by grind⟩, ⟨(l.column + col).toNat, by grind⟩⟩

def Location.distance_to_edge (l : Location) (d : Direction) : Nat :=
  match d with
  | .neg_neg =>
      min l.row.toNat l.column.toNat
  | .pos_pos =>
      min (7 - l.row.toNat) (7 - l.column.toNat)
  | .pos_neg =>
      min (7 - l.row.toNat) l.column.toNat
  | .neg_pos =>
      min l.row.toNat (7 - l.column.toNat)
  | .zero_pos =>
      7 - l.column.toNat
  | .zero_neg =>
      l.column.toNat
  | .pos_zero =>
      7 - l.row.toNat
  | .neg_zero =>
      l.row.toNat


namespace Square

def IsWhite (s : Square) : Bool :=
  match s with
  | .Empty => False
  | .Black _ => False
  | .White _ => True

def IsBlack (s : Square) : Bool :=
  match s with
  | .Empty => False
  | .Black _ => True
  | .White _ => False

abbrev IsNonempty (s : Square) : Bool := s ≠ .Empty

abbrev IsEmpty (s : Square) : Bool := s = .Empty

abbrev CanMoveTo (s : Square) (t : Turn) : Bool := s.IsEmpty ||
  match t with
  | .Black => s.IsWhite
  | .White => s.IsBlack

def IsOppositeColor (s1 s2 : Square) : Prop :=
  (s1.IsBlack ∧ s2.IsWhite) ∨ (s1.IsWhite ∧ s2.IsBlack)


end Square

/-- TODO mehr special stuff mit en passant und casteln -/
structure Board where
  board : Vector Square 64
  turn : Turn := .White

inductive Move where
  | move (m : Location × Location)
  | en_passant (l : Location)
  | castle_short (w : Turn)
  | castle_long (w : Turn)

instance : Inhabited Move where
  default := Move.en_passant ⟨0,0⟩

instance : ToString Move where
  toString m :=
    match m with
    | .move m => (toString m.1) ++ " → " ++ toString m.2
    | _ => "Not implemented"

namespace Board

instance : Zero Board where
  zero := ⟨Vector.zero, .White⟩

def SquareAt (b : Board) (l : Location) : Square := b.board[l.toFin]

def ReplaceSquareAt (b : Board) (l : Location) (s : Square) : Board where
  board := b.board.set l.toFin s
  turn := b.turn
