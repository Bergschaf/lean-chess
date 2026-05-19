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

instance : Repr Square where
  reprPrec s _ :=
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

def columnMap : List String := ["A","B","C","D","E","F","G","H"]

instance : Repr Location where
  reprPrec l n :=
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

def Square.ofTurn (t : Turn) : Piece → Square :=
  match t with
  | .White => Square.White
  | .Black => Square.Black


/-- TODO beachten wer wo steht -/
def Location.forward (l : Location) (t : Turn) : Option Location :=
  match t with
  | Turn.Black => if l.row < 7 then some ⟨l.row + 1, l.column⟩ else none
  | Turn.White => if l.row > 0 then some ⟨l.row - 1, l.column⟩ else none

/-- TODO effizientere Versionen die nur links rechts oder oben unten macht -/
def Location.shift (l : Location) (row : Int) (col : Int) : Option Location :=
  if hi : l.row + row < 0 ∨ l.row + row > 7 ∨ l.column + col < 0 ∨ l.column + col > 7 then none else
    some ⟨⟨(l.row + row).toNat, by grind⟩, ⟨(l.column + col).toNat, by grind⟩⟩

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

instance : Repr Move where
  reprPrec m n :=
    match m with
    | .move m => (Repr.reprPrec m.1 10).append " → " |>.append (Repr.reprPrec m.2 10)
    | _ => "Not implemented"

namespace Board

instance : Zero Board where
  zero := ⟨Vector.zero, .White⟩

def SquareAt (b : Board) (l : Location) : Square := b.board[l.toFin]

def ReplaceSquareAt (b : Board) (l : Location) (s : Square) : Board where
  board := b.board.set l.toFin s
  turn := b.turn
