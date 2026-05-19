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
    | .Empty => " "
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

instance : Coe (Fin 64) Location where
  coe x := ⟨⟨x / 8, by grind⟩, ⟨x % 8,by grind⟩⟩

def Location.toFin (l : Location) : Fin 64 where
  val := l.row * 8 + l.column
  isLt := by grind


inductive Turn where
  | White
  | Black
deriving Repr

def Location.forward (l : Location) (t : Turn) : Option Location :=
  match t with
  | Turn.White => if l.row < 7 then some ⟨l.row + 1, l.column⟩ else none
  | Turn.Black => if l.row > 0 then some ⟨l.row - 1, l.column⟩ else none

namespace Square

def IsWhite (s : Square) : Prop :=
  match s with
  | .Empty => False
  | .Black _ => False
  | .White _ => True

def IsBlack (s : Square) : Prop :=
  match s with
  | .Empty => False
  | .Black _ => True
  | .White _ => False

def IsNonempty (s : Square) : Prop :=
  match s with
  | .Empty => False
  | _ => True

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

namespace Board

instance : Zero Board where
  zero := ⟨Vector.zero, .White⟩

def SquareAt (b : Board) (l : Location) : Square := b.board[l.toFin]

def ReplaceSquareAt (b : Board) (l : Location) (s : Square) : Board where
  board := b.board.set l.toFin s
  turn := b.turn
