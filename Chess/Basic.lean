import Lean

inductive Piece where
  | Pawn
  | Rook
  | Knight
  | Queen
  | Bishop
  | King

def Piece.value (p : Piece) :=
  match p with
  | Pawn => 10
  | Knight => 30
  | Bishop => 35
  | Rook => 50
  | Queen => 90
  | King => 0

def Piece.ofChar (c : Char) : Option Piece :=
  match c with
  | 'p' => some .Pawn
  | 'n' => some .Knight
  | 'b' => some .Bishop
  | 'r' => some .Rook
  | 'q' => some .Queen
  | 'k' => some .King
  | _ => none

inductive Square where
  | Empty
  | Black (piece : Piece)
  | White (piece : Piece)

def Square.ofChar (c : Char) : Option Square :=
  if c.isUpper then (Piece.ofChar c.toLower).elim none (some ∘ Square.White) else
                  (Piece.ofChar c.toLower).elim none (some ∘ Square.Black)


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


def SquareAt (b : Board) (l : Location) : Square := b.board[l.toFin]

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

def ReplaceSquareAt (b : Board) (l : Location) (s : Square) : Board where
  board := b.board.set l.toFin s
  turn := b.turn

end Board

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

/-- TODO bauern in die richtige richtung -/
def Board.possibleMoves (b : Board) (t : Turn) : List Move := sorry

/-- Value from the Perspective of White (black gets counted negatively)-/
def Board.valueWhite (b : Board) : Int :=
  (b.board.map (fun s ↦ match s with
    | .Empty => 0
    | .Black p => -p.value
    | .White p => p.value
  )).sum

def Board.evaluate (b : Board) (t : Turn) : Int := sorry
