import Chess.Util

inductive Turn where
  | White
  | Black
deriving Repr, DecidableEq

/-- True is White, False is Black -/
@[inline]
def Turn.ofBool (b : Bool) : Turn :=
  if b then .White else .Black

@[inline]
def Turn.toBool (t : Turn) : Bool := t = .White

@[unbox]
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


/- TODO nicht pattern matching über toNat-/
@[inline]
def Piece.ofUInt8 (i : UInt8) (h : i < 6) : Piece :=
  match hi : i with
  | 0 => Pawn
  | 1 => Rook
  | 2 => Knight
  | 3 => Queen
  | 4 => Bishop
  | 5 => King
  | _ => Pawn

def Piece.toUInt8 (p : Piece) : {i : UInt8 // i < 6} :=
  match p with
  | Pawn => ⟨0, by grind⟩
  | Rook => ⟨1, by grind⟩
  | Knight => ⟨2, by grind⟩
  | Queen => ⟨3, by grind⟩
  | Bishop => ⟨4, by grind⟩
  | King => ⟨5, by grind⟩


-- TODO ggf optimieren, d.h. square ist nur ein u8 und der rest wird durch API geregelt
/-
inductive Square where
  | Empty
  | Black (piece : Piece)
  | White (piece : Piece)-/

@[inline]
private def Square.pieceBits (i : UInt8) : UInt8 := i &&& 0b111

@[inline]
def Square.whiteBit (i : UInt8) : Bool := (i &&& 0b1000) > 0

@[inline]
def Turn.toWhiteBit (t : Turn) : UInt8 := if t.toBool then 0b1000 else 0

@[inline]
def Square.emptyBit (i : UInt8) : Bool := (i &&& 0b10000) > 0

/--
0 -> empty

-/
structure Square where
  val : UInt8
  wellFormed : Square.pieceBits val < 6 := by simp_all [Square.pieceBits]; decide
deriving DecidableEq

instance : Zero Square where
  zero := {val := 0b10000}

instance : Inhabited Square where
  default := 0

def Square.toColorPiece (s : Square) : Option (Turn × Piece) :=
  if Square.emptyBit s.val then .none else .some (Turn.ofBool (Square.whiteBit s.val), Piece.ofUInt8 (pieceBits s.val) s.wellFormed)

def Square.color (s : Square) : Option Turn :=
  if Square.emptyBit s.val then .none else .some (Turn.ofBool (Square.whiteBit s.val))

def Square.ofColorPiece (t : Turn) (p : Piece) : Square :=
  ⟨t.toWhiteBit ||| p.toUInt8, sorry⟩



def Square.toString (s : Square) : String :=
  match s.toColorPiece with
  | .none => "."
  | .some (.Black, p) =>
    match p with
    | .Pawn => "♟"
    | .Knight => "♞"
    | .Bishop => "♝"
    | .Rook => "♜"
    | .Queen => "♛"
    | .King => "♚"
  | .some (.White, p) =>
    match p with
    | .Pawn => "♙"
    | .Knight => "♘"
    | .Bishop => "♗"
    | .Rook => "♖"
    | .Queen => "♕"
    | .King => "♔"


structure Location where
  idx : Fin 64
deriving BEq

def Location.toFin (l : Location) : Fin 64 := l.idx

def Location.toUInt64 (l : Location) : UInt64 := (1 : UInt64) <<< l.idx.toNat.toUInt64

def Location.ofFin (i : Fin 64) : Location := ⟨i⟩

def Location.row (l : Location) : Fin 8 := ⟨l.idx / 8, (Nat.div_lt_iff_lt_mul (by grind)).mpr (by grind)⟩

def Location.col (l : Location) : Fin 8 := ⟨l.idx % 8, by grind⟩

def Location.ofRowCol (row : Fin 8) (col : Fin 8) : Location := ⟨row * 8 + col, by grind⟩

def colMap : List String := ["A","B","C","D","E","F","G","H"]

instance : ToString Location where
  toString l :=
    colMap[l.col].append (l.row + 1: Nat).repr

instance : Coe (Fin 64) Location where
  coe i := ⟨i⟩

def Turn.next (t : Turn) : Turn :=
  match t with
  | .White => .Black
  | .Black => .White

def Square.ofTurn (t : Turn) : Piece → Square :=
  match t with
  | .White => fun p ↦ ⟨p.toUInt8.val ||| 0b1000, sorry⟩
  | .Black => fun p ↦ ⟨p.toUInt8.val, sorry⟩

/-- TODO beachten wer wo steht -/
def Location.forward (l : Location) (t : Turn) : Option Location :=
  match t with
  | Turn.Black => if l.row < 7 then some ⟨l.idx + 8⟩ else none
  | Turn.White => if l.row > 0 then some ⟨l.idx - 8⟩ else none

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

/-

 a b c d e f g h
 · · · · · · · · 1
 · · ♔ · · · · · 2
 · · · ♘ ♙ · · · 3
 · · · · · · · · 4
 · · ♜ · ♖ · · · 5
 · · · · · · · · 6
 · · · · ♛ · · · 7
 · · · · · · · · 8
 a b c d e f g h

-/
def Location.shift (l : Location) (d : Direction) : Option Location :=
  match d with
  | .neg_neg =>
      if h : l.row = 0 ∨ l.col = 0 then none
      else some ⟨l.idx.subSafe 9 (by grind [Location.row, Location.col])⟩

  | .pos_pos =>
      if h : l.row = 7 ∨ l.col = 7 then none
      else some ⟨l.idx + 9⟩

  | .pos_neg =>
      if h : l.row = 7 ∨ l.col = 0 then none
      else some ⟨l.idx + 7⟩

  | .neg_pos =>
      if h : l.row = 0 ∨ l.col = 7 then none
      else some ⟨l.idx.subSafe 7 (by grind [Location.row, Location.col])⟩

  | .zero_neg =>
      if h : l.col = 0 then none
      else some ⟨l.idx.pred' (by grind [Location.col]) ⟩

  | .zero_pos =>
      if h : l.col = 7 then none
      else some ⟨l.idx + 1⟩

  | .pos_zero =>
      if h : l.row = 7 then none
      else some ⟨l.idx + 8⟩

  | .neg_zero =>
      if h : l.row = 0 then none
      else some ⟨l.idx.subSafe 8 (by grind [Location.row])⟩


/-- TODO effizientere Versionen die nur links rechts oder oben unten macht -/
def Location.shift' (l : Location) (row : Int) (col : Int) : Option Location :=
  if hi : l.row + row < 0 ∨ l.row + row > 7 ∨ l.col + col < 0 ∨ l.col + col > 7 then none else
    some ⟨(l.idx + row * 8 + col).toNat, by simp [Location.row, Location.col] at *; grind⟩

def Location.distance_to_edge (l : Location) (d : Direction) : Nat :=
  match d with
  | .neg_neg =>
      min l.row.toNat l.col.toNat
  | .pos_pos =>
      min (7 - l.row.toNat) (7 - l.col.toNat)
  | .pos_neg =>
      min (7 - l.row.toNat) l.col.toNat
  | .neg_pos =>
      min l.row.toNat (7 - l.col.toNat)
  | .zero_pos =>
      7 - l.col.toNat
  | .zero_neg =>
      l.col.toNat
  | .pos_zero =>
      7 - l.row.toNat
  | .neg_zero =>
      l.row.toNat


namespace Square

@[inline]
def IsWhite (s : Square) : Bool := Square.whiteBit s.val

@[inline]
def IsBlack (s : Square) : Bool := ¬Square.whiteBit s.val

abbrev IsNonempty (s : Square) : Bool := ¬ (Square.emptyBit s.val)

abbrev IsEmpty (s : Square) : Bool := (Square.emptyBit s.val)


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

private def Board.boardEqTr (b1 b2 : Vector Square 64) (i : Fin 64) : Bool :=
  if hi : i = 0 then b1[0].val = b2[0].val
  else
    if b1[i].val = b2[i].val then Board.boardEqTr b1 b2 (i.pred' hi) else false

instance : BEq Board where
  beq b1 b2 := Board.boardEqTr b1.board b2.board 63

inductive Move where
  | move (m : Location × Location)
  | en_passant (l : Location)
  | castle_short (w : Turn)
  | castle_long (w : Turn)
  | empty
deriving BEq

instance : Inhabited Move where
  default := Move.empty

instance : ToString Move where
  toString m :=
    match m with
    | .move m => (toString m.1) ++ " → " ++ toString m.2
    | _ => "Not implemented"

namespace Board

instance : Zero Board where
  zero := ⟨Vector.zero⟩

def SquareAt (b : Board) (l : Location) : Square := b.board[l.toFin]

def ReplaceSquareAt (b : Board) (l : Location) (s : Square) : Board where
  board := b.board.set l.toFin s


def getPlayerBitVec (b : Board) (p : Turn) : UInt64 :=
  UInt64.ofFnTr (fun i ↦ if p = .Black then (b.SquareAt i).IsBlack else (b.SquareAt i).IsWhite) 63 0

/-- All the pieces -/ -- TODO vlt ist das mit foldl schneller
@[inline]
def getBitVec (b : Board) : UInt64 := .ofFnTr (fun i ↦ (b.SquareAt i).IsNonempty) 63 0

/-
private def computeKnightAttacks (location : Location) : BitVec 64 :=
  (shifts.foldl (fun acc s ↦ (match location.shift' s.1 s.2 with | .none => acc | .some new_loc => acc ||| new_loc.toBitVec))) 0

privae def precomputeKnightAttacks : List <| BitVec 64 :=
  (List.finRange 64).map (fun i : Fin 64 ↦ computeKnightAttacks i)-/

def knightAttackTable' := [132096#64, 329728#64, 659712#64, 1319424#64, 2638848#64, 5277696#64, 10489856#64, 4202496#64, 33816580#64, 84410376#64,
  168886289#64, 337772578#64, 675545156#64, 1351090312#64, 2685403152#64, 1075839008#64, 8657044482#64, 21609056261#64,
  43234889994#64, 86469779988#64, 172939559976#64, 345879119952#64, 687463207072#64, 275414786112#64, 2216203387392#64,
  5531918402816#64, 11068131838464#64, 22136263676928#64, 44272527353856#64, 88545054707712#64, 175990581010432#64,
  70506185244672#64, 567348067172352#64, 1416171111120896#64, 2833441750646784#64, 5666883501293568#64,
  11333767002587136#64, 22667534005174272#64, 45053588738670592#64, 18049583422636032#64, 145241105196122112#64,
  362539804446949376#64, 725361088165576704#64, 1450722176331153408#64, 2901444352662306816#64, 5802888705324613632#64,
  11533718717099671552#64, 4620693356194824192#64, 288234782788157440#64, 576469569871282176#64, 1224997833292120064#64,
  2449995666584240128#64, 4899991333168480256#64, 9799982666336960512#64, 1152939783987658752#64,
  2305878468463689728#64, 1128098930098176#64, 2257297371824128#64, 4796069720358912#64, 9592139440717824#64,
  19184278881435648#64, 38368557762871296#64, 4679521487814656#64, 9077567998918656#64]

def knightAttackTable : List UInt64 := [132096, 329728, 659712, 1319424, 2638848, 5277696, 10489856, 4202496, 33816580, 84410376, 168886289, 337772578,
  675545156, 1351090312, 2685403152, 1075839008, 8657044482, 21609056261, 43234889994, 86469779988, 172939559976,
  345879119952, 687463207072, 275414786112, 2216203387392, 5531918402816, 11068131838464, 22136263676928,
  44272527353856, 88545054707712, 175990581010432, 70506185244672, 567348067172352, 1416171111120896, 2833441750646784,
  5666883501293568, 11333767002587136, 22667534005174272, 45053588738670592, 18049583422636032, 145241105196122112,
  362539804446949376, 725361088165576704, 1450722176331153408, 2901444352662306816, 5802888705324613632,
  11533718717099671552, 4620693356194824192, 288234782788157440, 576469569871282176, 1224997833292120064,
  2449995666584240128, 4899991333168480256, 9799982666336960512, 1152939783987658752, 2305878468463689728,
  1128098930098176, 2257297371824128, 4796069720358912, 9592139440717824, 19184278881435648, 38368557762871296,
  4679521487814656, 9077567998918656]

def BitVecList_to_UInt64List (l : List (BitVec 64)) : List UInt64 :=
  l.map (fun b ↦ UInt64.ofBitVec b)


/-

def precomputeKingAttackAt (location : Location) : BitVec 64 :=
  [Direction.neg_neg, .pos_pos, .neg_pos, .pos_neg, .zero_neg, .zero_pos, .neg_zero, .pos_zero].foldl
    (fun acc s ↦ match location.shift s with | .none => acc | .some new_loc => acc ||| new_loc.toBitVec) 0

private def precomputeKingAttacks : List <| BitVec 64 :=
  (List.finRange 64).map (fun i : Fin 64 ↦ precomputeKingAttackAt i)

set_option pp.deepTerms.threshold 100
#eval precomputeKingAttacks
-/

def kingAttackTable' := [770#64, 1797#64, 3594#64, 7188#64, 14376#64, 28752#64, 57504#64, 49216#64, 197123#64, 460039#64, 920078#64, 1840156#64,
  3680312#64, 7360624#64, 14721248#64, 12599488#64, 50463488#64, 117769984#64, 235539968#64, 471079936#64, 942159872#64,
  1884319744#64, 3768639488#64, 3225468928#64, 12918652928#64, 30149115904#64, 60298231808#64, 120596463616#64,
  241192927232#64, 482385854464#64, 964771708928#64, 825720045568#64, 3307175149568#64, 7718173671424#64,
  15436347342848#64, 30872694685696#64, 61745389371392#64, 123490778742784#64, 246981557485568#64, 211384331665408#64,
  846636838289408#64, 1975852459884544#64, 3951704919769088#64, 7903409839538176#64, 15806819679076352#64,
  31613639358152704#64, 63227278716305408#64, 54114388906344448#64, 216739030602088448#64, 505818229730443264#64,
  1011636459460886528#64, 2023272918921773056#64, 4046545837843546112#64, 8093091675687092224#64,
  16186183351374184448#64, 13853283560024178688#64, 144959613005987840#64, 362258295026614272#64, 724516590053228544#64,
  1449033180106457088#64, 2898066360212914176#64, 5796132720425828352#64, 11592265440851656704#64,
  4665729213955833856#64]


def kingAttackTable : List UInt64 := [770, 1797, 3594, 7188, 14376, 28752, 57504, 49216, 197123, 460039, 920078, 1840156, 3680312, 7360624, 14721248,
  12599488, 50463488, 117769984, 235539968, 471079936, 942159872, 1884319744, 3768639488, 3225468928, 12918652928,
  30149115904, 60298231808, 120596463616, 241192927232, 482385854464, 964771708928, 825720045568, 3307175149568,
  7718173671424, 15436347342848, 30872694685696, 61745389371392, 123490778742784, 246981557485568, 211384331665408,
  846636838289408, 1975852459884544, 3951704919769088, 7903409839538176, 15806819679076352, 31613639358152704,
  63227278716305408, 54114388906344448, 216739030602088448, 505818229730443264, 1011636459460886528,
  2023272918921773056, 4046545837843546112, 8093091675687092224, 16186183351374184448, 13853283560024178688,
  144959613005987840, 362258295026614272, 724516590053228544, 1449033180106457088, 2898066360212914176,
  5796132720425828352, 11592265440851656704, 4665729213955833856]
