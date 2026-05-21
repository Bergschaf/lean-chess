import Lean
@[inline]
abbrev Fin.pred' {n : Nat} (i : Fin (n + 1)) (hi : i ≠ 0) : Fin (n + 1) := (i.pred hi).castSucc

@[inline]
abbrev Fin.subSafe {n : Nat} (i : Fin (n + 1)) (s : Nat) (hi : s ≤ i) : Fin (n + 1) :=
   ((@i.castLE _ (n - s + 1 + s) (by grind)).subNat s (by grind)).castLE (by grind)


@[inline]
def UInt64.ofFin64 (i : Fin 64) : UInt64 := .ofFin <| i.castLT <| by grind


/-- todo da wird zuviel konvertiert -/
@[inline]
def UInt64.getBitAt (x : UInt64) (i : Fin 64) : Bool := (x >>> .ofFin64 i) &&& 1 = 1

@[inline]
def UInt64.bitAt (i : Fin 64) : UInt64 := (1 : UInt64) <<< .ofFin64 i

@[inline]
def UInt64.ofFnTr (f : Fin 64 → Bool) (i : Fin 64) (soFar : UInt64) :=
  if hi : i = 0 then soFar ||| (if f 0 then 1 else 0) else .ofFnTr f (i.pred' hi) (soFar ||| (if f i then (UInt64.bitAt ⟨i, by grind⟩) else 0))
