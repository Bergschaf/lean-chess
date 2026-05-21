import Lean
@[inline]
abbrev Fin.pred' {n : Nat} (i : Fin (n + 1)) (hi : i ≠ 0) : Fin (n + 1) := (i.pred hi).castSucc

@[inline]
abbrev Fin.subSafe {n : Nat} (i : Fin (n + 1)) (s : Nat) (hi : s ≤ i) : Fin (n + 1) :=
   ((@i.castLE _ (n - s + 1 + s) (by grind)).subNat s (by grind)).castLE (by grind)
