

def testFinSubTr (v : Fin (2^30)) :=
  if hi : (v = 0) then 4 else
   have h : v - 1 < v := by grind
   testFinSubTr (v - 1)
termination_by v.toNat

def testNatSubTr (n : Nat) :=
  if n = 0 then 5 else testNatSubTr (n - 1)

def testUIntSubTr (n : UInt64):=
  if hi : n = 0 then 6 else
    have : (n - 1).toNat < n.toNat := by refine UInt64.lt_iff_toNat_lt.mp (by grind)
    testUIntSubTr (n - 1)
termination_by n.toNat

def testFinPredTr (v : Fin (2^30)) :=
  if hi : (v = 0) then 4 else
   have h : v - 1 < v := by grind
   testFinPredTr (v.pred (by grind)).castSucc
/-
#time #eval testFinSubTr 10000000
#time #eval testNatSubTr 10000000
#time #eval testUIntSubTr 10000000
#time #eval testFinPredTr 10000000 -- im build dann am schnellsten -/
