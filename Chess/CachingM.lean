import Std
import Chess.Defs

open Std

structure CacheValue where
  whiteAttackBitMap : Option UInt64
  blackAttackBitMap : Option UInt64
  score : Option Int
deriving BEq

instance : Hashable Board where
  hash b := b.getBitVec -- todo sollte das besser sein?


abbrev CacheM := StateM (HashMap Board CacheValue)

def lookUpCache (b : Board) : CacheM (Option CacheValue) := do
  let cache <- get
  pure <| cache[b]?

-- TODO ist das linear oder macht das faxen?
def insertScore (b : Board) (score : Int) : CacheM Unit := do
  modify (fun cache ↦
  match cache[b]? with
  | .none => cache.insert b ⟨.none, .none, .some score⟩
  | .some value => cache.insert b ⟨value.whiteAttackBitMap, value.blackAttackBitMap, .some score⟩)

def insertAttackBitVec (b : Board) (t : Turn) (bv : UInt64) : CacheM Unit := do
  match t with
  | .White =>
  modify (fun cache ↦
  match cache[b]? with
  | .none => cache.insert b ⟨.none, .some bv, .none⟩
  | .some val => cache.insert b ⟨.some bv, val.blackAttackBitMap, val.score⟩)
  | .Black =>
  modify (fun cache ↦
  match cache[b]? with
  | .none => cache.insert b ⟨.some bv, .none, .none⟩
  | .some val => cache.insert b ⟨val.whiteAttackBitMap, .some bv, val.score⟩)
