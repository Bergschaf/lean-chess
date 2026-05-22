import Std
import Chess.Defs

open Std

structure CacheValue where
  whiteAttackBitMap : Option UInt64
  blackAttackBitMap : Option UInt64
  score : Option Int
deriving BEq

instance : Hashable Board where
  hash b := b.board.foldl (fun acc s ↦ mixHash acc s.val.toUInt64) 5092837452430297021
-- hash b := b.getBitVec -- todo sollte das besser sein?


abbrev CacheM := StateM (HashMap Board CacheValue)

def lookUpCache (b : Board) : CacheM (Option CacheValue) := do
  let cache <- get
  pure <| cache[b]?

-- TODO schauen wie ausgeglichen die hashmap ist

/-- gibt die vollste assoicated list zurück -/
def checkHealth : CacheM Int := do
  let cache ← get
  let buckets := cache.inner.inner.buckets
  return buckets.foldl (fun acc b ↦ max acc b.length) 0

def freshHashMap : HashMap Board CacheValue := .emptyWithCapacity (2^14)

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
  | .none => cache.insert b ⟨.some bv, .none, .none⟩
  | .some val => cache.insert b ⟨.some bv, val.blackAttackBitMap, val.score⟩)
  | .Black =>
  modify (fun cache ↦
  match cache[b]? with
  | .none => cache.insert b ⟨.none, .some bv, .none⟩
  | .some val => cache.insert b ⟨val.whiteAttackBitMap, .some bv, val.score⟩)
