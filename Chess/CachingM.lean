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


abbrev CacheM := StateM (HashMap Board CacheValue × Nat)

def lookUpCache (b : Board) : CacheM (Option CacheValue) := do
  let cache <- get
  pure <| cache.1[b]?

-- TODO schauen wie ausgeglichen die hashmap ist

/-- gibt die vollste assoicated list zurück -/
def checkHealth : CacheM Int := do
  let cache ← get
  let buckets := cache.1.inner.inner.buckets
  return buckets.foldl (fun acc b ↦ max acc b.length) 0

def freshHashMap : HashMap Board CacheValue := .emptyWithCapacity (2^14)

-- TODO ist das linear oder macht das faxen?
def insertScore (b : Board) (score : Int) : CacheM Unit := do
  modify (fun cache ↦
  match cache.1[b]? with
  | .none => ⟨cache.1.insert b ⟨.none, .none, .some score⟩, cache.2⟩
  | .some value => ⟨cache.1.insert b ⟨value.whiteAttackBitMap, value.blackAttackBitMap, .some score⟩, cache.2⟩)

def count : CacheM Unit := do
  modify (fun cache ↦
  ⟨cache.1, cache.2 + 1⟩
  )

def insertAttackBitVec (b : Board) (t : Turn) (bv : UInt64) : CacheM Unit := do
  match t with
  | .White =>
  modify (fun cache ↦
  match cache.1[b]? with
  | .none => ⟨cache.1.insert b ⟨.some bv, .none, .none⟩, cache.2⟩
  | .some val => ⟨cache.1.insert b ⟨.some bv, val.blackAttackBitMap, val.score⟩, cache.2⟩)
  | .Black =>
  modify (fun cache ↦
  match cache.1[b]? with
  | .none => ⟨cache.1.insert b ⟨.none, .some bv, .none⟩, cache.2⟩
  | .some val => ⟨cache.1.insert b ⟨val.whiteAttackBitMap, .some bv, val.score⟩,cache.2⟩)
