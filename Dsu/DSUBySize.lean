import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

--  
--  I need to capture the fact that a node's size can never go above n
--  even when I'm doing the sum operation in the union
--
-- How do I carry this proof? Is this possible???



-- def sm_inv {n: Nat} ( j : Nat ) (k: Nat) (parent: Fin n -> Fin n) (size: Fin n -> Nat):  := if h: j < n then (
--         if ( parent ( ⟨j,h⟩ ) ) = k  then 1 + (size (⟨j,h ⟩)) + ( sm_inv (j + 1) k)
--         else sm_inv (j + 1) k
--         ) else 0

structure DSU (n: Nat) where
    parent: Fin n -> Fin n
    size : Fin n -> Nat
    size_invariant : forall (i: Fin n), parent i = i ∨ size (parent i) > size i
    size_capped : forall (i: Fin n), size i < n
    sz_is_subtree_size  : ∀ (i : Fin n),
        -- The set of children of i is `{j | parent j = i ∧ j ≠ i}`
        let children := Finset.univ.filter (fun j => parent j = i ∧ j ≠ i)
        size i = Finset.sum children (fun i => size i + 1)


-- #check DSU.mk

-- def dsu := @DSU.mk 10 (fun i => i) (fun i => 0) (by
--     intro i
--     simp at *
--   )

-- def find {n: Nat} (idx: Fin n) (dsu: DSU n) : (Fin n × DSU n)  :=
--     let par := dsu.parent idx
--     if par = idx then (par, dsu)
--     else (
--     find par dsu
--     )
--   termination_by n - dsu.size idx
--   decreasing_by (
--       have size_inv := dsu.size_invariant idx
--       cases size_inv
--       · trivial
--       · apply Nat.sub_lt_sub_left
--         · apply dsu.size_capped
--         · assumption
--   )

inductive SizePreservedDsu {n} (dsu: DSU n) where
   | res (result: DSU n) (h: dsu.size = result.size) 

def find' {n: Nat} (idx: Fin n) (dsu: DSU n) : (Fin n × SizePreservedDsu dsu)  :=
    let par := dsu.parent idx
    if parEqIdx: par = idx then (par, SizePreservedDsu.res dsu (by rfl) )
    else (
      let res := find' par dsu
      let parent :=  Prod.fst res
      let ⟨dsu', hSameSize ⟩  := Prod.snd res
      (parent,  SizePreservedDsu.res ({ dsu' with
                 parent := ( fun i => if (i = idx) then par else dsu'.parent i ) ,
                 size := dsu.size,
                 size_capped := dsu.size_capped,
                 size_invariant := (by
                 intros i
                 by_cases iEqIdx: i = idx
                 · simp [*] at *
                   have sz':= dsu.size_invariant idx
                   cases sz'
                   · trivial
                   · rw [<- hSameSize] at *; trivial
                 · simp [*] at *
                   have sz' := dsu'.size_invariant i
                   cases sz'
                   · left; assumption
                   · right; trivial
                 ),
                 sz_is_subtree_size:= (by
                    intro i
                    simp [*] at *

                 )
                 })  (by simp) )
    )
  termination_by n - dsu.size idx
  decreasing_by (
      have size_inv := dsu.size_invariant idx
      cases size_inv
      · trivial
      · apply Nat.sub_lt_sub_left
        · apply dsu.size_capped
        · assumption
  )

#find ?a <= ?a + ?b 

-- forall parent nodes, the size is the sum of their children nodes size


def union' {n: Nat} (id1: Fin n) (id2: Fin n) (dsu: DSU n) : DSU n :=
    let (p1, ⟨ dsu', hDsu'SameSizeAsDsu ⟩) := find' id1 dsu
    let (p2,  ⟨ dsu'', hDsu''SameSizeAsDsu' ⟩) := find' id2 dsu'
    if p1EqP2: p1 = p2 then dsu''
    else (
        -- assume p1 is the larger one, we'll handle the swap later
         let biggerP := p1
         let smallerP := p2
         {
                 parent := ( fun i => if (i = smallerP) then biggerP else dsu''.parent i ) ,
                 size := (fun i => if (i = biggerP) then dsu''.size smallerP + dsu''.size biggerP + 1 else dsu''.size i ),
                 size_capped := ( by
                    intros i
                    by_cases iEqBiggerP : i = biggerP
                    · simp [*] at *
                      sorry
                    · simp [*] at *
                      apply dsu''.size_capped
                 )  
                 size_invariant := (by
                        intro i
                        by_cases iEqSmallerP : i = smallerP
                        · simp [*] at *
                          right
                          by_cases smallEqBig : smallerP = biggerP
                          · grind
                          · simp [*] at *;
                            omega
                        · simp [*] at *
                          sorry
                          -- right
                          -- by_cases h': i = biggerP
                          -- · simp [*]
                            
                 ),
                 sz_is_subtree_size := (by
                        intro i
                        simp [*] at *
                )
        }
)
