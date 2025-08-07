import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

structure DSU.Data (n: Nat) where
    parent: Fin n -> Fin n
    rank : Fin n -> Nat
    max_rank : Nat
    rank_capped : forall (i: Fin n), rank i < max_rank
    rank_invariant : forall (i: Fin n), parent i = i ∨ rank (parent i) > rank i

inductive Find.Result (n: Nat) (dsu: DSU.Data n) where
    | res (root: Fin n) (resulting_dsu: DSU.Data n) (hSameRank: dsu.rank = resulting_dsu.rank) (hRootBefore : resulting_dsu.parent root = root) (hRootAfter: dsu.parent root = root)

def find' {n: Nat} (idx: Fin n) (dsu: DSU.Data n)
                : Find.Result n dsu  :=
    let par := dsu.parent idx
    if parEqIdx: par = idx then Find.Result.res par dsu (by rfl) (by grind) (by grind)
    else (
      let ⟨parent, dsu', hSameRank, hIsRootBefore, hIsRootAfter ⟩ := find' par dsu 
      Find.Result.res parent ({ dsu' with
                 parent := ( fun i => if (i = idx) then par else dsu'.parent i ) ,
                 max_rank := dsu.max_rank,
                 rank := dsu.rank,
                 rank_invariant := (by
                 intros i
                 by_cases iEqIdx: i = idx
                 · simp [*] at *
                   have sz':= dsu.rank_invariant idx
                   cases sz'
                   · trivial
                   · rw [<- hSameRank] at *; trivial
                 · simp [*] at *
                   have sz' := dsu'.rank_invariant i
                   cases sz'
                   · left; assumption
                   · right; trivial
                 ),
                 rank_capped := (by
                   intro n
                   apply dsu.rank_capped
                 )
                 })
                 (by simp)
                 (by grind)
                 (by grind)
    )
  termination_by dsu.max_rank - dsu.rank idx
  decreasing_by (
      have size_inv := dsu.rank_invariant idx
      cases size_inv
      · trivial
      · apply Nat.sub_lt_sub_left
        · apply dsu.rank_capped
        · assumption
  )

theorem parentRankBigger: forall {n: Nat} (i j: Fin n) (dsu: DSU.Data n),
        ¬ (dsu.parent i = i) ->  (dsu.parent i = j )  -> dsu.rank j > dsu.rank i := by
        intro n i j dsu
        intro hNotRoot
        intro hParent
        cases dsu.rank_invariant i
        · trivial
        · rw [<-hParent]
          assumption

def union'.helper {n: Nat} (smaller_p bigger_p : Fin n ) ( dsu: DSU.Data n ) (hRankBigger: dsu.rank smaller_p < dsu.rank bigger_p )
    : DSU.Data n :=
    { dsu with
    parent := (fun i => if i = smaller_p then bigger_p else dsu.parent i),
    rank := dsu.rank,
    rank_invariant := (by
        intro i
        by_cases h: i = smaller_p
        · simp [*] at *
        · simp [*] at *
          apply dsu.rank_invariant
    ),
    rank_capped := dsu.rank_capped 
    }

def union' {n: Nat} (id1: Fin n) (id2: Fin n) (dsu: DSU.Data n) : DSU.Data n :=
    let ⟨ p1 , dsu', hSameRank', hRootBefore', hRootAfter' ⟩ := find' id1 dsu 
    let ⟨ p2 , dsu'', hSameRank'', hRootBefore'', hRootAfter'' ⟩ := find' id2 dsu'
    if p1EqP2: p1 = p2 then dsu''
    else (
         if h: dsu''.rank p1 < dsu''.rank p2 then
            union'.helper p1 p2 dsu'' h
         else if h': dsu''.rank p2 < dsu''.rank p1 then
            union'.helper p2 p1 dsu'' h' 
         else
            let parent := (fun i => if i = p1 then p2 else dsu''.parent i)
            let rank := ( fun i => if i = p2 then dsu''.rank p2 + 1 else dsu''.rank i)
            let max_rank := if dsu''.max_rank > dsu''.rank p2 + 1 then dsu''.max_rank else dsu''.rank p2 + 2
            let rank_capped := (by
                    intro i
                    by_cases h: i = p2 <;> simp [*] at *
                    · unfold rank ; simp ; unfold max_rank
                      by_cases maxRankLarger: dsu''.max_rank > dsu''.rank p2 + 1 <;> simp [*] at *
                    · unfold rank
                      unfold max_rank
                      simp [*] at *
                      by_cases maxRankLarger: dsu''.max_rank > dsu''.rank p2 + 1 <;> simp [*] at *
                      · exact dsu''.rank_capped i
                      · have dsu''RankILtDsu''MaxRank :
                             dsu''.rank i < dsu''.max_rank := by
                            apply dsu''.rank_capped i
                        omega
                )

            { dsu'' with
                parent := parent,
                rank := rank,
                max_rank :=  max_rank,
                rank_capped := rank_capped,
                rank_invariant := (by
                    clear rank_capped
                    intro i
                    by_cases h: i = p1
                    · simp [*] at *
                      right
                      have hSameRank : dsu''.rank p1 = dsu''.rank p2 := by
                           rw [Nat.eq_iff_le_and_ge]
                           trivial
                      unfold rank
                      by_cases p1EqP2 : p1 = p2 <;> simp [*] at *
                      by_cases parentP1EqP2 : parent p1 = p2 <;> simp [*] at *
                      · grind
                    · simp [*] at *
                      by_cases iIsRoot : parent i = i
                      · left; trivial
                      · right
                        unfold rank
                        by_cases iEqP2 : i = p2 <;> simp [*] at *
                        · unfold parent ; grind
                        · unfold parent
                          simp [*] at *
                          by_cases iParentEqP2 : dsu''.parent i = p2
                          · simp [*] at *
                            have p2RankLtIRank : dsu''.rank i < dsu''.rank p2 := by
                                 apply parentRankBigger i p2 <;> grind
                            omega
                          · simp [*] at *
                            cases (dsu''.rank_invariant i)
                            · grind
                            · assumption
                )
}
)


abbrev DsuM (n: Nat) (a: Type) := StateM (DSU.Data n) a 

-- def DSU.parent {n} (dsu: DSU n) :=
--     DSU.Data.parent dsu

def initDSU (size: Nat): DSU.Data size :=
    @DSU.Data.mk size (fun i => i) (fun i => 0) 1
                 (by intros ; simp) (by intros; simp)


def DSU.find {n} (idx: Fin n) : DsuM n (Fin n) := do
    let dsu <- get
    let ⟨ parent, dsu', _ , _ , _⟩ := find' idx dsu
    set dsu'
    return parent
    
def DSU.union {n} (idx1: Fin n) (idx2: Fin n) : DsuM n Unit := do
    let dsu <- get
    let dsu' := union' idx1 idx2 dsu
    set dsu'

def dsu1 := initDSU 10

def test1 : DsuM 10 Unit := do
    DSU.union 0 1
    DSU.union 2 3
    DSU.union 4 5
    DSU.union 6 7
    DSU.union 8 9
    DSU.union 1 2
    DSU.union 7 8

#eval StateT.run' (test1 >>= (fun  () => DSU.find 0 )) dsu1
#eval StateT.run' (test1 >>= (fun  () => DSU.find 1 )) dsu1
#eval StateT.run' (test1 >>= (fun  () => DSU.find 2 )) dsu1
#eval StateT.run' (test1 >>= (fun  () => DSU.find 3 )) dsu1

#eval StateT.run' (test1 >>= (fun  () => DSU.find 6 )) dsu1
#eval StateT.run' (test1 >>= (fun  () => DSU.find 7 )) dsu1
#eval StateT.run' (test1 >>= (fun  () => DSU.find 8 )) dsu1
#eval StateT.run' (test1 >>= (fun  () => DSU.find 9 )) dsu1
