module

public import Camus.BudgetDPDefinitions

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

 theorem mem_forest {M : Address → ℕ → Finset ℕ} {rs : List Address}
    (hrs : rs.Nodup) {k z : ℕ} : z ∈ forest M rs k ↔
      ∃ b s : Address → ℕ,
        (∑ r ∈ rs.toFinset, b r) = k ∧
        (∑ r ∈ rs.toFinset, s r) = z ∧
        ∀ r ∈ rs.toFinset, s r ∈ M r (b r) := by
  classical
  induction rs generalizing k z with
  | nil =>
    simp only [forest,List.toFinset_nil,Finset.sum_empty,Finset.notMem_empty]
    constructor
    · intro h
      split_ifs at h with hk
      · have hz : z=0 := Finset.mem_singleton.mp h
        exact ⟨fun _=>0,fun _=>0,hk.symm,hz.symm,by simp⟩
      · exact (Finset.notMem_empty _ h).elim
    · rintro ⟨b,s,hk,hz,_⟩
      simp [←hk,←hz]
  | cons r rs ih =>
    have hrnot : r ∉ rs.toFinset := by simpa using (List.nodup_cons.mp hrs).1
    have htail := (List.nodup_cons.mp hrs).2
    simp only [forest,mem_convolution]
    constructor
    · rintro ⟨i,j,a,c,hij,ha,hc,hac⟩
      obtain ⟨b,s,hb,hs,hm⟩ := (ih htail).mp hc
      let b' := Function.update b r i
      let s' := Function.update s r a
      have hb' : ∀ x ∈ rs.toFinset, b' x = b x := by
        intro x hx
        have hne : x ≠ r := by intro h; exact hrnot (h ▸ hx)
        exact Function.update_of_ne hne _ _
      have hs' : ∀ x ∈ rs.toFinset, s' x = s x := by
        intro x hx
        have hne : x ≠ r := by intro h; exact hrnot (h ▸ hx)
        exact Function.update_of_ne hne _ _
      refine ⟨b',s',?_,?_,?_⟩
      · rw [List.toFinset_cons,Finset.sum_insert hrnot]
        rw [show b' r = i by simp [b']]
        rw [Finset.sum_congr rfl hb',hb,hij]
      · rw [List.toFinset_cons,Finset.sum_insert hrnot]
        rw [show s' r = a by simp [s']]
        rw [Finset.sum_congr rfl hs',hs,hac]
      · intro x hx
        rw [List.toFinset_cons] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simpa [b',s'] using ha
        · rw [hs' x hx,hb' x hx]
          exact hm x hx
    · rintro ⟨b,s,hb,hs,hm⟩
      refine ⟨b r,∑ x ∈ rs.toFinset, b x,s r,∑ x ∈ rs.toFinset, s x,?_,?_,?_,?_⟩
      · simpa [List.toFinset_cons,Finset.sum_insert hrnot] using hb
      · exact hm r (by simp)
      · exact (ih htail).mpr ⟨b,s,rfl,rfl,fun x hx=>hm x (by simp [hx])⟩
      · simpa [List.toFinset_cons,Finset.sum_insert hrnot] using hs

 theorem forest_attainable {t : PhyloTree} {M : Address → ℕ → Finset ℕ}
    {e : Pair} (_he : EdgeAbove.Admissible t e) (w : Pair → ℕ)
    (hM : ∀ r ∈ hanging t e, ∀ k z, z ∈ M r k →
      ∃ F, FeasibleBelow t r F ∧ F.card = k ∧ value w F = z)
    {k z : ℕ} (hz : z ∈ forest M (hanging t e).toList k) :
    ∃ F : Address → Finset Pair,
      (∀ r ∈ hanging t e, FeasibleBelow t r (F r)) ∧
      (∑ r ∈ hanging t e, (F r).card) = k ∧
      (∑ r ∈ hanging t e, value w (F r)) = z := by
  classical
  obtain ⟨b,s,hb,hs,hm⟩ := (mem_forest (Finset.nodup_toList _)).mp hz
  simp only [Finset.toList_toFinset] at hb hs hm
  have hex r (hr : r ∈ hanging t e) := hM r hr (b r) (s r) (hm r hr)
  let F := fun r => if hr : r ∈ hanging t e then (hex r hr).choose else ∅
  have hF r (hr : r ∈ hanging t e) :
      FeasibleBelow t r (F r) ∧ (F r).card = b r ∧ value w (F r) = s r := by
    simpa only [F,dite_eq_left hr] using (hex r hr).choose_spec
  exact ⟨F,fun r hr=>(hF r hr).1,
    (Finset.sum_congr rfl (fun r hr=>(hF r hr).2.1)).trans hb,
    (Finset.sum_congr rfl (fun r hr=>(hF r hr).2.2)).trans hs⟩

 theorem forest_dominates {t : PhyloTree} {M : Address → ℕ → Finset ℕ}
    {e : Pair} (_he : EdgeAbove.Admissible t e) (w : Pair → ℕ)
    (hM : ∀ r ∈ hanging t e, ∀ F, FeasibleBelow t r F →
      ∃ z ∈ M r F.card, value w F ≤ z)
    (F : Address → Finset Pair) (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    ∃ z ∈ forest M (hanging t e).toList (∑ r ∈ hanging t e, (F r).card),
      (∑ r ∈ hanging t e, value w (F r)) ≤ z := by
  classical
  have hex r (hr : r ∈ hanging t e) := hM r hr (F r) (hF r hr)
  let s := fun r => if hr : r ∈ hanging t e then (hex r hr).choose else 0
  have hs r (hr : r ∈ hanging t e) : s r ∈ M r (F r).card ∧ value w (F r) ≤ s r := by
    simpa only [s,dite_eq_left hr] using (hex r hr).choose_spec
  refine ⟨∑ r ∈ hanging t e, s r,?_,Finset.sum_le_sum (fun r hr=>(hs r hr).2)⟩
  apply (mem_forest (Finset.nodup_toList _)).mpr
  simp only [Finset.toList_toFinset]
  exact ⟨fun r=>(F r).card,s,rfl,rfl,fun r hr=>(hs r hr).1⟩

 theorem card_forest {t : PhyloTree} {e : Pair} (he : EdgeAbove.Admissible t e)
    (F : Address → Finset Pair) (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    ((hanging t e).biUnion F).card = ∑ r ∈ hanging t e, (F r).card := by
  exact Finset.card_biUnion (forest_disjoint (EdgeAbove.footprint_region t e he) F hF)

 theorem card_gall {t : PhyloTree} {e : Pair} (he : EdgeAbove.Admissible t e)
    (F : Address → Finset Pair) (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    (insert e ((hanging t e).biUnion F)).card = 1 + ∑ r ∈ hanging t e, (F r).card := by
  rw [Finset.card_insert_of_notMem (gall_not_mem_forest he F hF),card_forest he F hF]
  omega

end Camus.BudgetDP
