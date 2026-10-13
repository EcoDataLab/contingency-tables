import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextCount
import Mathlib.Tactic

namespace Math115.CompletedRepairInjection

open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- Literal full completed defects at fixed labels and actual selected prefix.
The second component retains the entire dense completion. -/
abbrev CompletedDefects (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  (z : DefectProfiles small B s t σ l) ×
    CompletionFibre small B r rbar c cbar (naturalProfile z.val)

/-- Explicit actual completion-retaining map into the true residual-table
child. Only earlier SELECTED entries are fixed; large crossings remain free. -/
def repairToChild {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (a : CompletedDefects small B r rbar c cbar s t σ l) :
    SmallResidualChild small r rbar c cbar s σ (l-1+if t.1=s.1 then 1 else 0) := by
  let Z := defectPairContext hs ht a
  refine ⟨jointRepair hs ht Z.val,?_,?_⟩
  · intro i j hij hbefore
    change repairMatrix Z.val.val.val.1 s t i j=σ (i,j)
    rw [repairMatrix_prefix Z.val.property.1 hst hbefore]
    exact Z.property.1 i j hij hbefore
  · change repairMatrix Z.val.val.val.1 s t s.1 s.2=_
    rw [repairMatrix_special Z.val.property.1,Z.property.2]

/-- Fixed labels recover both full source views, hence the entire profile and
its completion. There is no equality-of-projected-completion-weights premise. -/
theorem repairToChild_injective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t) :
    Function.Injective (repairToChild (B:=B) (r:=r) (rbar:=rbar) (c:=c) (cbar:=cbar)
      (σ:=σ) (l:=l) hs ht hst) := by
  intro a b he
  apply defectPairContext_injective hs ht
  apply Subtype.ext
  apply jointRepair_injective hs ht
  exact congrArg Subtype.val he

lemma repairToChild_matrix {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (a : CompletedDefects small B r rbar c cbar s t σ l) :
    (repairToChild hs ht hst a).val.val.val=repairMatrix a.2.val.val.1 s t := rfl

/-- Full signed inverse formulas on the image, at every selected OR dense
coordinate. They do not assert inverse feasibility for arbitrary child tables. -/
theorem repairToChild_views_recover {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (a : CompletedDefects small B r rbar c cbar s t σ l) :
    ∀ i j,
      (a.2.val.val.1 i j:ℤ)=((repairToChild hs ht hst a).val.val.val i j:ℤ)+
        (if i=t.1 ∧ j=t.2 then 1 else 0)-(if i=t.1 ∧ j=s.2 then 1 else 0) ∧
      (a.2.val.val.2 i j:ℤ)=((repairToChild hs ht hst a).val.val.val i j:ℤ)+
        (if i=s.1 ∧ j=s.2 then 1 else 0)-(if i=t.1 ∧ j=s.2 then 1 else 0) := by
  intro i j
  have hd := defect_fibre_views a.2 hs ht a.1.property.1
  have hx := repairMatrix_cast hd i j
  have hq := hd.2 i j
  simp only [repairToChild_matrix,transferInt] at hx hq ⊢
  constructor <;> omega

/-- A genuine LL crossing increments the dense completion entry by one. The
full source dense value is recovered by subtraction on this image. -/
theorem repairToChild_large_crossing {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (hv : small t.1 s.2=false)
    (a : CompletedDefects small B r rbar c cbar s t σ l) :
    (repairToChild hs ht hst a).val.val.val t.1 s.2=a.2.val.val.1 t.1 s.2+1 ∧
      a.2.val.val.1 t.1 s.2=(repairToChild hs ht hst a).val.val.val t.1 s.2-1 ∧
      a.2.val.val.2 t.1 s.2=a.2.val.val.1 t.1 s.2 := by
  have hcol : s.2≠t.2 := by intro he; rw [he,ht] at hv; contradiction
  have hi := (repairToChild_views_recover hs ht hst a t.1 s.2).1
  simp [hcol] at hi
  have hviews := a.2.property.2.2.2.1 t.1 s.2 hv
  constructor
  · omega
  · exact ⟨by omega,hviews.symm⟩

/-- The source donor is a selected entry of the repaired full table, with the
literal +1 correction exactly when the crossing differs from the donor. -/
theorem repairToChild_donor {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (a : CompletedDefects small B r rbar c cbar s t σ l) :
    a.2.val.val.1 t.1 t.2=(repairToChild hs ht hst a).val.val.val t.1 t.2+
      (if t.2=s.2 then 0 else 1) := by
  have hi := (repairToChild_views_recover hs ht hst a t.1 t.2).1
  by_cases hc : t.2=s.2
  · simp [hc] at hi ⊢
    omega
  · simp [hc] at hi ⊢
    omega

/-- Literal finite reindexing keeps every completion once for its fixed label.
It is an image sum, not a surjectivity or projected-weight comparison claim. -/
theorem donor_sum_eq_repaired_image {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (phi : ℕ → ℝ) :
    (∑ a : CompletedDefects small B r rbar c cbar s t σ l,phi (a.2.val.val.1 t.1 t.2))=
      ∑ A ∈ Finset.univ.image (repairToChild (B:=B) (r:=r) (rbar:=rbar) (c:=c) (cbar:=cbar)
        (σ:=σ) (l:=l) hs ht hst),
        phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1)) := by
  rw [Finset.sum_image (fun a _ b _ he => repairToChild_injective hs ht hst he)]
  apply Finset.sum_congr rfl
  intro a _
  rw [repairToChild_donor hs ht hst a]

/-- Only summands on the actual residual child need be nonnegative. This
permits hard moments whose formula is negative outside the physical support. -/
theorem donor_sum_le_child_of_nonnegative {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (phi : ℕ → ℝ)
    (hphi : ∀ A : SmallResidualChild small r rbar c cbar s σ
      (l-1+if t.1=s.1 then 1 else 0),
      0≤phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1))) :
    (∑ a : CompletedDefects small B r rbar c cbar s t σ l,phi (a.2.val.val.1 t.1 t.2))≤
      ∑ A : SmallResidualChild small r rbar c cbar s σ (l-1+if t.1=s.1 then 1 else 0),
        phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1)) := by
  rw [donor_sum_eq_repaired_image hs ht hst phi]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun A _ _ => hphi A)

/-- Every literal hard weight counts exactly its full completion fibre.
Multiplying by a selected-donor observable preserves this multiplicity. -/
theorem hard_donor_sum_eq_completed {small : I → J → Bool} {B : I → J → ℕ}
    {r : I → ℕ} {c : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (L : ℕ) (ht : small t.1 t.2=true) (phi : ℕ → ℝ) :
    (∑ z : DefectProfiles small B s t σ l,
      phi (smallView small (naturalProfile z.val) false t.1 t.2)*
        hardMarginal small B r c L (naturalProfile z.val))=
    ∑ a : CompletedDefects small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) s t σ l,
      phi (a.2.val.val.1 t.1 t.2) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  have hentry (Z : CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) (naturalProfile z.val)) :
      Z.val.val.1 t.1 t.2=smallView small (naturalProfile z.val) false t.1 t.2 := by
    simpa only [smallView,ht,dite_eq_left] using (Z.property.2.2.1 t.1 t.2 ht).1
  simp_rw [hentry]
  rw [hardMarginal_eq_fibre_card small B r c L _ (naturalProfile_bounded z.val)]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- Exact hard donor-moment reindexing into the completion-retaining repaired
image, including unrestricted dense crossing entries. -/
theorem hard_donor_sum_eq_repaired_image {small : I → J → Bool} {B : I → J → ℕ}
    {r : I → ℕ} {c : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (L : ℕ) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hst : RowMajorBefore s t) (phi : ℕ → ℝ) :
    (∑ z : DefectProfiles small B s t σ l,
      phi (smallView small (naturalProfile z.val) false t.1 t.2)*
        hardMarginal small B r c L (naturalProfile z.val))=
      ∑ A ∈ Finset.univ.image (repairToChild (B:=B) (r:=r)
        (rbar:=fun i => r i+rowLargeCount small i*L) (c:=c)
        (cbar:=fun j => c j+columnLargeCount small j*L) (σ:=σ) (l:=l) hs ht hst),
        phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1)) := by
  rw [hard_donor_sum_eq_completed L ht phi,donor_sum_eq_repaired_image hs ht hst phi]

/-- The usable fixed-label hard-moment bound: genuine hard fibre multiplicities
are dominated by the sum over actual full residual tables in the true child. -/
theorem hard_donor_sum_le_child {small : I → J → Bool} {B : I → J → ℕ}
    {r : I → ℕ} {c : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (L : ℕ) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hst : RowMajorBefore s t) (phi : ℕ → ℝ)
    (hphi : ∀ A : SmallResidualChild small r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) s σ (l-1+if t.1=s.1 then 1 else 0),
      0≤phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1))) :
    (∑ z : DefectProfiles small B s t σ l,
      phi (smallView small (naturalProfile z.val) false t.1 t.2)*
        hardMarginal small B r c L (naturalProfile z.val))≤
      ∑ A : SmallResidualChild small r (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) s σ (l-1+if t.1=s.1 then 1 else 0),
        phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1)) := by
  rw [hard_donor_sum_eq_completed L ht phi]
  exact donor_sum_le_child_of_nonnegative hs ht hst phi hphi

/-- Nonnegative image summands may be upper bounded by the actual full
residual-table child, retaining all original selected partial constraints. -/
theorem donor_sum_le_child {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (phi : ℕ → ℝ) (hphi : ∀ n,0≤phi n) :
    (∑ a : CompletedDefects small B r rbar c cbar s t σ l,phi (a.2.val.val.1 t.1 t.2))≤
      ∑ A : SmallResidualChild small r rbar c cbar s σ (l-1+if t.1=s.1 then 1 else 0),
        phi (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1)) := by
  rw [donor_sum_eq_repaired_image hs ht hst phi]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun A _ _ => hphi _)

end
end Math115.CompletedRepairInjection
