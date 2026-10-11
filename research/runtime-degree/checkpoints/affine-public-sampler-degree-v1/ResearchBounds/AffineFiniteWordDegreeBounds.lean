/-
SPDX-License-Identifier: Apache-2.0
Source-only affine-output refinement of the fixed finite-word compiler.
Derived from OpenAI's pinned openai-math finite-word and online-word sources,
and this project's checked generic degree helpers. New refinement, 2026-10-10.
The original checked helpers are imported unchanged. No numerical count or
draw degree certificate is supplied here.
-/
import ResearchBounds.FiniteWordDegreeBounds

namespace Math115.AffineFiniteWordDegree
open OAI OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open OAI.MatchingFPRAS.PhysicalStream OAI.ContingencyTables Polynomial
open Math115.DegreeBounds

variable {A B : Type} [Codec A] [Codec B]

/-- The reserved bit count is numeric: exactly `n a` Boolean cells are
generated. This output bound is independent of count-computation work. -/
lemma source_all_weight (n : A → ℕ) (a : A) :
    (FiniteWordExecution.source n a).All (fun bs => weight bs ≤ 4 * n a + 1) := by
  simpa only [FiniteWordExecution.source, List.length_nil, Nat.add_zero] using
    OnlineWord.all_weight (n a) ([] : List Bool)

/-- Actual encoded input to the supplied-word draw: preserved input plus
the freshly generated Boolean word. Its size is affine in wordMeasure. -/
lemma preserved_pair_all_weight (n : A → ℕ) (a : A) :
    ((FiniteWordExecution.source n a).map (Prod.mk a)).All
      (fun ab => weight ab ≤ (4 * X + 2 : Polynomial ℕ).eval
        (FiniteWordExecution.wordMeasure n a)) := by
  rw [Experiment.all_map]
  apply (source_all_weight n a).mono
  intro bs hbs
  simp only [weight_prod, eval_add, eval_mul, eval_ofNat, eval_X,
    FiniteWordExecution.wordMeasure]
  omega

def completeOnlineDegree (countDegree drawDegree : ℕ) : ℕ :=
  max (max countDegree 6) drawDegree

/-- The complete exact online realizer retains source work degree max(e,6),
while the actual pair fed into F has degree-one output size. -/
lemma complete_online_degree {n : A → ℕ} {f : A × List Bool → B}
    {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f} {e t : ℕ}
    (hN : Typed N e) (hF : Typed F t) :
    OnlineBounded (FiniteWordExecution.realizer N F)
      (FiniteWordExecution.wordMeasure n) (completeOnlineDegree e t) := by
  unfold FiniteWordExecution.realizer
  apply online_congr
  have hid : OnlineBounded (OnlineTree.deterministic (TreeTyped.identity (A := A)))
      (FiniteWordExecution.wordMeasure n) 1 := by
    apply online_deterministic
    simpa only [Nat.mul_one] using
      bounded_remeasure (m := weight) (n := FiniteWordExecution.wordMeasure n)
        (e := 1) (t := 1) (typed_identity (A := A)) X
        (show (X : Polynomial ℕ).natDegree ≤ 1 by simp) (by
          intro a
          simp only [eval_X, FiniteWordExecution.wordMeasure]
          exact Nat.le_add_right (weight a) (n a))
  have hpair := online_pair hid (source_degree hN) X
    (show (X : Polynomial ℕ).natDegree ≤ 1 by simp) (by
      intro a
      simp only [eval_X, FiniteWordExecution.wordMeasure]
      omega)
  have hk : max (max 1 (max e 6)) 1 = max e 6 := by omega
  rw [hk] at hpair
  have hcomp := online_composition hpair (online_deterministic hF) (4 * X + 2)
    (show (4 * X + 2 : Polynomial ℕ).natDegree ≤ 1 by
      simpa using degree_affine 4 2) (by
        intro a
        change ((FiniteWordExecution.source n a).map (Prod.mk a)).All _
        exact preserved_pair_all_weight n a)
  simpa only [Nat.mul_one, completeOnlineDegree] using hcomp

/-- The same physical compiler polynomial and machineTime definition, with
degree twice the improved complete-online bound. -/
theorem machineTime_degree {n : List Symbol → ℕ}
    {f : List Symbol × List Bool → List Symbol}
    {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f} {e t : ℕ}
    (hN : Typed N e) (hF : Typed F t) :
    ∃ q : Polynomial ℕ, q.natDegree ≤ 2 * completeOnlineDegree e t ∧
      ∀ as, FiniteWordExecution.machineTime N F as ≤
        q.eval (FiniteWordExecution.wordMeasure n as) := by
  obtain ⟨p, hp, hpb⟩ := complete_online_degree hN hF
  refine ⟨compilerPolynomial N F p, compiler_degree N F hp ?_,
    compiler_bound N F p hpb⟩
  dsimp [completeOnlineDegree]
  omega

/-- This source refinement is never larger than the preserved published
conditional expression, including zero degree parameters. -/
lemma completeOnlineDegree_le_original (e t : ℕ) :
    completeOnlineDegree e t ≤ DegreeBounds.completeOnlineDegree e t := by
  have hbase : 1 ≤ max e 6 := by omega
  have h1 : max e 6 ≤ max 1 t * max e 6 := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (max e 6) (le_max_left 1 t)
  have h2 : t ≤ max 1 t * max e 6 := by
    calc
      t = t * 1 := by simp
      _ ≤ max 1 t * max e 6 := Nat.mul_le_mul (le_max_right 1 t) hbase
  exact max_le h1 h2

end Math115.AffineFiniteWordDegree
