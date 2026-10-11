/- Private quantitative lift of the actual pinned finite-word compiler.
   Both public deterministic degree obligations remain hypotheses. -/
import ResearchBounds.FreshBitDegreeBounds
import ResearchBounds.PolynomialCompilerDegree
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine

namespace Math115.DegreeBounds
open OAI OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open OAI.MatchingFPRAS.PhysicalStream OAI.ContingencyTables Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma online_weaken {f : A→Experiment B} {F : OnlineTree.Realizer f} {m : A→ℕ} {e t : ℕ}
    (hF : OnlineBounded F m e) (het : e≤t) : OnlineBounded F m t := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp.trans het,hpb⟩

lemma source_degree {n : A→ℕ} {N : TreeTyped.Realizer n} {e : ℕ} (hN : Typed N e) :
    OnlineBounded (FiniteWordExecution.sourceRealizer N)
      (FiniteWordExecution.wordMeasure n) (max e 6) := by
  unfold FiniteWordExecution.sourceRealizer
  apply online_congr
  have hN' : OnlineBounded (OnlineTree.deterministic N)
      (FiniteWordExecution.wordMeasure n) e := by
    apply online_deterministic
    simpa only [Nat.mul_one] using
      bounded_remeasure (m:=weight) (n:=FiniteWordExecution.wordMeasure n) (e:=e) (t:=1)
        hN X (show (X : Polynomial ℕ).natDegree≤1 by simp) (by
          intro a
          simp only [eval_X,FiniteWordExecution.wordMeasure]
          exact Nat.le_add_right (weight a) (n a))
  apply online_composition hN' fresh_natural_degree (5*X+1)
    (show (5*X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 5 1)
  intro a
  change n a+weight (n a)≤(5*X+1).eval (FiniteWordExecution.wordMeasure n a)
  have hw := weight_nat_numeric (n a)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one,FiniteWordExecution.wordMeasure]
  omega

def completeOnlineDegree (countDegree drawDegree : ℕ) : ℕ :=
  max 1 drawDegree * max countDegree 6

/-- Complete online experiment, including preserved input, fresh bits and
    final encoded output. N and F are precisely the compiler's actual inputs. -/
lemma complete_online_degree {n : A→ℕ} {f : A×List Bool→B}
    {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f} {e t : ℕ}
    (hN : Typed N e) (hF : Typed F t) :
    OnlineBounded (FiniteWordExecution.realizer N F)
      (FiniteWordExecution.wordMeasure n) (completeOnlineDegree e t) := by
  unfold FiniteWordExecution.realizer
  apply online_congr
  have hid : OnlineBounded (OnlineTree.deterministic (TreeTyped.identity (A:=A)))
      (FiniteWordExecution.wordMeasure n) 1 := by
    apply online_deterministic
    simpa only [Nat.mul_one] using
      bounded_remeasure (m:=weight) (n:=FiniteWordExecution.wordMeasure n) (e:=1) (t:=1)
        (typed_identity (A:=A)) X (show (X : Polynomial ℕ).natDegree≤1 by simp) (by
          intro a
          simp only [eval_X,FiniteWordExecution.wordMeasure]
          exact Nat.le_add_right (weight a) (n a))
  have hpair := online_pair hid (source_degree hN) X
    (show (X : Polynomial ℕ).natDegree≤1 by simp) (by
      intro a
      simp only [eval_X,FiniteWordExecution.wordMeasure]
      omega)
  have hk : max (max 1 (max e 6)) 1 = max e 6 := by omega
  rw [hk] at hpair
  apply online_weaken (online_then hpair (online_deterministic hF))
  dsimp [completeOnlineDegree]
  apply max_le
  · exact le_trans (by omega : max e 6≤1*max e 6)
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · exact Nat.mul_le_mul_right _ (le_max_right _ _)

noncomputable def compilerPolynomial {n : List Symbol→ℕ}
    {f : List Symbol×List Bool→List Symbol}
    (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) (p : Polynomial ℕ) : Polynomial ℕ :=
  let G := FiniteWordExecution.realizer N F
  let a := OnlineStack.accesses G.program.code
  let o := OnlineStack.overhead G.program.code
  let pk := (1+LiteralProgram.budgetPolynomial 1 (18*LiteralPacked.width) X 0)*
    C (MachineCost.programCost LiteralPacked.packCode)
  let out := C (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))+
    (1+LiteralProgram.budgetPolynomial (18*LiteralPacked.width) 1 p 0)*
      C (MachineCost.programCost LiteralPacked.unpackCode)
  let fac := C o*(1+2*C a*(X+p*C a+1))+1
  pk+p*fac+out

lemma budget_degree (w H : ℕ) {p : Polynomial ℕ} {e : ℕ}
    (hp : p.natDegree≤e) :
    (LiteralProgram.budgetPolynomial w H p 0).natDegree≤2*e := by
  simpa only [LiteralProgram.budgetPolynomial,blockBudget] using blockBudget_degree w H hp

lemma compiler_degree {n : List Symbol→ℕ} {f : List Symbol×List Bool→List Symbol}
    (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) {p : Polynomial ℕ} {e : ℕ}
    (hp : p.natDegree≤e) (he : 1≤e) : (compilerPolynomial N F p).natDegree≤2*e := by
  let G := FiniteWordExecution.realizer N F
  simpa only [compilerPolynomial,physicalEnvelope,blockBudget,LiteralProgram.budgetPolynomial]
    using physicalEnvelope_degree LiteralPacked.width
      (MachineCost.programCost LiteralPacked.packCode)
      (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))
      (MachineCost.programCost LiteralPacked.unpackCode)
      (OnlineStack.accesses G.program.code) (OnlineStack.overhead G.program.code) hp he


open ContingencyTables.FiniteWordExecution

/-- The degree-controlled polynomial is the exact polynomial constructed by
    FiniteWordMachine, and bounds the same machineTime definition. -/
lemma compiler_bound {n : List Symbol→ℕ} {f : List Symbol×List Bool→List Symbol}
    (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) (p : Polynomial ℕ)
    (hp : ∀ as,(realizer N F).cost as+(experiment n f as).worst weight≤
      p.eval (wordMeasure n as)) :
    ∀ as,machineTime N F as≤(compilerPolynomial N F p).eval (wordMeasure n as) := by
  let G := realizer N F
  let a := OnlineStack.accesses G.program.code
  let o := OnlineStack.overhead G.program.code
  let pk : Polynomial ℕ := (1+LiteralProgram.budgetPolynomial 1 (18*LiteralPacked.width) X 0)*
    C (MachineCost.programCost LiteralPacked.packCode)
  let out : Polynomial ℕ := C (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))+
    (1+LiteralProgram.budgetPolynomial (18*LiteralPacked.width) 1 p 0)*
      C (MachineCost.programCost LiteralPacked.unpackCode)
  let fac : Polynomial ℕ := C o*(1+2*C a*(X+p*C a+1))+1
  change ∀ as, _ ≤ (pk+p*fac+out).eval (wordMeasure n as)
  intro as
  let M := wordMeasure n as
  have hw : weight as≤M := Nat.le_add_right _ _
  have hn : as.length≤M := (list_length_le_weight as).trans hw
  have hc : G.cost as≤p.eval M := (Nat.le_add_right _ _).trans (hp as)
  have hout : (experiment n f as).worst weight≤p.eval M :=
    (Nat.le_add_left _ _).trans (hp as)
  have hl : (experiment n f as).worst List.length≤p.eval M :=
    Experiment.worst_le _ _ _ ((Experiment.all_worst _ weight).mono
      (fun bs hbs => (list_length_le_weight bs).trans (hbs.trans hout)))
  have hf : OnlineStack.Executes.factor G.program.code (weight as) (G.cost as)≤fac.eval M := by
    have he : fac.eval M=OnlineStack.Executes.factor G.program.code M (p.eval M) := by
      simp only [fac,eval_add,eval_mul,eval_C,eval_ofNat,eval_X,eval_one,
        OnlineStack.Executes.factor,a,o]
    rw [he]
    exact OnlineStack.Executes.factor_mono _ _ _ _ hw hc
  have hpk : pk.eval M=LiteralProgram.packTime M := by
    simp only [pk,eval_mul,eval_add,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.packTime]
  have hpout : out.eval M=LiteralProgram.postTime (p.eval M) := by
    simp only [out,eval_add,eval_mul,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_zero,LiteralProgram.postTime]
  change LiteralProgram.wrapTime G as≤(pk+p*fac+out).eval M
  simp only [eval_add,eval_mul,hpk,hpout]
  unfold LiteralProgram.wrapTime OnlineTree.physicalCost
  exact Nat.add_le_add
    (Nat.add_le_add (LiteralProgram.packTime_mono hn) (Nat.mul_le_mul hc hf))
    (LiteralProgram.postTime_mono hl)


/-- No numeral is claimed for e or t: they are degree certificates for the
    actual complete word-count and complete supplied-word public draw. -/
theorem machineTime_degree {n : List Symbol→ℕ} {f : List Symbol×List Bool→List Symbol}
    {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f} {e t : ℕ}
    (hN : Typed N e) (hF : Typed F t) :
    ∃ q : Polynomial ℕ,q.natDegree≤2*completeOnlineDegree e t ∧
      ∀ as,machineTime N F as≤q.eval (wordMeasure n as) := by
  obtain ⟨p,hp,hpb⟩ := complete_online_degree hN hF
  refine ⟨compilerPolynomial N F p,compiler_degree N F hp ?_,compiler_bound N F p hpb⟩
  dsimp [completeOnlineDegree]
  have h1 : 1 ≤ max 1 t := le_max_left _ _
  have h2 : 1 ≤ max e 6 := by omega
  exact Nat.mul_le_mul h1 h2

end Math115.DegreeBounds
