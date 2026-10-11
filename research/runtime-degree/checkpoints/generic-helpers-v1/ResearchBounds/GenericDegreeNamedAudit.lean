/- Named-axiom audit for the four exact compiled generic helpers.
   This driver declares no new proof and does not integrate sampler seed degrees. -/
import ResearchBounds.TreeDegreeBounds
import ResearchBounds.PolynomialCompilerDegree
import ResearchBounds.FreshBitDegreeBounds
import ResearchBounds.FiniteWordDegreeBounds

-- ResearchBounds.TreeDegreeBounds; source fd9a62620e3b640045845e973ae8d39a8101139e8330768c240962a8ff2a7adf
#print axioms Math115.DegreeBounds.degree_add
#print axioms Math115.DegreeBounds.degree_mul
#print axioms Math115.DegreeBounds.degree_comp
#print axioms Math115.DegreeBounds.degree_scale
#print axioms Math115.DegreeBounds.degree_affine
#print axioms Math115.DegreeBounds.Bounded
#print axioms Math115.DegreeBounds.Typed
#print axioms Math115.DegreeBounds.typed_identity
#print axioms Math115.DegreeBounds.typed_first
#print axioms Math115.DegreeBounds.typed_second
#print axioms Math115.DegreeBounds.typed_constantData
#print axioms Math115.DegreeBounds.typed_constant
#print axioms Math115.DegreeBounds.typed_composition
#print axioms Math115.DegreeBounds.typed_pair
#print axioms Math115.DegreeBounds.typed_congr
#print axioms Math115.DegreeBounds.bounded_congr
#print axioms Math115.DegreeBounds.bounded_remeasure
#print axioms Math115.DegreeBounds.typed_fold

-- ResearchBounds.PolynomialCompilerDegree; source dc85a5de270470e4be4fc66dedd8ebd128b3c940a4f20c9d17f600a1875dbd97
#print axioms Math115.DegreeBounds.blockBudget
#print axioms Math115.DegreeBounds.physicalEnvelope
#print axioms Math115.DegreeBounds.blockBudget_degree
#print axioms Math115.DegreeBounds.physicalEnvelope_degree
#print axioms Math115.DegreeBounds.physicalEnvelope_degree_max

-- ResearchBounds.FreshBitDegreeBounds; source fa55d0458fab0ea1a2ffe49c856c035bffec07b119c59b978f2e51e91ff56674
#print axioms Math115.DegreeBounds.OnlineBounded
#print axioms Math115.DegreeBounds.online_deterministic
#print axioms Math115.DegreeBounds.online_congr
#print axioms Math115.DegreeBounds.online_composition
#print axioms Math115.DegreeBounds.online_then
#print axioms Math115.DegreeBounds.online_pair
#print axioms Math115.DegreeBounds.online_choose
#print axioms Math115.DegreeBounds.typed_listCons
#print axioms Math115.DegreeBounds.typed_subtract
#print axioms Math115.DegreeBounds.typed_predecessor
#print axioms Math115.DegreeBounds.typed_rangeStep
#print axioms Math115.DegreeBounds.range_numeric_degree
#print axioms Math115.DegreeBounds.fresh_step_degree
#print axioms Math115.DegreeBounds.fresh_list_degree
#print axioms Math115.DegreeBounds.fresh_natural_degree

-- ResearchBounds.FiniteWordDegreeBounds; source 9ee4f34b9a3219aeb4294eb84027145cc16a831ff6e5f86dd7afaac736d04b16
#print axioms Math115.DegreeBounds.online_weaken
#print axioms Math115.DegreeBounds.source_degree
#print axioms Math115.DegreeBounds.completeOnlineDegree
#print axioms Math115.DegreeBounds.complete_online_degree
#print axioms Math115.DegreeBounds.compilerPolynomial
#print axioms Math115.DegreeBounds.budget_degree
#print axioms Math115.DegreeBounds.compiler_degree
#print axioms Math115.DegreeBounds.compiler_bound
#print axioms Math115.DegreeBounds.machineTime_degree
