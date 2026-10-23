# What the resolvent refinement cannot remove

11 October 2026. Explicit rational constructions complement the positive theorem in [the resolvent refinement](resolvent-rejection.md). They concern generic Markov/terminal premises, not lower bounds for every contingency-table sampler.

## 1. Rare acceptance does not make first-accept bias vanish

Let `0<z<1/2`, `pi=(1-2z,z,z)`, and distinguish state 1. In L2(pi), let E be the rank-one orthogonal projection onto the centered contrast separating state 1 from the other two states. Its entries are rational:

`E_ij=pi_j v_i v_j`, where

`v_1^2=(1-z)/z`, `v_i v_1=-1` for i!=1, and `v_i v_j=z/(1-z)` for i,j!=1.

Then

`P=1/2 I+1/2 Pi+1/4 E`

is a genuine reversible half-lazy Markov kernel. Its off-diagonal entries are nonnegative: crossing to or from state 1 gives `pi_j/4`; other off-diagonals are positive. Its diagonal is at least one half. Its centered eigenvalues are `3/4` on E and `1/2` on the remaining centered direction.

For t steps,

`Q=P^t=Pi+u(I-Pi)+(rho-u)E`, `rho=(3/4)^t`, `u=(1/2)^t`.

Let acceptance be `(0,1,1)`, returning the accepted state's label. Stationary success is `s=2z`, and the exact target is uniform on states 1 and 2. Every rejection leaves the state at 0. The infinite first-accepted output therefore has exact TV bias

`(1-2z)(rho-u) / {2[(2-rho-u)-2z(1-rho)]}`.

This follows directly from the exit probabilities `Q_01=(1-rho)z` and `Q_02=(1-u)z+(rho-u)z^2/(1-z)`, plus the stationary initial acceptance mass z at each target state.

As z tends to zero and then t grows, `TV/rho` tends to `1/4`. Thus a general output-bias bound cannot be `o(rho)`, nor can it gain a factor s merely because success is rare. This validates the accuracy dependence of the new spacing rule: `rho=O(epsilon)` is generally needed.

The exact reproducer checks z equal to `1/100`, `1/1000`, and `1/1000000`, at t=8. It verifies the true P matrix, analytic eigenspaces by exact projection identities, exact matrix powers, the resolvent, and the closed bias formula. No numerical eigenvalues are used.

## 2. Generic cold-start mass dependence is real

On states `0,...,L`, take a reflected nearest-neighbor chain with right probability `1/3`, left probability `1/6`, and holding probability `1/2`; missing boundary moves hold. It is reversible and half-lazy, with

`pi_i=2^i/(2^(L+1)-1)`.

Its relaxation time has a constant upper bound independent of L. To see this without guessing eigenvalues, any set of mass at most one half excludes state L, since `pi_L>1/2`. Split it into disjoint intervals. For an interval ending at b<L, its mass is less than `2pi_b`, while its right-edge flow is `pi_b/3`. Summing over intervals gives conductance at least `1/6`; consequently the symmetric flow parameter `tau_c=sup_S pi(S)pi(S^c)/flow(S,S^c)` is at most six. Aldous–Fill's discrete-time [Cheeger bound](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch4.S5.html), `tau_2<=8tau_c^2`, yields the uniform allowance `tau_2<=288`.

Yet from state 0, before L steps the chain cannot reach L. Its TV distance from pi is therefore greater than one half. Also

`log(1/pi_min)=log(2^(L+1)-1)=Theta(L)`.

Thus a constant gap does not give a point-start mixing bound independent of log(1/pi_min). With acceptance identically one and output equal to the current state, the stationary terminal identity is exact; the same obstruction applies to its output. This is a genuine output obstruction, not merely failure-probability accounting.

The exact report checks stationarity, detailed balance, all flow cuts, and the point-start support bound for L=2,4,8. The general interval proof covers every L.

## 3. The cold obstruction also has a uniform-stationary version

Replace path state i by a layer of `2^i` distinct vertices. Let R move with probability one half to a uniform vertex in its current layer, with probability `1/3` to a uniform vertex in the next layer, and with probability `1/6` to a uniform vertex in the preceding layer; missing boundary layer moves hold at the current vertex. Each cross-layer per-edge rate is symmetric, since

`1/(3*2^(i+1))=1/(6*2^i)`.

Set `P=(I+R)/2`. It is half-lazy and has uniform stationary law on `N=2^(L+1)-1` vertices. The projected layer chain is the preceding biased path slowed by a factor two, so its relaxation allowance is at most 576. The within-layer heat bath has coefficient one quarter. Decomposing variance into within-layer and between-layer parts, and applying Jensen to the vertical energy, gives full relaxation allowance at most `max(4,576)=576`.

From the single bottom vertex, no transition raises the layer index by more than one. Before L steps, more than half the uniform target mass in the top layer is unreachable. Thus mixing requires `Omega(L)=Omega(log N)=Omega(log(1/pi_min))` even with uniform pi and constant gap.

This does not rule out a problem-specific warm-start construction. It rules out deleting the cold factor from a theorem based only on point start, gap and stationary measure.

## 4. A genuine warm start in a solvable table family

If every column margin is one, row margins are positive and sum to n, ordinary tables are assignments of the n labeled columns to rows with fixed row counts. Shuffle the columns uniformly, then assign consecutive chunks of sizes r_i to rows. Every table has exactly `prod_i r_i!` permutation preimages, so the table law is uniform.

Every table has support exactly n, and `m<=n`. Its defect repair fiber has the same size `(p-1)n`. Choosing a uniform positive receiver and a uniform crossing label therefore gives an **exact stationary defect draw**. The support terminal accepts with probability one. The transpose covers all row margins equal to one.

This is a standard direct shuffle construction; it also solves that fiber directly and is not a universal warm-start method. Bounded fair-word integer draws yield an approximate version with a transparent summed draw-error budget. Initializing all p table cells and performing n shuffle updates costs `O(p)` integer operations. There is no need to run the enormous generic gap schedule for these instances.

No generic ordinary-margin warm start was established by this pass. A proposal obtained by assigning labeled individuals to cells would have a different aggregate-table law and cannot be called warm for the uniform-table target without a density-ratio proof.
