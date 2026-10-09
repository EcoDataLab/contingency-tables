/-
SPDX-License-Identifier: Apache-2.0
A single list program for dilated dense sampling, prefix decoding, and retry.
All dimensions enumerated by the program come from encoded lists. Its cost
theorem includes the supplied Boolean word in the input weight; accuracy and
the required word length are identified separately in the semantics module.
-/
import Math115.LatticeCompletionProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseReservedWord
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram

namespace Math115.CompletionSamplerProgram

open OAI OAI.ContingencyTables OAI.ContingencyTables.DensePrograms
open OAI.ContingencyTables.ProfilePrograms
open OAI.MatchingFPRAS.TreeTyped

set_option maxHeartbeats 1200000

/-- Coarse row and column lists, dimension allowance, and requested precision. -/
abbrev Parameters := CanonicalParameters
abbrev InnerParameters := ℕ × CanonicalParameters

def retriesRealizer : Realizer CompletionRetryBudget.retries :=
  composition (f := fun h : ℕ => (4, h + 2))
    (g := fun x : ℕ × ℕ => x.1 * x.2)
    (pair (constant 4)
      (composition (f := fun h : ℕ => (h, 2))
        (g := fun x : ℕ × ℕ => x.1 + x.2) (pair identity (constant 2)) add)) multiply

theorem polynomial_retries : PolynomialTime retriesRealizer := by
  unfold retriesRealizer
  exact polynomial_composition (f := fun h : ℕ => (4, h + 2))
    (g := fun x : ℕ × ℕ => x.1 * x.2)
    (polynomial_pair (polynomial_constant 4)
      (polynomial_composition (f := fun h : ℕ => (h, 2))
        (g := fun x : ℕ × ℕ => x.1 + x.2)
        (polynomial_pair polynomial_identity (polynomial_constant 2)) polynomial_add))
    polynomial_multiply

def precisionRealizer : Realizer CompletionRetryBudget.finePrecision :=
  composition (f := fun h : ℕ => (h + 2, Nat.clog 2 (CompletionRetryBudget.retries h)))
    (g := fun x : ℕ × ℕ => x.1 + x.2)
    (pair (composition (f := fun h : ℕ => (h, 2))
        (g := fun x : ℕ × ℕ => x.1 + x.2) (pair identity (constant 2)) add)
      (composition (f := CompletionRetryBudget.retries) (g := Nat.clog 2)
        retriesRealizer ceilLogTwoRealizer)) add

theorem polynomial_precision : PolynomialTime precisionRealizer := by
  unfold precisionRealizer
  exact polynomial_composition
    (f := fun h : ℕ => (h + 2, Nat.clog 2 (CompletionRetryBudget.retries h)))
    (g := fun x : ℕ × ℕ => x.1 + x.2)
    (polynomial_pair
      (polynomial_composition (f := fun h : ℕ => (h, 2))
        (g := fun x : ℕ × ℕ => x.1 + x.2)
        (polynomial_pair polynomial_identity (polynomial_constant 2)) polynomial_add)
      (polynomial_composition (f := CompletionRetryBudget.retries) (g := Nat.clog 2)
        polynomial_retries polynomial_ceilLogTwo)) polynomial_add

def powerTwelveRealizer : Realizer (fun d : ℕ => d^12) :=
  (composition (f := fun d : ℕ => d^4) (g := fun d : ℕ => (d*d)*d)
    fourthPower
    (composition (f := fun d : ℕ => (d*d, d))
      (g := fun x : ℕ × ℕ => x.1 * x.2) (pair squareNat identity) multiply)).congr
    (by intro d; simp only [Function.comp_apply]; ring)

theorem polynomial_powerTwelve : PolynomialTime powerTwelveRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_fourthPower
    (polynomial_composition (polynomial_pair polynomial_squareNat polynomial_identity)
      polynomial_multiply))

def dilateEntry (x : (ℕ × ℕ) × ℕ) : ℕ := x.1.1 * (x.2 + 2 * x.1.2)

def dilateEntryRealizer : Realizer dilateEntry :=
  composition (f := fun x : (ℕ × ℕ) × ℕ => (x.1.1, x.2 + 2 * x.1.2))
    (g := fun x : ℕ × ℕ => x.1 * x.2)
    (pair first.fst
      (composition (f := fun x : (ℕ × ℕ) × ℕ => (x.2, 2 * x.1.2))
        (g := fun x : ℕ × ℕ => x.1 + x.2)
        (pair second
          (composition (f := fun x : (ℕ × ℕ) × ℕ => (2, x.1.2))
            (g := fun x : ℕ × ℕ => x.1 * x.2)
            (pair (constant 2) first.snd) multiply)) add)) multiply

theorem polynomial_dilateEntry : PolynomialTime dilateEntryRealizer := by
  unfold dilateEntryRealizer Realizer.fst Realizer.snd
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition (polynomial_pair (polynomial_constant 2)
        (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply))
      polynomial_add)) polynomial_multiply

def dilateList (x : (ℕ × ℕ) × List ℕ) : List ℕ :=
  x.2.map (fun v => dilateEntry (x.1, v))

def dilateListRealizer : Realizer dilateList := mapWith dilateEntryRealizer

theorem polynomial_dilateList : PolynomialTime dilateListRealizer :=
  polynomial_mapWith polynomial_dilateEntry

def prepare (p : Parameters) : InnerParameters :=
  (p.2.1^12,
    ((dilateList ((p.2.1^12, p.1.2.length), p.1.1),
      dilateList ((p.2.1^12, p.1.1.length), p.1.2)),
      (p.2.1, CompletionRetryBudget.finePrecision p.2.2)))

def prepareRealizer : Realizer prepare := by
  let k : Realizer (fun p : Parameters => p.2.1^12) :=
    composition (f := fun p : Parameters => p.2.1) (g := fun d : ℕ => d^12)
      second.fst powerTwelveRealizer
  let rows : Realizer (fun p : Parameters =>
      dilateList ((p.2.1^12, p.1.2.length), p.1.1)) :=
    composition (f := fun p : Parameters => ((p.2.1^12, p.1.2.length), p.1.1))
      (g := dilateList)
      (pair (pair k (composition (f := fun p : Parameters => p.1.2)
        (g := List.length) first.snd listLength)) first.fst) dilateListRealizer
  let cols : Realizer (fun p : Parameters =>
      dilateList ((p.2.1^12, p.1.1.length), p.1.2)) :=
    composition (f := fun p : Parameters => ((p.2.1^12, p.1.1.length), p.1.2))
      (g := dilateList)
      (pair (pair k (composition (f := fun p : Parameters => p.1.1)
        (g := List.length) first.fst listLength)) first.snd) dilateListRealizer
  exact pair k (pair (pair rows cols)
    (pair second.fst
      (composition (f := fun p : Parameters => p.2.2)
        (g := CompletionRetryBudget.finePrecision) second.snd precisionRealizer)))

theorem polynomial_prepare : PolynomialTime prepareRealizer := by
  unfold prepareRealizer Realizer.fst Realizer.snd
  exact polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_powerTwelve)
    (polynomial_pair
      (polynomial_pair
        (polynomial_composition (polynomial_pair
          (polynomial_pair
            (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
              polynomial_powerTwelve)
            (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
              polynomial_listLength))
          (polynomial_composition polynomial_first polynomial_first)) polynomial_dilateList)
        (polynomial_composition (polynomial_pair
          (polynomial_pair
            (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
              polynomial_powerTwelve)
            (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
              polynomial_listLength))
          (polynomial_composition polynomial_first polynomial_second)) polynomial_dilateList))
      (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_precision)))

/-- One dense call, including its canonical internal fallback, followed by
the signed prefix-floor rejection test. -/
def trial (x : InnerParameters × List Bool) : Option MatrixCode :=
  LatticeCompletionProgram.decode (x.1.1, canonicalDenseDraw (x.1.2, x.2))

def trialRealizer : Realizer trial :=
  composition (f := fun x : InnerParameters × List Bool =>
      (x.1.1, canonicalDenseDraw (x.1.2, x.2)))
    (g := LatticeCompletionProgram.decode)
    (pair first.fst
      (composition (f := fun x : InnerParameters × List Bool => (x.1.2, x.2))
        (g := canonicalDenseDraw) (pair first.snd second) canonicalDenseDrawRealizer))
    LatticeCompletionProgram.decodeRealizer

theorem polynomial_trial : PolynomialTime trialRealizer := by
  unfold trialRealizer Realizer.fst Realizer.snd
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_canonicalDenseDraw)) LatticeCompletionProgram.polynomial_decode

def wordWidth (p : Parameters) : ℕ := canonicalBitCount (prepare p).2

def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun p : Parameters => (prepare p).2) (g := canonicalBitCount)
    (composition (f := prepare) (g := fun x : InnerParameters => x.2)
      prepareRealizer second) canonicalBitCountRealizer

theorem polynomial_wordWidth : PolynomialTime wordWidthRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepare polynomial_second)
    polynomial_canonicalBitCount

def bitCount (p : Parameters) : ℕ := CompletionRetryBudget.retries p.2.2 * wordWidth p

def bitCountRealizer : Realizer bitCount :=
  composition (f := fun p : Parameters =>
      (CompletionRetryBudget.retries p.2.2, wordWidth p))
    (g := fun x : ℕ × ℕ => x.1 * x.2)
    (pair (composition (f := fun p : Parameters => p.2.2)
      (g := CompletionRetryBudget.retries) second.snd retriesRealizer) wordWidthRealizer)
    multiply

theorem polynomial_bitCount : PolynomialTime bitCountRealizer := by
  unfold bitCountRealizer Realizer.snd
  exact polynomial_composition
    (f := fun p : Parameters => (CompletionRetryBudget.retries p.2.2, wordWidth p))
    (g := fun x : ℕ × ℕ => x.1 * x.2)
    (polynomial_pair
      (polynomial_composition (f := fun p : Parameters => p.2.2)
        (g := CompletionRetryBudget.retries)
        (polynomial_composition polynomial_second polynomial_second) polynomial_retries)
      polynomial_wordWidth) polynomial_multiply

/-- Rectangular complete words from the reserved prefix. On short malformed
inputs there are fewer trials; surplus bits never add trials. -/
def reservedWords (x : Parameters × List Bool) : List (List Bool) :=
  wordChunks (wordWidth x.1, x.2.take (bitCount x.1))

def reservedWordsRealizer : Realizer reservedWords :=
  composition (f := fun x : Parameters × List Bool =>
      (wordWidth x.1, x.2.take (bitCount x.1))) (g := wordChunks)
    (pair (composition (f := fun x : Parameters × List Bool => x.1) (g := wordWidth)
        first wordWidthRealizer)
      (composition (f := fun x : Parameters × List Bool => (x.2, bitCount x.1))
        (g := fun x : List Bool × ℕ => x.1.take x.2)
        (pair second
          (composition (f := fun x : Parameters × List Bool => x.1) (g := bitCount)
            first bitCountRealizer)) takeFast))
    wordChunksRealizer

theorem polynomial_reservedWords : PolynomialTime reservedWordsRealizer := by
  unfold reservedWordsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_wordWidth)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_bitCount)) polynomial_takeFast))
    polynomial_wordChunks

/-- The original coarse-table fallback is computed by the unchanged binary
greedy constructor. No table witness or precomputed fine margins are inputs. -/
def draw (x : Parameters × List Bool) : MatrixCode :=
  FirstSuccessProgram.retry trial
    ((prepare x.1, GreedyFeasibleTable.listMatrix x.1.1.1 x.1.1.2), reservedWords x)

def drawRealizer : Realizer draw :=
  composition (f := fun x : Parameters × List Bool =>
      ((prepare x.1, GreedyFeasibleTable.listMatrix x.1.1.1 x.1.1.2), reservedWords x))
    (g := FirstSuccessProgram.retry trial)
    (pair
      (pair (composition (f := fun x : Parameters × List Bool => x.1) (g := prepare)
          first prepareRealizer)
        (composition (f := fun x : Parameters × List Bool => x.1.1)
          (g := fun x : List ℕ × List ℕ => GreedyFeasibleTable.listMatrix x.1 x.2)
          first.fst GreedyFeasibleTable.tableRealizer)) reservedWordsRealizer)
    (FirstSuccessProgram.retryRealizer trialRealizer)

/-- Polynomial charged tree-machine cost in the encoded margins, parameters,
and supplied random word. This does not assign a full outer-sampler exponent. -/
theorem polynomial_draw : PolynomialTime drawRealizer := by
  unfold drawRealizer Realizer.fst
  exact polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_prepare)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        GreedyFeasibleTable.polynomial_table)) polynomial_reservedWords)
    (FirstSuccessProgram.polynomial_retry polynomial_trial)

end Math115.CompletionSamplerProgram
