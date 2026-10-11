/-
SPDX-License-Identifier: Apache-2.0
Encoded outer reference trials with separate walk and terminal precisions.
Retries consume a fixed reserved prefix and restart from the same supplied
configuration. Pointwise physical-table semantics are a separate bridge.
-/
import Math115.LatticeProfileWalk
import Math115.CompletionSamplerProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileWordProgram
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

namespace Math115.LatticeOuterProgram

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms

/-- Replace only the requested completion precision, retaining dimensions,
padding, original margins, catalogue and both current state views. -/
def withPrecision (z : ResidualParameters × ℕ) : ResidualParameters :=
  (z.1.1, (z.1.2.1, z.2))

def withPrecisionRealizer : Realizer withPrecision :=
  pair (composition first first) (pair (composition (composition first second) first) second)

theorem polynomial_withPrecision : PolynomialTime withPrecisionRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second)

abbrev TrialData := ((ProfileConfiguration × List ProfileWord) × ℕ) × List Bool

def trialState (z : TrialData) : ProfileConfiguration := LatticeProfileWalk.profileWalk z.1.1

def trialStateRealizer : Realizer trialState :=
  composition (composition first first) LatticeProfileWalk.profileWalkRealizer

theorem polynomial_trialState : PolynomialTime trialStateRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    LatticeProfileWalk.polynomial_profileWalk

def trialParameters (z : TrialData) : ResidualParameters :=
  withPrecision (currentParameters (trialState z), z.1.2)

def trialParametersRealizer : Realizer trialParameters :=
  composition (pair (composition trialStateRealizer currentParametersRealizer)
    (composition first second)) withPrecisionRealizer

theorem polynomial_trialParameters : PolynomialTime trialParametersRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_trialState polynomial_currentParameters)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_withPrecision

def trialCompletion (z : TrialData) : MatrixCode :=
  CompletionSamplerProgram.draw (residualParameters (trialParameters z), z.2)

def trialCompletionRealizer : Realizer trialCompletion :=
  composition (pair (composition trialParametersRealizer residualParametersRealizer) second)
    CompletionSamplerProgram.drawRealizer

theorem polynomial_trialCompletion : PolynomialTime trialCompletionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_trialParameters polynomial_residualParameters)
    polynomial_second) CompletionSamplerProgram.polynomial_draw

def trialOutputInput (z : TrialData) : OuterTrialInput :=
  ((trialParameters z).1, trialCompletion z)

def trialOutputInputRealizer : Realizer trialOutputInput :=
  pair (composition trialParametersRealizer first) trialCompletionRealizer

theorem polynomial_trialOutputInput : PolynomialTime trialOutputInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_trialParameters polynomial_first)
    polynomial_trialCompletion

def profileTrial (z : TrialData) : Option MatrixCode := outerTrial (trialOutputInput z)

def profileTrialRealizer : Realizer profileTrial :=
  composition trialOutputInputRealizer outerTrialRealizer

theorem polynomial_profileTrial : PolynomialTime profileTrialRealizer :=
  polynomial_composition polynomial_trialOutputInput polynomial_outerTrial

/-- The original word schedule carries `(steps, proposal width, step-completion
width)`. The final pair adds `(terminal precision, terminal-completion width)`.
These are separate fields, so terminal accuracy need not match step accuracy. -/
abbrev TrialParameters := (ProfileConfiguration × ProfileWordSchedule) × (ℕ × ℕ)
abbrev PackedTrial := TrialParameters × List Bool

def trialWordInput (z : PackedTrial) : ProfileWordInput := (z.1.1.2, z.2)

def trialWordInputRealizer : Realizer trialWordInput :=
  pair (composition (composition first first) second) second

theorem polynomial_trialWordInput : PolynomialTime trialWordInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second

def terminalWord (z : PackedTrial) : List Bool :=
  (profileTerminalWord (trialWordInput z)).take z.1.2.2

def terminalWordRealizer : Realizer terminalWord :=
  composition (pair (composition trialWordInputRealizer profileTerminalWordRealizer)
    (composition (composition first second) second)) takeFast

theorem polynomial_terminalWord : PolynomialTime terminalWordRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_trialWordInput polynomial_profileTerminalWord)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second)) polynomial_takeFast

def prepareTrial (z : PackedTrial) : TrialData :=
  (((z.1.1.1, profileWalkWords (trialWordInput z)), z.1.2.1), terminalWord z)

def prepareTrialRealizer : Realizer prepareTrial :=
  pair (pair (pair (composition (composition first first) first)
    (composition trialWordInputRealizer profileWalkWordsRealizer))
    (composition (composition first second) first)) terminalWordRealizer

theorem polynomial_prepareTrial : PolynomialTime prepareTrialRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition polynomial_trialWordInput polynomial_profileWalkWords))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
    polynomial_terminalWord

def packedTrial (z : PackedTrial) : Option MatrixCode := profileTrial (prepareTrial z)

def packedTrialRealizer : Realizer packedTrial := composition prepareTrialRealizer profileTrialRealizer

theorem polynomial_packedTrial : PolynomialTime packedTrialRealizer :=
  polynomial_composition polynomial_prepareTrial polynomial_profileTrial

/-- Width depends only on the schedule, not the supplied word length. -/
def attemptWidth (z : TrialParameters) : ℕ :=
  z.1.2.1.1 * (z.1.2.1.2 + z.1.2.2) + z.2.2

def attemptWidthRealizer : Realizer attemptWidth :=
  composition (pair (composition (pair (composition first second) (constant ([] : List Bool)))
    profileWalkWidthRealizer) (composition second second)) add

theorem polynomial_attemptWidth : PolynomialTime attemptWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_constant ([] : List Bool))) polynomial_profileWalkWidth)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_add

abbrev RetryParameters := (TrialParameters × MatrixCode) × ℕ
abbrev RetryData := RetryParameters × List Bool

def retryAttemptWidth (z : RetryData) : ℕ := attemptWidth z.1.1.1

def retryAttemptWidthRealizer : Realizer retryAttemptWidth :=
  composition (composition (composition first first) first) attemptWidthRealizer

theorem polynomial_retryAttemptWidth : PolynomialTime retryAttemptWidthRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_attemptWidth

def retryBankWidth (z : RetryData) : ℕ := z.1.2 * retryAttemptWidth z

def retryBankWidthRealizer : Realizer retryBankWidth :=
  composition (pair (composition first second) retryAttemptWidthRealizer) multiply

theorem polynomial_retryBankWidth : PolynomialTime retryBankWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_retryAttemptWidth)
    polynomial_multiply

/-- Extra supplied bits do not create extra attempts. A short malformed word
produces only its complete chunks, keeping the total program polynomial. -/
def retryWords (z : RetryData) : List (List Bool) :=
  wordChunks (retryAttemptWidth z, z.2.take (retryBankWidth z))

def retryWordsRealizer : Realizer retryWords :=
  composition (pair retryAttemptWidthRealizer
    (composition (pair second retryBankWidthRealizer) takeFast)) wordChunksRealizer

theorem polynomial_retryWords : PolynomialTime retryWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_retryAttemptWidth
    (polynomial_composition (polynomial_pair polynomial_second polynomial_retryBankWidth)
      polynomial_takeFast)) polynomial_wordChunks

/-- Every callback receives exactly the same initial trial parameters. -/
def retry (z : RetryData) : MatrixCode :=
  FirstSuccessProgram.retry packedTrial (z.1.1, retryWords z)

def retryRealizer : Realizer retry :=
  composition (pair (composition first first) retryWordsRealizer)
    (FirstSuccessProgram.retryRealizer packedTrialRealizer)

theorem polynomial_retry : PolynomialTime retryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_retryWords)
    (FirstSuccessProgram.polynomial_retry polynomial_packedTrial)

open FirstSuccess FairBits GridBoundary
open scoped Classical
noncomputable section

/-- The reused step-word parser works for an independent terminal width. -/
lemma walkWords_ofFn {T s f g : ℕ} (hw : 0 < s + f)
    (bits : Fin (T * (s + f) + g) → Bool) :
    profileWalkWords (((T, s), f), List.ofFn bits) = List.ofFn (fun i : Fin T =>
      let word := gridWordEquiv T (s + f) (splitWordEquiv (T * (s + f)) g bits).1 i
      (List.ofFn (splitWordEquiv s f word).1, List.ofFn (splitWordEquiv s f word).2)) := by
  unfold profileWalkWords profileWalkChunks
  dsimp only [profileWordWidth, profileWalkWidth]
  rw [ofFn_split_take, wordChunks_ofFn hw, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact splitProfileWord_ofFn _

lemma terminalWord_ofFn (configuration : ProfileConfiguration) (T s f g hTerminal : ℕ)
    (bits : Fin (T * (s + f) + g) → Bool) :
    terminalWord (((configuration, ((T, s), f)), (hTerminal, g)), List.ofFn bits) =
      List.ofFn (splitWordEquiv (T * (s + f)) g bits).2 := by
  unfold terminalWord profileTerminalWord
  dsimp only [trialWordInput, profileWalkWidth, profileWordWidth]
  rw [ofFn_split_drop]
  exact List.take_of_length_le (by simp)

lemma retryWords_ofFn (parameters : TrialParameters) (fallback : MatrixCode) (R : ℕ)
    (hw : 0 < attemptWidth parameters) (bits : Fin (R * attemptWidth parameters) → Bool) :
    retryWords (((parameters, fallback), R), List.ofFn bits) =
      List.ofFn (fun i : Fin R => List.ofFn (gridWordEquiv R (attemptWidth parameters) bits i)) := by
  unfold retryWords
  dsimp only [retryAttemptWidth, retryBankWidth]
  rw [show List.take (R * attemptWidth parameters) (List.ofFn bits) = List.ofFn bits by
    exact List.take_of_length_le (by simp)]
  exact wordChunks_ofFn hw bits

lemma retryWords_suffix (parameters : TrialParameters) (fallback : MatrixCode) (R : ℕ)
    (bits suffix : List Bool) (hbits : bits.length = R * attemptWidth parameters) :
    retryWords (((parameters, fallback), R), bits ++ suffix) =
      retryWords (((parameters, fallback), R), bits) := by
  unfold retryWords
  dsimp only [retryAttemptWidth, retryBankWidth]
  rw [← hbits, List.take_left, List.take_length]

/-- Exact first-success semantics before the separate physical-table bridge. -/
theorem retry_ofFn (parameters : TrialParameters) (fallback : MatrixCode) (R : ℕ)
    (hw : 0 < attemptWidth parameters) (bits : Fin (R * attemptWidth parameters) → Bool) :
    retry (((parameters, fallback), R), List.ofFn bits) =
      wordRetry (fun word => packedTrial (parameters, List.ofFn word)) fallback R
        (gridWordEquiv R (attemptWidth parameters) bits) := by
  unfold retry
  rw [retryWords_ofFn parameters fallback R hw bits]
  exact FirstSuccessProgram.retry_ofFn _ _ _ _

end
end Math115.LatticeOuterProgram
