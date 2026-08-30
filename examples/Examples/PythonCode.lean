import Mathlib

open Lean Meta Elab Tactic

namespace tacticbook

/--
An untrusted certificate produced by the external factorization program.
-/
structure FactorCertificate where
  n : Nat
  p : Nat
  q : Nat

/-- A valid certificate contains two non-trivial factors whose product is `n`. -/
def ValidFactorCertificate (certificate : FactorCertificate) : Prop :=
  1 < certificate.p ∧
    1 < certificate.q ∧
      certificate.n = certificate.p * certificate.q

/-- The executable certificate checker used inside Lean. -/
def checkFactorCertificate (certificate : FactorCertificate) : Bool :=
  decide (1 < certificate.p) && (
    decide (1 < certificate.q) &&
      decide (certificate.n = certificate.p * certificate.q))

/-- The checker is sound: acceptance implies the claimed factorization. -/
theorem checkFactorCertificate_sound (certificate : FactorCertificate)
    (accepted : checkFactorCertificate certificate = true) :
    certificate.n = certificate.p * certificate.q := by
  have valid : ValidFactorCertificate certificate := by
    simpa [ValidFactorCertificate, checkFactorCertificate] using accepted
  exact valid.2.2

/--
Ask an untrusted Python program to factor 10. Python returns only a certificate,
not a Lean proof; the Lean checker establishes the resulting equality.
-/
elab "python_factor" : tactic => withMainContext do
  let output ← IO.Process.output {
    cmd := "python3"
    args := #["-c", "import math\nn = 10\nfor p in range(2, math.isqrt(n) + 1):\n    if n % p == 0:\n        q = n // p\n        print(f'{{ n := {n}, p := {p}, q := {q} }}')\n        break\nelse:\n    raise SystemExit(f'no non-trivial factorization of {n}')"]
  }
  unless output.exitCode == 0 do
    throwError "Python failed with exit code {output.exitCode}:\n{output.stderr}"

  let certificateSource := output.stdout.trimAscii.toString
  let certificateSyntax : TSyntax `term ←
    match Parser.runParserCategory (← getEnv) `term certificateSource with
    | .ok stx => pure ⟨stx⟩
    | .error err => throwError "Python returned an invalid certificate: {err}"

  evalTactic (← `(tactic|
    exact checkFactorCertificate_sound $certificateSyntax (by native_decide)))

example : 10 = 2 * 5 := by
  python_factor

end tacticbook
