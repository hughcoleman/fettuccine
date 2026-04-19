import Fettuccine.Algorithm.Certification
import Mathlib.Algebra.Field.Rat

-- We allow ourselves to use `native_decide`.
set_option linter.style.nativeDecide false

namespace Examples

open FMvPolynomial FMonomialOrder FMonomial

-- All of these examples will be over ℚ[x, y, z], with x > y > z.
abbrev S := FMvPolynomial 3 Rat

def m (x y z : ℕ) : FMonomial 3 :=
  { data := #[x, y, z], hsize := by simp }

section
-- ### Example: Monomial Orders
--
-- We can compare monomials under the three defined orders.

#eval lex (m 1 0 0) (m 0 1 0)  -- .gt  (x > y)
#eval lex (m 0 2 0) (m 0 1 1)  -- .gt  (y² > yz)

#eval grlex (m 0 1 0) (m 2 0 0)  -- .lt (y < x²: lower degree)
#eval grlex (m 1 1 0) (m 2 0 0)  -- .lt (xy < x²: same degree, lex)

#eval grevlex (m 1 0 0) (m 0 0 1)  -- .gt (x > z under grevlex)
#eval grevlex (m 2 0 0) (m 0 2 0)  -- .gt (x² > y² under grevlex)
end

section
-- ### Example 1: I = (xy - 1, x² - y)

def f₁ : S := #[(m 1 1 0, 1), (m 0 0 0, -1)] -- xy - 1
def f₂ : S := #[(m 2 0 0, 1), (m 0 1 0, -1)] -- x² - y

#eval (buchberger     lex #[f₁, f₂]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger   grlex #[f₁, f₂]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger grevlex #[f₁, f₂]).map (·.map fun (m, c) => (m.toList, c))

def w₁Lex := buchbergerWithCertificateWitnesses lex #[f₁, f₂]
def cert₁Lex : GroebnerBasisCertificate (n := 3) lex where
  gens := #[f₁, f₂]
  basis := w₁Lex.basis
  h_mem := IdealMembershipCertificate.ofWitnesses lex #[f₁, f₂] w₁Lex.basis w₁Lex.h_mem
    (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses lex w₁Lex.basis
    w₁Lex.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' lex cert₁Lex.gens cert₁Lex.basis :=
  cert₁Lex.isGroebnerBasis'

def w₁Grlex := buchbergerWithCertificateWitnesses grlex #[f₁, f₂]
def cert₁Grlex : GroebnerBasisCertificate (n := 3) grlex where
  gens := #[f₁, f₂]
  basis := w₁Grlex.basis
  h_mem := IdealMembershipCertificate.ofWitnesses grlex #[f₁, f₂] w₁Grlex.basis w₁Grlex.h_mem
    (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses grlex w₁Grlex.basis
    w₁Grlex.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' grlex cert₁Grlex.gens cert₁Grlex.basis :=
  cert₁Grlex.isGroebnerBasis'

def w₁Grevlex := buchbergerWithCertificateWitnesses grevlex #[f₁, f₂]
def cert₁Grevlex : GroebnerBasisCertificate (n := 3) grevlex where
  gens := #[f₁, f₂]
  basis := w₁Grevlex.basis
  h_mem := IdealMembershipCertificate.ofWitnesses grevlex #[f₁, f₂] w₁Grevlex.basis
    w₁Grevlex.h_mem (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses grevlex w₁Grevlex.basis
    w₁Grevlex.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' grevlex cert₁Grevlex.gens cert₁Grevlex.basis :=
  cert₁Grevlex.isGroebnerBasis'

def w₁LowFuel := buchbergerWithCertificateWitnesses lex #[f₁, f₂] 0
#eval checkSPolynomialsReduceCertificateWitnesses lex w₁LowFuel.basis w₁LowFuel.h_sPolynomials
end

section
-- ### Example 2: I = (xy - z, xz - y, yz - x)

def g₁ : S := #[(m 1 1 0, 1), (m 0 0 1, -1)] -- xy - z
def g₂ : S := #[(m 1 0 1, 1), (m 0 1 0, -1)] -- xz - y
def g₃ : S := #[(m 0 1 1, 1), (m 1 0 0, -1)] -- yz - x

#eval (buchberger     lex #[g₁, g₂, g₃]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger   grlex #[g₁, g₂, g₃]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger grevlex #[g₁, g₂, g₃]).map (·.map fun (m, c) => (m.toList, c))

def w₂Lex := buchbergerWithCertificateWitnesses lex #[g₁, g₂, g₃]
def cert₂Lex : GroebnerBasisCertificate (n := 3) lex where
  gens := #[g₁, g₂, g₃]
  basis := w₂Lex.basis
  h_mem := IdealMembershipCertificate.ofWitnesses lex #[g₁, g₂, g₃] w₂Lex.basis w₂Lex.h_mem
    (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses lex w₂Lex.basis
    w₂Lex.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' lex cert₂Lex.gens cert₂Lex.basis :=
  cert₂Lex.isGroebnerBasis'

def w₂Grlex := buchbergerWithCertificateWitnesses grlex #[g₁, g₂, g₃]
def cert₂Grlex : GroebnerBasisCertificate (n := 3) grlex where
  gens := #[g₁, g₂, g₃]
  basis := w₂Grlex.basis
  h_mem := IdealMembershipCertificate.ofWitnesses grlex #[g₁, g₂, g₃] w₂Grlex.basis
    w₂Grlex.h_mem (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses grlex w₂Grlex.basis
    w₂Grlex.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' grlex cert₂Grlex.gens cert₂Grlex.basis :=
  cert₂Grlex.isGroebnerBasis'

def w₂Grevlex := buchbergerWithCertificateWitnesses grevlex #[g₁, g₂, g₃]
def cert₂Grevlex : GroebnerBasisCertificate (n := 3) grevlex where
  gens := #[g₁, g₂, g₃]
  basis := w₂Grevlex.basis
  h_mem := IdealMembershipCertificate.ofWitnesses grevlex #[g₁, g₂, g₃] w₂Grevlex.basis
    w₂Grevlex.h_mem (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses grevlex w₂Grevlex.basis
    w₂Grevlex.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' grevlex cert₂Grevlex.gens cert₂Grevlex.basis :=
  cert₂Grevlex.isGroebnerBasis'
end

section
-- ### Certification edge cases

def duplicateUnsorted : S :=
  #[(m 0 0 0, 2), (m 1 1 0, 1), (m 0 0 0, -3)] -- xy - 1, unsorted
def zeroGen : S := #[]

def wDupZero := buchbergerWithCertificateWitnesses lex #[duplicateUnsorted, zeroGen, f₂]
def certDupZero : GroebnerBasisCertificate (n := 3) lex where
  gens := #[duplicateUnsorted, zeroGen, f₂]
  basis := wDupZero.basis
  h_mem := IdealMembershipCertificate.ofWitnesses lex #[duplicateUnsorted, zeroGen, f₂]
    wDupZero.basis wDupZero.h_mem (by native_decide)
  h_sPolynomials := SPolynomialsReduceCertificate.ofWitnesses lex wDupZero.basis
    wDupZero.h_sPolynomials (by native_decide)

example : IsGroebnerBasis' lex certDupZero.gens certDupZero.basis :=
  certDupZero.isGroebnerBasis'
end

end Examples
