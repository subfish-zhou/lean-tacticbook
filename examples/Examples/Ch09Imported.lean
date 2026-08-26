import SubVerso.Examples

namespace tacticbook_exact_imported

inductive SearchToken : Prop where
  | intro

theorem importedToken : SearchToken := .intro

theorem imported_chain {P Q R : Prop} (hPQ : P → Q) (hQR : Q → R) (hP : P) : R :=
  hQR (hPQ hP)

theorem imported_partial {P Q : Prop} (hP : P) : Q → P ∧ Q :=
  fun hQ => ⟨hP, hQ⟩

end tacticbook_exact_imported
