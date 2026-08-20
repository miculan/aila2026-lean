/-
  AILA 2026 — SOLUZIONI del Foglio 1 (logica proposizionale, Curry–Howard).

  Dove è istruttivo, la soluzione è data sia come termine (il λ-termine di
  L1) sia in tactic mode: sono lo stesso oggetto visto da due lati.
-/

import Mathlib.Tactic

namespace Soluzioni.Foglio1

variable (A B C : Prop)

/-! ## Parte I — Implicazione: i combinatori -/

/-- 1.1 — Combinatore K: `λx.λy.x`. -/
theorem comb_K : A → B → A := by
  intro a _
  exact a

theorem comb_K' : A → B → A :=
  fun a _ => a

/-- 1.2 — Combinatore S: `λx.λy.λz. (x z) (y z)`. -/
theorem comb_S : (A → B → C) → (A → B) → A → C := by
  intro f g a
  exact f a (g a)

theorem comb_S' : (A → B → C) → (A → B) → A → C :=
  fun f g a => f a (g a)

/-- 1.3 — Composizione, in term mode: è la composizione di funzioni. -/
theorem comp : (A → B) → (B → C) → (A → C) :=
  fun f g a => g (f a)

/-! ## Parte II — Congiunzione e disgiunzione -/

/-- 1.4 — Currying: l'isomorfismo `A × B → C  ≃  A → B → C`. -/
theorem curry : (A ∧ B → C) ↔ (A → B → C) := by
  constructor
  · intro h a b
    exact h ⟨a, b⟩
  · intro h hab
    exact h hab.1 hab.2

/-- 1.5 — Distributività di ∧ su ∨. -/
theorem distrib : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
  constructor
  · rintro ⟨a, hb | hc⟩
    · left;  exact ⟨a, hb⟩
    · right; exact ⟨a, hc⟩
  · rintro (⟨a, hb⟩ | ⟨a, hc⟩)
    · exact ⟨a, Or.inl hb⟩
    · exact ⟨a, Or.inr hc⟩

/-- 1.6 — Eliminazione della disgiunzione: l'eliminatore del tipo somma. -/
theorem or_elim : (A → C) → (B → C) → (A ∨ B → C) := by
  intro f g h
  rcases h with a | b
  · exact f a
  · exact g b

theorem or_elim' : (A → C) → (B → C) → (A ∨ B → C) :=
  fun f g h => h.elim f g

/-! ## Parte III — Negazione e falso (tutto costruttivo) -/

/-- 1.7 — `A → ¬¬A`. Il termine è `λa.λk. k a`: la doppia negazione
«applica il continuation». -/
theorem nn_intro : A → ¬¬A := by
  intro a hna
  exact hna a

theorem nn_intro' : A → ¬¬A :=
  fun a hna => hna a

/-- 1.8 — Contrapposizione: è la composizione `hb ∘ f`. -/
theorem contrap : (A → B) → (¬B → ¬A) := by
  intro f hb a
  exact hb (f a)

/-- 1.9 — Ex falso quodlibet: l'eliminatore del tipo vuoto. -/
theorem ex_falso : False → A := by
  intro h
  exact h.elim

theorem ex_falso' : False → A :=
  fun h => h.elim

/-- 1.10 — De Morgan, la metà costruttiva. -/
theorem demorgan_or : ¬(A ∨ B) ↔ ¬A ∧ ¬B := by
  constructor
  · intro h
    constructor
    · intro a; exact h (Or.inl a)
    · intro b; exact h (Or.inr b)
  · rintro ⟨hna, hnb⟩ (a | b)
    · exact hna a
    · exact hnb b

/-- 1.11 — Non contraddizione: costruttiva, a differenza del terzo escluso. -/
theorem non_contrad : ¬(A ∧ ¬A) := by
  rintro ⟨a, na⟩
  exact na a

/-- 1.12 — Il terzo escluso non è refutabile.

L'idea: da `h : ¬(A ∨ ¬A)` si ricava `¬A` (perché da `A` seguirebbe
`A ∨ ¬A`, che `h` rifiuta); ma allora `A ∨ ¬A` vale per la destra, di
nuovo contro `h`. Si usa `h` due volte, ed è essenziale che lo si possa
fare: è il motivo per cui la doppia negazione «recupera» il classico. -/
theorem nn_lem : ¬¬(A ∨ ¬A) := by
  intro h
  apply h
  right
  intro a
  exact h (Or.inl a)

theorem nn_lem' : ¬¬(A ∨ ¬A) :=
  fun h => h (Or.inr (fun a => h (Or.inl a)))

/-! ## Parte IV — Dove il costruttivismo si ferma -/

/-- 1.13 — Eliminazione della doppia negazione: **classica**. -/
theorem nn_elim : ¬¬A → A := by
  intro h
  by_contra hA
  exact h hA

/-- 1.14 — Legge di Peirce: puramente implicativa, eppure classica.
Il «programma» corrispondente è l'operatore di controllo `call/cc`. -/
theorem peirce : ((A → B) → A) → A := by
  intro h
  by_contra hA
  exact hA (h (fun a => absurd a hA))

/-- 1.15 — De Morgan, la metà classica. -/
theorem demorgan_and : ¬(A ∧ B) → ¬A ∨ ¬B := by
  intro h
  by_cases hA : A
  · right
    intro b
    exact h ⟨hA, b⟩
  · left
    exact hA

/-! ## 1.16 — Il confronto finale

Ecco la differenza fra L1 «BHK» e L1 «LEM», resa meccanicamente
ispezionabile dal kernel. -/

#print axioms nn_intro     -- non dipende da alcun assioma
#print axioms non_contrad  -- idem
#print axioms nn_lem       -- idem: costruttiva!
#print axioms nn_elim      -- propext, Classical.choice, Quot.sound
#print axioms peirce       -- idem
#print axioms demorgan_and -- idem

end Soluzioni.Foglio1
