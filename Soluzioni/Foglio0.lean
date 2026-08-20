/-
  AILA 2026 — SOLUZIONI del Foglio 0 (riscaldamento).
  Non guardarle prima di esserti bloccato per qualche minuto.
-/

import Mathlib.Tactic

namespace Soluzioni.Foglio0

/-! ### 0.1 — Identità polimorfa -/

def identita : ∀ X : Type, X → X :=
  fun _ x => x

#eval identita Nat 42
#eval identita String "ciao"

-- In tactic mode sarebbe:
example : ∀ X : Type, X → X := by
  intro X x
  exact x

/-! ### 0.2 — Il combinatore K nei due stili -/

theorem k_term (A B : Prop) : A → (B → A) :=
  fun a _ => a

theorem k_tac (A B : Prop) : A → (B → A) := by
  intro a _
  exact a

-- e sono lo stesso termine:
example (A B : Prop) : k_term A B = k_tac A B := rfl

/-! ### 0.3 — Uguaglianze per calcolo

`rfl` chiude ciò che vale per uguaglianza *definizionale*: qui basta per
tutti e tre, perché su ℕ i letterali si calcolano. `decide` e `norm_num`
sono alternative più robuste quando il calcolo non è immediato. -/

example : 2 + 2 = 4 := by rfl
example : (List.range 4).length = 4 := by rfl
example : 12345 * 6789 = 83810205 := by norm_num

-- varianti equivalenti
example : 2 + 2 = 4 := by decide
example : (List.range 4).length = 4 := by simp
example : 12345 * 6789 = 83810205 := by decide

/-! ### 0.4 — Definire e calcolare -/

def doppio (n : Nat) : Nat := 2 * n

#eval doppio 21

example : doppio 21 = 42 := by rfl

-- che raddoppi *davvero*, per ogni n:
theorem doppio_eq (n : Nat) : doppio n = n + n := by
  simp [doppio, Nat.two_mul]

end Soluzioni.Foglio0
