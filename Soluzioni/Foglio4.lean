/-
  AILA 2026 — SOLUZIONI del Foglio 4 (Mathlib, automazione, ricerca).

  Accanto a ogni soluzione trovata con `exact?` è annotato il nome del
  lemma: costruirsi un vocabolario di Mathlib è metà del lavoro.
-/

import Mathlib.Tactic

namespace Soluzioni.Foglio4

/-! ## Parte I — Scegliere l'automazione giusta -/

example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring

example (n : ℕ) (h : n > 3) : n ≥ 4 := by omega

example (a b : ℤ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega

example : (2:ℕ)^10 = 1024 := by norm_num

example (x : ℝ) (hx : 0 < x) : 0 < x^3 + x := by positivity

example (l : List ℕ) : (l ++ []).length = l.length := by simp

example (G : Type) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group

-- alternative altrettanto valide:
example (a b : ℤ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := le_antisymm h1 h2
example (G : Type) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b

/-! ## Parte II — Trovare il lemma -/

example (a b : ℕ) : a + b = b + a := Nat.add_comm a b

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := add_le_add_left h c

example (s t : Set ℕ) (h : s ⊆ t) (x : ℕ) (hx : x ∈ s) : x ∈ t := h hx

example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ)
    (h : f a = f b) : a = b := hf h

/-- 4.1 — `Nat.exists_infinite_primes`. -/
theorem infiniti_primi (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n

/-- 4.2 — `irrational_sqrt_two`. -/
theorem radice_due_irrazionale : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

/-! ## Parte III — La gerarchia algebrica di Mathlib -/

#synth AddGroup ℤ
#synth CommRing ℤ
#synth LinearOrder ℕ

/-- 4.3 — Lo stesso enunciato del 3.10, ma con la classe `Group` di
Mathlib: `inv_eq_of_mul_eq_one_right`, `inv_inv` e `mul_inv_rev` sono
già disponibili, e la dimostrazione si accorcia di due terzi. -/
theorem abeliano_di_quadrati (G : Type) [Group G] (h : ∀ x : G, x * x = 1)
    (a b : G) : a * b = b * a := by
  have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h x)
  calc a * b
      = ((a * b)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (b⁻¹ * a⁻¹)⁻¹ := by rw [mul_inv_rev]
    _ = (b * a)⁻¹     := by rw [hinv b, hinv a]
    _ = b * a         := hinv _

/-- 4.4 — I multipli di 3 come sottogruppo di ℤ.
`dvd_add`, `dvd_zero`, `dvd_neg`: i tre assiomi sono tre lemmi già
presenti in Mathlib. -/
def multipliDiTre : AddSubgroup ℤ where
  carrier   := {n : ℤ | (3:ℤ) ∣ n}
  add_mem'  := fun ha hb => dvd_add ha hb
  zero_mem' := dvd_zero 3
  neg_mem'  := fun ha => dvd_neg.mpr ha

/-! ## Parte IV — Un po' di matematica vera -/

/-- 4.5 — La somma di Gauss è già in Mathlib: `Finset.sum_range_id_mul_two`.
Confronta con la dimostrazione per induzione del Foglio 2: là il punto era
capire l'induzione, qui è saper cercare. -/
theorem gauss (n : ℕ) : (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) :=
  Finset.sum_range_id_mul_two n

/-- 4.6 — Media geometrica ≤ media aritmetica (caso n = 2).
Il suggerimento `sq_nonneg (x - y)` è tutto ciò che serve a `nlinarith`:
l'automazione non trova l'idea, la sfrutta. -/
theorem am_gm (x y : ℝ) : x * y ≤ (x^2 + y^2) / 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- 4.7 — Ogni naturale ≥ 2 ha un divisore primo: `Nat.exists_prime_and_dvd`,
la cui ipotesi è `n ≠ 1` (e per `n = 0` funziona perché ogni primo divide 0). -/
theorem esiste_divisore_primo (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n :=
  Nat.exists_prime_and_dvd (by omega)

/-! ## Parte V — L'enunciato è la parte difficile -/

/-! ### 4.8 — I tre enunciati difettosi, e le loro correzioni -/

-- ✗ «Ogni funzione continua su [0,1] ha un massimo»
--   Difetto: `f x = f x` è una tautologia, vera per QUALUNQUE f e x. Non
--   si parla né di continuità, né di [0,1], né di massimo.
example : ∀ f : ℝ → ℝ, ∃ x : ℝ, f x = f x := fun _ => ⟨0, rfl⟩

-- ✓ enunciato corretto (teorema di Weierstrass su un compatto)
theorem weierstrass (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, f y ≤ f x := by
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hf.continuousOn
  exact ⟨x, hx, fun y hy => hmax hy⟩

-- ✗ «f è iniettiva»
--   Difetto: l'implicazione è girata. Questa dice che f è una FUNZIONE
--   (rispetta l'uguaglianza), cosa vera per definizione di funzione.
example (f : ℕ → ℕ) : ∀ a b : ℕ, a = b → f a = f b := fun _ _ h => by rw [h]

-- ✓ enunciato corretto: l'ipotesi e la conclusione vanno scambiate
example (f : ℕ → ℕ) (hf : Function.Injective f) :
    ∀ a b : ℕ, f a = f b → a = b := fun _ _ h => hf h

-- ✗ «esiste un numero primo maggiore di ogni n»
--   Difetto: `∨` invece di `∧`. Basta esibire p = 2, che è primo, e il
--   disgiunto sinistro è soddisfatto senza dire nulla su n.
example : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∨ n ≤ p := fun _ => ⟨2, Or.inl Nat.prime_two⟩

-- ✓ enunciato corretto
example : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n ≤ p := fun n => by
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, hnp⟩

/-! ### 4.9 — Formalizzare un enunciato informale

«Se f : ℝ → ℝ è monotona crescente e iniettiva, allora è strettamente
crescente.» I tre predicati esistono già; la difficoltà è solo scegliere
quelli giusti e comporli. -/

theorem strictMono_di_monotone_iniettiva (f : ℝ → ℝ)
    (hm : Monotone f) (hi : Function.Injective f) : StrictMono f :=
  hm.strictMono_of_injective hi

end Soluzioni.Foglio4
