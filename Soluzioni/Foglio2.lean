/-
  AILA 2026 — SOLUZIONI del Foglio 2 (tipi induttivi e induzione).
-/

import Mathlib.Tactic

namespace Soluzioni.Foglio2

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

namespace MyNat

def add : MyNat → MyNat → MyNat
  | m, zero    => m
  | m, succ n  => succ (add m n)

instance : Add MyNat := ⟨add⟩

@[simp] theorem add_zero (m : MyNat) : m + zero = m := rfl
@[simp] theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := rfl

/-- 2.1 — `zero + n = n`: qui serve l'induzione, perché la ricorsione di
`add` guarda il **secondo** argomento e `zero + n` resta bloccato. -/
theorem zero_add (n : MyNat) : zero + n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [add_succ, ih]

/-- 2.2 — `succ` si può portare fuori anche da sinistra. -/
theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [add_succ, ih, add_succ]

/-- 2.3 — Associatività: induzione sull'ultimo argomento. -/
theorem add_assoc (m n p : MyNat) : (m + n) + p = m + (n + p) := by
  induction p with
  | zero      => rfl
  | succ p ih => rw [add_succ, add_succ, add_succ, ih]

/-- 2.4 — Commutatività: il primo teorema che riusa i lemmi precedenti. -/
theorem add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero      => rw [add_zero, zero_add]
  | succ n ih => rw [add_succ, ih, succ_add]

def mul : MyNat → MyNat → MyNat
  | _, zero   => zero
  | m, succ n => mul m n + m

instance : Mul MyNat := ⟨mul⟩

@[simp] theorem mul_zero (m : MyNat) : m * zero = zero := rfl
@[simp] theorem mul_succ (m n : MyNat) : m * succ n = m * n + m := rfl

/-- 2.5 — `zero` assorbente a sinistra: di nuovo il lato non definizionale. -/
theorem zero_mul (n : MyNat) : zero * n = zero := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [mul_succ, ih, add_zero]

end MyNat

/-! ## La somma di Gauss -/

def somma : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + somma n

/-- 2.6 — `2 * (0 + 1 + ... + n) = n * (n+1)`, senza divisioni.
Nel passo induttivo `ring` chiude l'identità polinomiale; a mano
servirebbero distributività e commutatività, ed è esattamente il tipo di
passaggio noioso che conviene delegare (cfr. L6). -/
theorem due_somma (n : Nat) : 2 * somma n = n * (n + 1) := by
  induction n with
  | zero      => rfl
  | succ n ih =>
    simp only [somma, Nat.mul_add, ih]
    ring

/-! ## Liste -/

/-- 2.7 — La lunghezza è un omomorfismo da `++` a `+`. -/
theorem length_append {α : Type} (l l' : List α) :
    (l ++ l').length = l.length + l'.length := by
  induction l with
  | nil          => simp
  | cons a l ih  =>
    simp only [List.cons_append, List.length_cons, ih]
    omega

/-- 2.8 — Inversione di una concatenazione. -/
theorem reverse_append {α : Type} (l l' : List α) :
    (l ++ l').reverse = l'.reverse ++ l.reverse := by
  induction l with
  | nil         => simp
  | cons a l ih => simp [ih]

/-- 2.8bis — L'inversione è un'involuzione. -/
theorem reverse_reverse {α : Type} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil         => rfl
  | cons a l ih => simp [ih]

/-! ## Alberi binari -/

inductive Albero (α : Type) where
  | foglia : Albero α
  | nodo   : Albero α → α → Albero α → Albero α

namespace Albero

def numNodi {α : Type} : Albero α → Nat
  | foglia      => 0
  | nodo s _ d  => numNodi s + 1 + numNodi d

def numFoglie {α : Type} : Albero α → Nat
  | foglia      => 1
  | nodo s _ d  => numFoglie s + numFoglie d

/-- 2.9 — Le foglie sono una più dei nodi interni.
Nota le **due** ipotesi induttive `ihs` e `ihd`, una per sottoalbero:
sono esattamente gli argomenti che l'eliminatore di `Albero` richiede. -/
theorem foglie_eq_nodi_succ {α : Type} (t : Albero α) :
    numFoglie t = numNodi t + 1 := by
  induction t with
  | foglia => rfl
  | nodo s x d ihs ihd =>
    simp only [numFoglie, numNodi, ihs, ihd]
    omega

/-- 2.10 — Lo specchio è un'involuzione. -/
def specchio {α : Type} : Albero α → Albero α
  | foglia     => foglia
  | nodo s x d => nodo (specchio d) x (specchio s)

theorem specchio_specchio {α : Type} (t : Albero α) :
    specchio (specchio t) = t := by
  induction t with
  | foglia => rfl
  | nodo s x d ihs ihd => simp only [specchio, ihs, ihd]

end Albero

end Soluzioni.Foglio2
