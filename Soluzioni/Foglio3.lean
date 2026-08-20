/-
  AILA 2026 — SOLUZIONI del Foglio 3 (monoidi e gruppi da zero).

  Tutte le dimostrazioni usano SOLTANTO gli assiomi della classe: nessun
  `simp`, nessun lemma di Mathlib. È il punto dell'esercizio.
-/

import Mathlib.Tactic

namespace Soluzioni.Foglio3

/-! ## Parte I — Monoidi -/

class MyMonoid (M : Type) extends Mul M, One M where
  mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : M, 1 * a = a
  mul_one   : ∀ a : M, a * 1 = a

namespace MyMonoid

variable {M : Type} [MyMonoid M]

/-- 3.1 — L'unità sinistra è unica: basta valutarla in `1`. -/
theorem one_unique (e : M) (h : ∀ a : M, e * a = a) : e = 1 := by
  calc e = e * 1 := (MyMonoid.mul_one e).symm
    _    = 1     := h 1

def pow (a : M) : Nat → M
  | 0     => 1
  | n + 1 => pow a n * a

/-- 3.2 — Legge degli esponenti. L'induzione è su `n`, e il passo usa
l'associatività per riassociare `(aᵐ aⁿ) a` in `aᵐ (aⁿ a)`. -/
theorem pow_add (a : M) (m n : Nat) : pow a (m + n) = pow a m * pow a n := by
  induction n with
  | zero      => rw [pow]; exact (MyMonoid.mul_one _).symm
  | succ n ih =>
    show pow a (m + n + 1) = pow a m * pow a (n + 1)
    rw [pow, pow, ih, MyMonoid.mul_assoc]

end MyMonoid

/-! ## Parte II — Gruppi con assiomi minimi

Attenzione: `mul_one` e `mul_inv` **non** sono assiomi qui. Vanno
dimostrati, e l'ordine in cui si dimostrano non è indifferente. -/

class MyGroup (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : G, 1 * a = a
  inv_mul   : ∀ a : G, a⁻¹ * a = 1

namespace MyGroup

variable {G : Type} [MyGroup G]

/-- 3.3 — L'inverso è anche destro. Il trucco è inserire `1 = a⁻¹⁻¹ * a⁻¹`
davanti e riassociare: si crea un `a⁻¹ * a` che collassa a `1`. -/
theorem mul_inv (a : G) : a * a⁻¹ = 1 := by
  calc a * a⁻¹
      = 1 * (a * a⁻¹)                := (MyGroup.one_mul _).symm
    _ = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹)    := by rw [MyGroup.inv_mul]
    _ = a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹))    := MyGroup.mul_assoc _ _ _
    _ = a⁻¹⁻¹ * ((a⁻¹ * a) * a⁻¹)    := by rw [MyGroup.mul_assoc]
    _ = a⁻¹⁻¹ * (1 * a⁻¹)            := by rw [MyGroup.inv_mul]
    _ = a⁻¹⁻¹ * a⁻¹                  := by rw [MyGroup.one_mul]
    _ = 1                            := MyGroup.inv_mul _

/-- 3.4 — L'unità è anche destra: ora è facile, grazie a 3.3. -/
theorem mul_one (a : G) : a * 1 = a := by
  calc a * 1
      = a * (a⁻¹ * a)   := by rw [MyGroup.inv_mul]
    _ = (a * a⁻¹) * a   := (MyGroup.mul_assoc _ _ _).symm
    _ = 1 * a           := by rw [mul_inv]
    _ = a               := MyGroup.one_mul a

/-- 3.5 — Cancellazione a sinistra: si moltiplica per `a⁻¹` e si riassocia. -/
theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  calc b = 1 * b         := (MyGroup.one_mul b).symm
    _ = (a⁻¹ * a) * b    := by rw [MyGroup.inv_mul]
    _ = a⁻¹ * (a * b)    := MyGroup.mul_assoc _ _ _
    _ = a⁻¹ * (a * c)    := by rw [h]
    _ = (a⁻¹ * a) * c    := (MyGroup.mul_assoc _ _ _).symm
    _ = 1 * c            := by rw [MyGroup.inv_mul]
    _ = c                := MyGroup.one_mul c

/-- 3.6 — Unicità dell'inverso: da `a * b = 1` segue `b = a⁻¹`.
È il lemma che fa da grimaldello per tutti i successivi. -/
theorem inv_unique {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  apply mul_left_cancel (a := a)
  rw [h, mul_inv]

/-- 3.7 — L'inverso è involutivo: applicare 3.6 a `a⁻¹ * a = 1`. -/
theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
  (inv_unique (MyGroup.inv_mul a)).symm

/-- 3.8 — «Calzini e scarpe»: `(a*b)⁻¹ = b⁻¹ * a⁻¹`. -/
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    calc (a * b) * (b⁻¹ * a⁻¹)
        = a * (b * (b⁻¹ * a⁻¹))   := MyGroup.mul_assoc _ _ _
      _ = a * ((b * b⁻¹) * a⁻¹)   := by rw [MyGroup.mul_assoc]
      _ = a * (1 * a⁻¹)           := by rw [mul_inv]
      _ = a * a⁻¹                 := by rw [MyGroup.one_mul]
      _ = 1                       := mul_inv a
  exact (inv_unique h).symm

/-- 3.9 — L'unità è il proprio inverso. -/
theorem inv_one : (1 : G)⁻¹ = 1 :=
  (inv_unique (MyGroup.one_mul (1 : G))).symm

/-- 3.10 — Se ogni elemento è involutivo, il gruppo è abeliano.

L'idea: da `x * x = 1` segue `x⁻¹ = x` per ogni `x` (unicità
dell'inverso). Allora `a * b = ((a*b)⁻¹)⁻¹ = (b⁻¹ * a⁻¹)⁻¹ = (b*a)⁻¹ = b*a`. -/
theorem comm_of_sq_eq_one (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  have hinv : ∀ x : G, x⁻¹ = x := fun x => (inv_unique (h x)).symm
  calc a * b
      = ((a * b)⁻¹)⁻¹   := (inv_inv _).symm
    _ = (b⁻¹ * a⁻¹)⁻¹   := by rw [mul_inv_rev]
    _ = (b * a)⁻¹       := by rw [hinv b, hinv a]
    _ = b * a           := hinv _

end MyGroup

/-! ## Parte III — Un'istanza concreta: ℤ additivo -/

structure ZAdd where
  val : Int

namespace ZAdd

instance : Mul ZAdd := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : One ZAdd := ⟨⟨0⟩⟩
instance : Inv ZAdd := ⟨fun a => ⟨-a.val⟩⟩

@[simp] theorem mul_def (a b : ZAdd) : a * b = ⟨a.val + b.val⟩ := rfl
@[simp] theorem one_def : (1 : ZAdd) = ⟨0⟩ := rfl
@[simp] theorem inv_def (a : ZAdd) : a⁻¹ = ⟨-a.val⟩ := rfl

/-- 3.11 — Gli assiomi si riducono a fatti su ℤ, che `omega` chiude. -/
instance : MyGroup ZAdd where
  mul_assoc := by intro a b c; simp only [mul_def, ZAdd.mk.injEq]; omega
  one_mul   := by intro a; simp
  inv_mul   := by intro a; simp only [mul_def, inv_def, one_def, ZAdd.mk.injEq]; omega

-- Istanziata la classe, tutti i teoremi precedenti valgono gratis:
example (a : ZAdd) : a * a⁻¹ = 1 := MyGroup.mul_inv a
example (a b : ZAdd) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := MyGroup.mul_inv_rev a b

end ZAdd

/-! ## Parte IV — Omomorfismi -/

structure MyHom (G H : Type) [MyGroup G] [MyGroup H] where
  toFun    : G → H
  map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b

namespace MyHom

variable {G H : Type} [MyGroup G] [MyGroup H]

/-- 3.12 — Un omomorfismo preserva l'unità: non è un assioma, si dimostra
da `f 1 = f (1 * 1) = f 1 * f 1` per cancellazione. -/
theorem map_one (f : MyHom G H) : f.toFun 1 = 1 := by
  have h : f.toFun 1 * f.toFun 1 = f.toFun 1 * 1 := by
    rw [← f.map_mul', MyGroup.one_mul, MyGroup.mul_one]
  exact MyGroup.mul_left_cancel h

/-- 3.13 — …e gli inversi, per unicità dell'inverso. -/
theorem map_inv (f : MyHom G H) (a : G) : f.toFun a⁻¹ = (f.toFun a)⁻¹ := by
  have h : f.toFun a * f.toFun a⁻¹ = 1 := by
    rw [← f.map_mul', MyGroup.mul_inv, map_one]
  exact MyGroup.inv_unique h

end MyHom

end Soluzioni.Foglio3
