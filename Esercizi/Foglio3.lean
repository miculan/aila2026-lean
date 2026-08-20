/-
  AILA 2026 — Scuola Estiva di Logica, Bardonecchia
  «Teoria della dimostrazione. Teoria dei tipi, Proof Assistants e AI»
  Marino Miculan — Università di Udine

  ══════════════════════════════════════════════════════════════════════
  FOGLIO 3 — Strutture algebriche da zero
  Lezione 5, blocco 1  (~55 minuti)
  ══════════════════════════════════════════════════════════════════════

  Obiettivo: passare da «logica al calcolatore» a «matematica al
  calcolatore». Definiamo monoidi e gruppi come *type class* e
  dimostriamo i primi risultati elementari usando **soltanto** gli
  assiomi — niente `simp` a caso, niente Mathlib: qui si ragiona.

  Lo strumento nuovo è `calc`, che permette di scrivere una catena di
  uguaglianze come si farebbe alla lavagna, giustificando ogni passo.

  Soluzioni: `Soluzioni/Foglio3.lean`.
-/

import Mathlib.Tactic

namespace Foglio3

/-! ════════════════════════════════════════════════════════════════════
    PARTE I — Monoidi
    ════════════════════════════════════════════════════════════════════ -/

class MyMonoid (M : Type) extends Mul M, One M where
  mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : M, 1 * a = a
  mul_one   : ∀ a : M, a * 1 = a

namespace MyMonoid

variable {M : Type} [MyMonoid M]

/-! ### Esercizio 3.1 — Unicità dell'unità
Se `e` si comporta da unità a sinistra, allora `e = 1`. Una riga.
Suggerimento: `(mul_one e).symm.trans (h 1)`, oppure un `calc` di due passi. -/
theorem one_unique (e : M) (h : ∀ a : M, e * a = a) : e = 1 := by
  sorry

/-! ### Esercizio 3.2 — Potenze
La potenza `pow a n = a * ... * a` (n volte) è definita qui sotto per
ricorsione su `n`. Dimostra la legge degli esponenti. -/
def pow (a : M) : Nat → M
  | 0     => 1
  | n + 1 => pow a n * a

theorem pow_add (a : M) (m n : Nat) : pow a (m + n) = pow a m * pow a n := by
  sorry

end MyMonoid

/-! ════════════════════════════════════════════════════════════════════
    PARTE II — Gruppi, assiomatizzati al minimo

    Attenzione alla presentazione: chiediamo l'unità **solo a sinistra**
    e l'inverso **solo a sinistra**. Sono sufficienti, ma i lati destri
    (`a * 1 = a`, `a * a⁻¹ = 1`) diventano *teoremi* non banali — ed è
    esattamente questo a rendere gli esercizi istruttivi.
    ════════════════════════════════════════════════════════════════════ -/

class MyGroup (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : G, 1 * a = a
  inv_mul   : ∀ a : G, a⁻¹ * a = 1

namespace MyGroup

variable {G : Type} [MyGroup G]

/-! ### Esercizio 3.3 — Inverso destro
`a * a⁻¹ = 1`. Non è immediato: il trucco classico è moltiplicare a
sinistra per `a⁻¹⁻¹` e usare l'associatività. Prenditi il tempo che serve,
è il cuore del foglio.

Traccia:
  a * a⁻¹ = 1 * (a * a⁻¹)
          = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹)
          = a⁻¹⁻¹ * ((a⁻¹ * a) * a⁻¹)
          = a⁻¹⁻¹ * (1 * a⁻¹)
          = a⁻¹⁻¹ * a⁻¹
          = 1                                                            -/
theorem mul_inv (a : G) : a * a⁻¹ = 1 := by
  sorry

/-! ### Esercizio 3.4 — Unità destra
Ora `a * 1 = a` segue in poche righe da 3.3. -/
theorem mul_one (a : G) : a * 1 = a := by
  sorry

/-! ### Esercizio 3.5 — Cancellazione a sinistra -/
theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  sorry

/-! ### Esercizio 3.6 — Unicità dell'inverso
Se `a * b = 1` allora `b` è *l'*inverso di `a`. -/
theorem inv_unique {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  sorry

/-! ### Esercizio 3.7 — Involutività dell'inverso -/
theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  sorry

/-! ### Esercizio 3.8 — L'inverso di un prodotto
«Calzini e scarpe»: l'ordine si rovescia. -/
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

/-! ### Esercizio 3.9 — L'inverso dell'unità -/
theorem inv_one : (1 : G)⁻¹ = 1 := by
  sorry

/-! ### Esercizio 3.10 — Un gruppo con x² = 1 è abeliano
Classico esercizio da primo corso di algebra. Qui si vede bene la
differenza fra «lo so fare» e «lo so scrivere in modo che una macchina
lo verifichi». -/
theorem comm_of_sq_eq_one (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  sorry

end MyGroup

/-! ════════════════════════════════════════════════════════════════════
    PARTE III — Un'istanza concreta

    Le type class servono a poco se non si sanno *istanziare*: qui si
    verifica che gli interi con l'addizione formano davvero un gruppo
    secondo la nostra definizione.
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 3.11 — ℤ additivo è un `MyGroup`
Attenzione: la nostra `class` è scritta in notazione moltiplicativa,
quindi va incapsulata. `Int` con `*` **non** è un gruppo (0 non ha
inverso), perciò usiamo un tipo wrapper la cui moltiplicazione è
l'addizione di ℤ. Riempi i campi mancanti. -/

structure ZAdd where
  val : Int

namespace ZAdd

instance : Mul ZAdd := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : One ZAdd := ⟨⟨0⟩⟩
instance : Inv ZAdd := ⟨fun a => ⟨-a.val⟩⟩

@[simp] theorem mul_def (a b : ZAdd) : a * b = ⟨a.val + b.val⟩ := rfl
@[simp] theorem one_def : (1 : ZAdd) = ⟨0⟩ := rfl
@[simp] theorem inv_def (a : ZAdd) : a⁻¹ = ⟨-a.val⟩ := rfl

instance : MyGroup ZAdd where
  mul_assoc := by sorry
  one_mul   := by sorry
  inv_mul   := by sorry

-- Una volta istanziata la classe, TUTTI i teoremi dimostrati sopra
-- valgono gratis su `ZAdd`. Decommenta per verificarlo:
-- example (a : ZAdd) : a * a⁻¹ = 1 := MyGroup.mul_inv a

end ZAdd

/-! ════════════════════════════════════════════════════════════════════
    PARTE IV — Omomorfismi (facoltativo, se avanza tempo)
    ════════════════════════════════════════════════════════════════════ -/

structure MyHom (G H : Type) [MyGroup G] [MyGroup H] where
  toFun    : G → H
  map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b

namespace MyHom

variable {G H : Type} [MyGroup G] [MyGroup H]

/-! ### Esercizio 3.12 — Un omomorfismo preserva l'unità
Non è un assioma: si dimostra. Suggerimento: parti da `f 1 = f (1 * 1)`
e usa la cancellazione (3.5). -/
theorem map_one (f : MyHom G H) : f.toFun 1 = 1 := by
  sorry

/-! ### Esercizio 3.13 — …e gli inversi -/
theorem map_inv (f : MyHom G H) (a : G) : f.toFun a⁻¹ = (f.toFun a)⁻¹ := by
  sorry

end MyHom

end Foglio3
