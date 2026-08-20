/-
  AILA 2026 — Scuola Estiva di Logica, Bardonecchia
  «Teoria della dimostrazione. Teoria dei tipi, Proof Assistants e AI»
  Marino Miculan — Università di Udine

  ══════════════════════════════════════════════════════════════════════
  FOGLIO 2 — Tipi induttivi e induzione
  Lezione 4, blocco 3  (~40 minuti)
  ══════════════════════════════════════════════════════════════════════

  Obiettivo: vedere in funzione ciò che a L3 è stato presentato in
  astratto — un tipo induttivo è dato dai suoi **costruttori**, e il suo
  **eliminatore** *è* il principio di induzione. La tattica `induction`
  non è altro che l'eliminatore con un'interfaccia comoda.

  Il tema portante del foglio è la distinzione, cruciale in L3, fra

    • uguaglianza DEFINIZIONALE (giudizionale) a ≡ b : A
      — vale per calcolo, in Lean la chiude `rfl`;
    • uguaglianza PROPOSIZIONALE  Id_A(a,b)
      — è un tipo, va dimostrata, tipicamente per induzione.

  Soluzioni: `Soluzioni/Foglio2.lean`.
-/

import Mathlib.Tactic

namespace Foglio2

/-! ## 1. Un tipo induttivo fatto in casa

`MyNat` è definito esattamente come i naturali di Peano di L3: due
costruttori, `zero` e `succ`. -/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

namespace MyNat

-- L'eliminatore generato automaticamente È il principio di induzione:
-- guarda il suo tipo nell'Infoview e confrontalo con la regola di L3.
#check @MyNat.rec

-- La somma, definita per ricorsione **sul secondo argomento**.
def add : MyNat → MyNat → MyNat
  | m, zero    => m
  | m, succ n  => succ (add m n)

instance : Add MyNat := ⟨add⟩

@[simp] theorem add_zero (m : MyNat) : m + zero = m := rfl
@[simp] theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := rfl

/-! ### La distinzione chiave

`m + zero = m` vale **per definizione**: il pattern matching scatta subito,
quindi `rfl` basta (vedi sopra). Ma `zero + n = n` **non** vale per
definizione: `zero + n` resta bloccato finché `n` è una variabile, perché
la ricorsione guarda il secondo argomento. Serve l'induzione. -/

/-! ### Esercizio 2.1 — L'altra unità
Dimostra `zero + n = n` per induzione su `n`. -/
theorem zero_add (n : MyNat) : zero + n = n := by
  sorry

/-! ### Esercizio 2.2 — succ a sinistra -/
theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  sorry

/-! ### Esercizio 2.3 — Associatività -/
theorem add_assoc (m n p : MyNat) : (m + n) + p = m + (n + p) := by
  sorry

/-! ### Esercizio 2.4 — Commutatività
Servono 2.1 e 2.2: è il primo esempio di dimostrazione che riusa lemmi
precedenti, cioè di *sviluppo di una teoria*. -/
theorem add_comm (m n : MyNat) : m + n = n + m := by
  sorry

/-! ### Esercizio 2.5 — Un'operazione nuova
Il prodotto è definito qui sotto per ricorsione sul secondo argomento,
sullo stesso schema della somma. Dimostra che `zero` è assorbente **a
sinistra** — di nuovo il lato «difficile», quello che non è definizionale. -/
def mul : MyNat → MyNat → MyNat
  | _, zero   => zero
  | m, succ n => mul m n + m

instance : Mul MyNat := ⟨mul⟩

@[simp] theorem mul_zero (m : MyNat) : m * zero = zero := rfl
@[simp] theorem mul_succ (m n : MyNat) : m * succ n = m * n + m := rfl

theorem zero_mul (n : MyNat) : zero * n = zero := by
  sorry

end MyNat

/-! ════════════════════════════════════════════════════════════════════
    2. Gli stessi giochi sui `Nat` di Lean
    ════════════════════════════════════════════════════════════════════ -/

-- Il fenomeno è identico sui naturali della libreria standard:
example (n : Nat) : n + 0 = n := rfl        -- definizionale
example (n : Nat) : 0 + n = n := by omega   -- proposizionale (qui: automazione)

/-! ### Esercizio 2.6 — La somma di Gauss

La somma dei primi `n` naturali è definita qui sotto. Dimostra la formula
chiusa nella forma senza divisioni `2 * somma n = n * (n + 1)`.
Suggerimento: `induction n with | zero => .. | succ n ih => ..`, e nel
passo induttivo `simp [somma, ih]` seguito da `ring` oppure `omega`. -/

def somma : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + somma n

theorem due_somma (n : Nat) : 2 * somma n = n * (n + 1) := by
  sorry

/-! ════════════════════════════════════════════════════════════════════
    3. Liste: induzione su un altro tipo induttivo
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 2.7 — Lunghezza di una concatenazione -/
theorem length_append {α : Type} (l l' : List α) :
    (l ++ l').length = l.length + l'.length := by
  sorry

/-! ### Esercizio 2.8 — L'inversione è un'involuzione
Serve un lemma ausiliario su `reverse` di una concatenazione: dimostralo
prima (o cercalo in Mathlib con `exact?`). -/
theorem reverse_append {α : Type} (l l' : List α) :
    (l ++ l').reverse = l'.reverse ++ l.reverse := by
  sorry

theorem reverse_reverse {α : Type} (l : List α) : l.reverse.reverse = l := by
  sorry

/-! ════════════════════════════════════════════════════════════════════
    4. Un tipo induttivo con più di una ricorsione: gli alberi
    ════════════════════════════════════════════════════════════════════ -/

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

/-! ### Esercizio 2.9 — Foglie e nodi
In un albero binario, le foglie sono sempre una più dei nodi interni.
L'ipotesi induttiva qui è *doppia* (una per sottoalbero): guarda come
`induction ... with` le presenta entrambe nel contesto. -/
theorem foglie_eq_nodi_succ {α : Type} (t : Albero α) :
    numFoglie t = numNodi t + 1 := by
  sorry

/-! ### Esercizio 2.10 — Rispecchiamento (facoltativo)
Lo specchio di un albero è definito qui sotto. Dimostra che è
un'involuzione. -/
def specchio {α : Type} : Albero α → Albero α
  | foglia     => foglia
  | nodo s x d => nodo (specchio d) x (specchio s)

theorem specchio_specchio {α : Type} (t : Albero α) :
    specchio (specchio t) = t := by
  sorry

end Albero

end Foglio2
