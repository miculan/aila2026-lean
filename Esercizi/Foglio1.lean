/-
  AILA 2026 — Scuola Estiva di Logica, Bardonecchia
  «Teoria della dimostrazione. Teoria dei tipi, Proof Assistants e AI»
  Marino Miculan — Università di Udine

  ══════════════════════════════════════════════════════════════════════
  FOGLIO 1 — Logica proposizionale come esercizio di Curry–Howard
  Lezione 4, blocco 2  (~45 minuti)
  ══════════════════════════════════════════════════════════════════════

  Obiettivo: rifare *al calcolatore* la tabella di corrispondenza di L1.

      logica intuizionista        teoria dei tipi
      ─────────────────────       ────────────────────────
      A → B                       tipo funzione  A → B
      A ∧ B                       prodotto       A × B
      A ∨ B                       somma          A ⊕ B
      ⊥                           tipo vuoto     Empty
      ¬A  :=  A → ⊥               A → Empty
      dimostrazione               termine
      normalizzazione             riduzione β

  Ogni esercizio si può fare in due modi: costruendo il termine a mano
  (term mode) oppure con le tattiche. Fallo almeno una volta in entrambi
  gli stili — è il punto dell'intera lezione.

  TATTICHE DI BASE
    intro h        introduce un'ipotesi (→-intro, ∀-intro)
    exact e        chiude il goal con il termine e
    apply f        applica f al goal (→-elim all'indietro)
    constructor    spezza un ∧ / ↔ nei suoi componenti (∧-intro)
    obtain ⟨a,b⟩ := h   smonta un ∧ / ∃  (∧-elim)
    rcases h with h1 | h2   analisi di casi su ∨  (∨-elim)
    left / right   sceglie un disgiunto (∨-intro)
    exact absurd a na   /  exact (na a).elim    (⊥-elim)
    by_contra h    ragionamento per assurdo — NON costruttivo!

  Soluzioni: `Soluzioni/Foglio1.lean`.
-/

import Mathlib.Tactic

namespace Foglio1

variable (A B C : Prop)

/-! ## 0. Riscaldamento svolto

Gli esempi seguenti sono già fatti: leggili prima di cominciare. -/

-- Transitività dell'implicazione: lo stesso termine costruito alla
-- lavagna in L1, ora verificato dal kernel.
example (h1 : A → B) (h2 : B → C) : A → C :=
  fun a => h2 (h1 a)

example (h1 : A → B) (h2 : B → C) : A → C := by
  intro a
  exact h2 (h1 a)

-- Congiunzione: `⟨_, _⟩` è la coppia, `.1`/`.2` le proiezioni.
example (h : A ∧ B) : B ∧ A :=
  ⟨h.2, h.1⟩

-- Disgiunzione: `Or.inl`/`Or.inr` sono le iniezioni della somma,
-- l'analisi di casi è l'eliminatore.
example (h : A ∨ B) : B ∨ A := by
  rcases h with ha | hb
  · right; exact ha
  · left;  exact hb

/-! ════════════════════════════════════════════════════════════════════
    PARTE I — Implicazione: i combinatori
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 1.1 — Combinatore K
Il λ-termine è `λx.λy.x`. -/
theorem comb_K : A → B → A := by
  sorry

/-! ### Esercizio 1.2 — Combinatore S
Il λ-termine è `λx.λy.λz. (x z) (y z)`. Fallo prima in term mode: è
l'esercizio che convince più di ogni discorso che «dimostrare = programmare». -/
theorem comb_S : (A → B → C) → (A → B) → A → C := by
  sorry

/-! ### Esercizio 1.3 — Composizione
Riscrivi la transitività dell'implicazione *senza* usare `intro`, cioè
scrivendo direttamente il termine dopo `:=`. -/
theorem comp : (A → B) → (B → C) → (A → C) :=
  sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE II — Congiunzione e disgiunzione
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 1.4 — Currying
Il tipo `A ∧ B → C` è isomorfo a `A → B → C`: la congiunzione «è» il
prodotto e l'isomorfismo è esattamente il currying. -/
theorem curry : (A ∧ B → C) ↔ (A → B → C) := by
  sorry

/-! ### Esercizio 1.5 — Distributività
Uno dei due versi è puro assemblaggio, l'altro richiede analisi di casi. -/
theorem distrib : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
  sorry

/-! ### Esercizio 1.6 — Eliminazione della disgiunzione
È il principio di «ragionamento per casi»: nella lettura dei tipi, è
l'eliminatore del tipo somma. -/
theorem or_elim : (A → C) → (B → C) → (A ∨ B → C) := by
  sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE III — Negazione e falso

    Ricorda: `¬A` è *definizionalmente* `A → False`. Quindi se hai
    `h : ¬A` e `a : A`, il termine `h a : False` — e da `False` segue
    tutto, con `.elim` (ex falso quodlibet, l'eliminatore del tipo vuoto).
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 1.7 — Introduzione della doppia negazione
Attenzione: questa direzione è **costruttiva**. Il termine è brevissimo. -/
theorem nn_intro : A → ¬¬A := by
  sorry

/-! ### Esercizio 1.8 — Contrapposizione (verso costruttivo) -/
theorem contrap : (A → B) → (¬B → ¬A) := by
  sorry

/-! ### Esercizio 1.9 — Ex falso -/
theorem ex_falso : False → A := by
  sorry

/-! ### Esercizio 1.10 — De Morgan, la metà costruttiva
Questa equivalenza vale in logica intuizionista, in entrambi i versi. -/
theorem demorgan_or : ¬(A ∨ B) ↔ ¬A ∧ ¬B := by
  sorry

/-! ### Esercizio 1.11 — Non contraddizione
Anche `¬(A ∧ ¬A)` è perfettamente costruttiva: notare il contrasto con
il terzo escluso `A ∨ ¬A`, che invece non lo è. -/
theorem non_contrad : ¬(A ∧ ¬A) := by
  sorry

/-! ### Esercizio 1.12 — Il terzo escluso non si può *refutare*
`¬¬(A ∨ ¬A)` è dimostrabile costruttivamente, pur non essendolo
`A ∨ ¬A`. Moralmente: l'intuizionismo non *nega* il terzo escluso, si
limita a non asserirlo. Questo è l'esercizio più bello del foglio.

Suggerimento: assumi `h : ¬(A ∨ ¬A)`; usalo due volte, la seconda con
un `¬A` costruito a partire dalla prima. -/
theorem nn_lem : ¬¬(A ∨ ¬A) := by
  sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE IV — Dove il costruttivismo si ferma

    Gli enunciati seguenti **non** sono dimostrabili in logica
    intuizionista. Procedi così, in quest'ordine:

      1. prova sinceramente a dimostrarli con le sole tattiche
         costruttive (`intro`, `exact`, `apply`, `rcases`, `left`,
         `right`, `constructor`): osserva *dove* ti blocchi;
      2. poi usa `by_contra h` (assurdo) oppure `rcases Classical.em A`
         (terzo escluso) e concludi;
      3. infine confronta l'output di `#print axioms` fra un teorema
         della Parte III e uno di questa parte.
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 1.13 — Eliminazione della doppia negazione -/
theorem nn_elim : ¬¬A → A := by
  sorry

/-! ### Esercizio 1.14 — Legge di Peirce
Notevole: è puramente implicativa, non contiene né ¬ né ⊥, eppure è
classica. Il corrispondente «programma» è l'operatore di controllo
call/cc — Curry–Howard si estende alla logica classica, ma con effetti. -/
theorem peirce : ((A → B) → A) → A := by
  sorry

/-! ### Esercizio 1.15 — De Morgan, la metà classica -/
theorem demorgan_and : ¬(A ∧ B) → ¬A ∨ ¬B := by
  sorry

/-! ### Esercizio 1.16 — Il confronto finale

Decommenta le due righe seguenti quando hai finito e leggi l'Infoview:
la prima dimostrazione non usa alcun assioma, la seconda poggia su
`Classical.choice`. È la differenza fra L1 «BHK» e L1 «LEM», resa
meccanicamente ispezionabile. -/

-- #print axioms nn_intro     -- 'nn_intro' does not depend on any axioms
-- #print axioms nn_elim      -- ... depends on axioms: [propext, Classical.choice, Quot.sound]

end Foglio1
