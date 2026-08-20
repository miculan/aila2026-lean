/-
  AILA 2026 — Scuola Estiva di Logica, Bardonecchia
  «Teoria della dimostrazione. Teoria dei tipi, Proof Assistants e AI»
  Marino Miculan — Università di Udine

  ══════════════════════════════════════════════════════════════════════
  FOGLIO 4 — Mathlib, automazione e ricerca dei lemmi
  Lezione 5, blocco 2  (~45 minuti)
  ══════════════════════════════════════════════════════════════════════

  Obiettivo: smettere di reinventare la ruota. Mathlib è una libreria di
  ~1,7 milioni di righe e ~200 000 teoremi: la competenza che serve non è
  ricordarli, è **saperli trovare** e sapere quale automazione delegare.

  GLI STRUMENTI DI RICERCA
    exact?          cerca un lemma che chiuda esattamente il goal
    apply?          cerca lemmi applicabili (goal parziale)
    rw?             cerca riscritture possibili
    simp?           mostra quali lemmi userebbe `simp` (utile per capire)
    open ... in #find    ricerca per forma
    Loogle   https://loogle.lean-lang.org   ricerca per pattern di tipo
    Moogle   https://www.moogle.ai          ricerca in linguaggio naturale
    LeanSearch  https://leansearch.net      idem, con enunciati in inglese

  L'AUTOMAZIONE
    rfl        uguaglianza definizionale
    simp       riscrittura con la base di lemmi marcati @[simp]
    ring       identità in anelli/semianelli commutativi
    field_simp normalizza espressioni con divisioni
    linarith   combinazioni lineari di ipotesi su ordini
    nlinarith  idem, con qualche prodotto
    omega      aritmetica lineare su ℕ/ℤ (decidibile)
    positivity dimostra 0 < e, 0 ≤ e, e ≠ 0
    norm_num   calcolo numerico
    decide     valuta una proposizione decidibile
    aesop      ricerca automatica generica
    group / abel   normalizza espressioni in gruppi (non) commutativi

  Regola d'oro da tenere a mente per L6: l'automazione chiude i passaggi
  *noiosi*, non decide quale sia il passaggio giusto. La differenza fra
  `omega` e un dimostratore neurale è tutta lì.

  Soluzioni: `Soluzioni/Foglio4.lean`.
-/

import Mathlib.Tactic

namespace Foglio4

/-! ════════════════════════════════════════════════════════════════════
    PARTE I — Scegliere l'automazione giusta

    Ogni goal qui sotto si chiude con **una sola** tattica fra quelle
    elencate in testa al file. Trova quella giusta. (Provarne una
    sbagliata non costa nulla: è il modo migliore per impararle.)
    ════════════════════════════════════════════════════════════════════ -/

example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by sorry

example (n : ℕ) (h : n > 3) : n ≥ 4 := by sorry

example (a b : ℤ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by sorry

example : (2:ℕ)^10 = 1024 := by sorry

example (x : ℝ) (hx : 0 < x) : 0 < x^3 + x := by sorry

example (l : List ℕ) : (l ++ []).length = l.length := by sorry

example (G : Type) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE II — Trovare il lemma

    Sostituisci ogni `sorry` con `exact?` (o `apply?`), leggi il
    suggerimento nell'Infoview e poi **incolla il lemma trovato** al
    posto di `exact?`: lasciare `exact?` nel sorgente è lento e fragile.
    Annota accanto il nome del lemma: costruirsi un vocabolario di
    Mathlib è metà del lavoro.
    ════════════════════════════════════════════════════════════════════ -/

example (a b : ℕ) : a + b = b + a := by sorry

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by sorry

example (s t : Set ℕ) (h : s ⊆ t) (x : ℕ) (hx : x ∈ s) : x ∈ t := by sorry

example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ)
    (h : f a = f b) : a = b := by sorry

/-! ### Esercizio 4.1 — Esistono infiniti primi
L'enunciato è in Mathlib. Trovalo (`exact?`, oppure cerca «infinite
primes» su LeanSearch) e usalo. -/
theorem infiniti_primi (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  sorry

/-! ### Esercizio 4.2 — √2 è irrazionale
Anche questo è in Mathlib, con un nome che vale la pena conoscere.
Suggerimento: cerca `Nat.Prime.irrational_sqrt` oppure `irrational_sqrt_two`. -/
theorem radice_due_irrazionale : Irrational (Real.sqrt 2) := by
  sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE III — La gerarchia algebrica di Mathlib

    Nel Foglio 3 abbiamo definito `MyGroup` da zero. Mathlib fa lo stesso,
    ma con una gerarchia di ~100 classi collegate da ereditarietà
    multipla. Il prezzo è il *diamond problem*: due cammini diversi verso
    la stessa struttura devono produrre istanze **definizionalmente**
    uguali, altrimenti `rfl` smette di funzionare in modi misteriosi.
    ════════════════════════════════════════════════════════════════════ -/

-- Guarda quante strutture ha ℝ, e da dove le eredita:
-- #synth AddGroup ℤ
-- #synth CommRing ℤ
-- #synth LinearOrder ℕ

/-! ### Esercizio 4.3 — Lavorare in un gruppo astratto
Rifai l'esercizio 3.10 (x² = 1 ⇒ abeliano), stavolta con la classe
`Group` di Mathlib. Nota quanto è più corto: tutti i lemmi ausiliari
del Foglio 3 sono già lì. -/
theorem abeliano_di_quadrati (G : Type) [Group G] (h : ∀ x : G, x * x = 1)
    (a b : G) : a * b = b * a := by
  sorry

/-! ### Esercizio 4.4 — Un sottogruppo
Dimostra che i multipli di 3 formano un sottogruppo di ℤ, riempiendo i
campi della struttura `AddSubgroup`. -/
def multipliDiTre : AddSubgroup ℤ where
  carrier := {n : ℤ | (3:ℤ) ∣ n}
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE IV — Un po' di matematica vera
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 4.5 — La somma di Gauss, versione Mathlib
Nel Foglio 2 l'abbiamo dimostrata a mano per induzione. Qui usa
`Finset.sum` e cerca il lemma già pronto (`Finset.sum_range_id_mul_two`
o `Gauss`). Confronta le due esperienze. -/
theorem gauss (n : ℕ) : (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := by
  sorry

/-! ### Esercizio 4.6 — Disuguaglianza delle medie (caso n = 2)
Per ogni x, y reali: la media geometrica non supera quella aritmetica.
Suggerimento: parti da `(x - y)^2 ≥ 0` e usa `nlinarith`. -/
theorem am_gm (x y : ℝ) : x * y ≤ (x^2 + y^2) / 2 := by
  sorry

/-! ### Esercizio 4.7 — Induzione forte
Ogni naturale ≥ 2 ha un divisore primo. Serve l'induzione forte
(`Nat.strong_induction_on`), oppure — molto più semplice — il lemma di
Mathlib che fa esattamente questo: trovalo. -/
theorem esiste_divisore_primo (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n := by
  sorry

/-! ════════════════════════════════════════════════════════════════════
    PARTE V — L'enunciato è la parte difficile

    Il kernel garantisce che la *dimostrazione* è corretta; non può
    garantire che l'*enunciato* dica ciò che intendevi. È il punto
    epistemologico centrale di L6, e conviene toccarlo con mano.
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 4.8 — Enunciati sbagliati che si dimostrano lo stesso
Ciascuno dei tre enunciati seguenti è *vero e dimostrabile*, ma **non**
dice ciò che il commento sopra di esso pretende. Trova il difetto di
ognuno e riscrivi l'enunciato corretto (dimostrandolo, se sai farlo). -/

-- «Ogni funzione continua su [0,1] ha un massimo»
example : ∀ f : ℝ → ℝ, ∃ x : ℝ, f x = f x := by sorry

-- «f è iniettiva»
example (f : ℕ → ℕ) : ∀ a b : ℕ, a = b → f a = f b := by sorry

-- «esiste un numero primo maggiore di ogni n»
example : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∨ n ≤ p := by sorry

/-! ### Esercizio 4.9 — Formalizzare un enunciato informale
Scrivi tu l'enunciato Lean, poi dimostralo (o lascialo con `sorry` se è
troppo lungo: qui il punto è la *formalizzazione*, non la dimostrazione).

  «Se una funzione f : ℝ → ℝ è monotona crescente e iniettiva, allora è
   strettamente crescente.»

Suggerimento: `Monotone`, `Function.Injective`, `StrictMono` sono già in
Mathlib — la difficoltà è mettere insieme i pezzi nell'ordine giusto. -/

-- theorem mio_enunciato ... := ...

end Foglio4
