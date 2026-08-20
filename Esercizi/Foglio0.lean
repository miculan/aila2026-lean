/-
  AILA 2026 — Scuola Estiva di Logica, Bardonecchia
  «Teoria della dimostrazione. Teoria dei tipi, Proof Assistants e AI»
  Marino Miculan — Università di Udine

  ══════════════════════════════════════════════════════════════════════
  FOGLIO 0 — Riscaldamento: tour dell'ambiente
  Lezione 4, blocco 1  (~15 minuti)
  ══════════════════════════════════════════════════════════════════════

  Obiettivo: prendere confidenza con l'editor, con i comandi di
  interrogazione e con la differenza fra *term mode* e *tactic mode*.
  Nessuna dimostrazione difficile: qui si guarda, non si suda.

  ISTRUZIONI
  • Apri il file in VSCode. Il pannello «Lean Infoview» (⌘⇧Return, oppure
    l'icona ∀ in alto a destra) mostra lo stato della dimostrazione nel
    punto in cui si trova il cursore: è la cosa più importante dello
    schermo, tienilo sempre aperto.
  • Ogni esercizio è marcato `sorry`. Sostituiscilo con la tua soluzione.
  • Finché c'è un `sorry`, Lean segnala un warning giallo: è il promemoria
    che la dimostrazione è incompleta. Zero warning ⇒ foglio finito.
  • Soluzioni: `Soluzioni/Foglio0.lean`.
-/

import Mathlib.Tactic

namespace Foglio0

/-! ## 1. `#check` — chiedere il tipo

Nel mondo di Curry–Howard il **tipo** di un termine è l'**enunciato** che
quel termine dimostra. `#check` è quindi, al tempo stesso, «di che tipo è
questo dato?» e «che cosa dimostra questo termine?». -/

#check 3
#check (3 : ℤ)
#check Nat
#check Type            -- Type : Type 1  — la gerarchia di universi di L3
#check fun n : Nat => n + 1

-- I connettivi logici sono costruttori di tipi: guarda i loro tipi.
#check And             -- Prop → Prop → Prop
#check Or
#check False           -- il tipo vuoto ⊥ di L1
#check @Eq

-- Anche i *teoremi* sono termini, e il loro tipo è l'enunciato.
#check Nat.add_comm
#check @Nat.le_of_lt

/-! ## 2. `#eval` — calcolare

`#eval` esegue. Funziona sui dati, non sulle `Prop`: una proposizione non
si «esegue» (non ha contenuto computazionale osservabile in Lean 4). -/

#eval 2 + 2
#eval (List.range 10).map (· ^ 2)
#eval "Bardonecchia".length

-- Prova a togliere il commento alla riga seguente: perché fallisce?
-- #eval (2 + 2 = 4)

/-! ## 3. `#print` e `#print axioms`

`#print` mostra la definizione; `#print axioms` mostra su quali **assiomi**
poggia un teorema. Quest'ultimo è lo strumento con cui, nel Foglio 1,
misureremo quanto una dimostrazione è costruttiva (cfr. L1: BHK, LEM). -/

#print And
#print Iff
#print Nat

#print axioms Nat.add_comm   -- nessun assioma: dimostrazione costruttiva

/-! ## 4. Anatomia di una dimostrazione

`theorem nome (ipotesi) : enunciato := dimostrazione`

`example` è come `theorem` ma senza nome (non riutilizzabile dopo).
La dimostrazione può essere scritta in due stili equivalenti. -/

-- TERM MODE: si scrive direttamente il λ-termine. È letteralmente
-- l'oggetto di cui parla Curry–Howard.
theorem trans_term (A B C : Prop) (h1 : A → B) (h2 : B → C) : A → C :=
  fun a => h2 (h1 a)

-- TACTIC MODE: `by` apre una sessione interattiva; le tattiche
-- *costruiscono* per noi lo stesso termine, un pezzo alla volta.
theorem trans_tac (A B C : Prop) (h1 : A → B) (h2 : B → C) : A → C := by
  intro a
  exact h2 (h1 a)

-- Prova a mettere il cursore fra `intro a` ed `exact ...`: l'Infoview
-- mostra il **goal** (sotto la riga `⊢`) e il **contesto** (sopra).
-- È esattamente il giudizio Γ ⊢ t : A di L1, scritto in verticale.

-- E i due termini sono lo stesso termine:
example : trans_term = trans_tac := rfl

/-! ════════════════════════════════════════════════════════════════════
    ESERCIZI
    ════════════════════════════════════════════════════════════════════ -/

/-! ### Esercizio 0.1 — La funzione identità polimorfa

Scrivi il termine per l'identità polimorfa (l'abitante canonico di
`∀ X, X → X`, cioè `∀X.X→X` di System F, L2). -/

def identita : ∀ X : Type, X → X :=
  sorry

-- Una volta risolto, questi devono funzionare:
-- #eval identita Nat 42
-- #eval identita String "ciao"

/-! ### Esercizio 0.2 — Lo stesso enunciato nei due stili

Dimostra `A → (B → A)` (il combinatore **K**) prima in term mode e poi in
tactic mode. Suggerimento: il termine è `fun a => fun _ => a`. -/

theorem k_term (A B : Prop) : A → (B → A) :=
  sorry

theorem k_tac (A B : Prop) : A → (B → A) := by
  sorry

/-! ### Esercizio 0.3 — Uguaglianze per calcolo

Alcune uguaglianze valgono *per definizione* (uguaglianza giudizionale di
L3): le chiude `rfl`. Altre richiedono un minimo di calcolo: prova
`decide` o `norm_num`. Sostituisci ogni `sorry` con la tattica giusta. -/

example : 2 + 2 = 4 := by sorry

example : (List.range 4).length = 4 := by sorry

example : 12345 * 6789 = 83810205 := by sorry

/-! ### Esercizio 0.4 — Definire e calcolare

Definisci la funzione che raddoppia un naturale, poi verificala con
`#eval` e dimostra che raddoppia davvero. -/

def doppio (n : Nat) : Nat :=
  sorry

-- #eval doppio 21          -- deve dare 42
-- example : doppio 21 = 42 := by rfl

/-! ### Esercizio 0.5 — Leggere un tipo

Senza compilare, indovina il tipo di ciascuna espressione; poi verifica
con `#check`. (Non c'è nulla da riempire: è un esercizio per gli occhi.) -/

#check fun (f : Nat → Nat) (n : Nat) => f (f n)
#check @List.map
#check @Exists
#check fun (A : Prop) (h : A) => h

end Foglio0
