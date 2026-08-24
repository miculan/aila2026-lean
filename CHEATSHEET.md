# Cheatsheet — Lean 4 per l'AILA 2026

Riferimento rapido per i laboratori L4 e L5. Ogni tattica è affiancata dalla
regola logica che implementa: è il modo migliore per non impararle a memoria.

---

## 1. Curry–Howard in una tabella

| Logica intuizionista | Teoria dei tipi | Lean |
|---|---|---|
| proposizione `A` | tipo `A` | `A : Prop` |
| dimostrazione di `A` | termine di tipo `A` | `h : A` |
| `A → B` | funzione `A → B` | `A → B` |
| `A ∧ B` | prodotto `A × B` | `A ∧ B`, coppia `⟨ha, hb⟩` |
| `A ∨ B` | somma `A ⊕ B` | `A ∨ B`, `Or.inl` / `Or.inr` |
| `⊥` | tipo vuoto | `False` |
| `⊤` | tipo unitario | `True`, `trivial` |
| `¬A` | `A → ⊥` | `¬A`, cioè `A → False` |
| `∀x:A. P x` | Π-tipo `Π(x:A). P x` | `∀ x : A, P x` |
| `∃x:A. P x` | Σ-tipo `Σ(x:A). P x` | `∃ x : A, P x`, `⟨a, ha⟩` |
| `a = b` | tipo identità `Id_A(a,b)` | `a = b`, `rfl` |
| normalizzazione | riduzione β | `simp only []`, `rfl`, `decide` |

---

## 2. Le tattiche, per regola logica

### Introduzione (costruisco una dimostrazione)

| Tattica | Regola | Note |
|---|---|---|
| `intro h` | →-I, ∀-I | la λ-astrazione; `intro a b c` per più ipotesi |
| `exact e` | assioma | chiude il goal con il termine `e` |
| `constructor` | ∧-I, ↔-I | genera un goal per componente |
| `exact ⟨ha, hb⟩` | ∧-I | notazione anonima del costruttore |
| `left` / `right` | ∨-I | sceglie il disgiunto |
| `use a` | ∃-I | fornisce il testimone |
| `refine ?_ ` | parziale | come `exact` ma con buchi `?_` da riempire dopo |
| `rfl` | =-I | uguaglianza definizionale |
| `trivial` | ⊤-I | chiude i goal banali |

### Eliminazione (uso una dimostrazione che ho)

| Tattica | Regola | Note |
|---|---|---|
| `apply f` | →-E | ragionamento all'indietro: lascia le premesse come goal |
| `exact f a` | →-E | ragionamento in avanti |
| `obtain ⟨a, b⟩ := h` | ∧-E, ∃-E | smonta congiunzioni ed esistenziali |
| `rcases h with h₁ \| h₂` | ∨-E | analisi per casi |
| `rintro (h₁ \| h₂)` | →-I + ∨-E | `intro` + `rcases` in un colpo |
| `cases h` | eliminatore | forma generale |
| `induction n with ...` | eliminatore | l'induzione **è** l'eliminatore (L3) |
| `exact absurd a na` | ⊥-E | da `A` e `¬A` segue tutto |
| `exact h.elim` | ⊥-E | se `h : False` |
| `specialize h a` | ∀-E | istanzia un'ipotesi universale |

### Riscrittura ed uguaglianza

| Tattica | Effetto |
|---|---|
| `rw [h]` | riscrive con `h : a = b` da sinistra a destra |
| `rw [← h]` | …nella direzione opposta |
| `rw [h] at h'` | riscrive in un'ipotesi anziché nel goal |
| `subst h` | elimina una variabile usando `h : x = e` |
| `simp` | riscrive fino a normalizzare, con i lemmi `@[simp]` |
| `simp [h, foo]` | idem, aggiungendo lemmi alla base |
| `simp at h` | semplifica un'ipotesi |
| `simp only [h]` | usa **solo** i lemmi indicati (più prevedibile) |
| `calc` | catena di uguaglianze/disuguaglianze giustificate |

Sintassi di `calc`:

```lean
calc a = b   := by rw [h₁]
  _    = c   := h₂
  _    ≤ d   := by linarith
```

### Classico (attenzione: non costruttivo)

| Tattica | Note |
|---|---|
| `by_contra h` | assume `¬goal`, cerca `False` |
| `push_neg at h` | spinge le negazioni dentro (`¬∀` ⇒ `∃¬`) |
| `rcases Classical.em A with hA \| hnA` | terzo escluso esplicito |
| `by_cases h : A` | come sopra, più comodo |
| `#print axioms nome` | **verifica** se un teorema dipende da `Classical.choice` |

---

## 3. Automazione

| Tattica | Dominio |
|---|---|
| `rfl` | uguaglianza per calcolo |
| `decide` | proposizioni decidibili su domini finiti/concreti |
| `norm_num` | calcolo numerico |
| `ring` | identità in anelli e semianelli commutativi |
| `field_simp` | pulisce le divisioni, poi di solito `ring` |
| `linarith` | conseguenze lineari delle ipotesi in un ordine |
| `nlinarith` | idem, con prodotti (euristico) |
| `positivity` | `0 < e`, `0 ≤ e`, `e ≠ 0` |
| `omega` | aritmetica lineare su ℕ e ℤ — decidibile, completo |
| `gcongr` | disuguaglianze «congruenti» pezzo per pezzo |
| `group` / `abel` / `noncomm_ring` | normalizzazione in strutture algebriche |
| `aesop` | ricerca automatica generica |
| `tauto` | tautologie proposizionali (anche classiche) |
| `exact?` / `apply?` | **cerca il lemma** in Mathlib |
| `hint` | prova un ventaglio di tattiche e riferisce quali funzionano |

> Non abusarne. `simp` che chiude un goal non insegna nulla su *perché* il goal
> è vero; nei Fogli 1–3 il punto è proprio costruire la dimostrazione a mano.

---

## 4. Interrogare l'ambiente

```lean
#check e            -- il tipo di e (= l'enunciato che e dimostra)
#check @f           -- con tutti gli argomenti impliciti espliciti
#eval e             -- calcola e
#print nome         -- la definizione
#print axioms nome  -- da quali assiomi dipende  ← lo strumento di L1
#synth Group ℤ      -- quale istanza di type class viene sintetizzata
example : T := by exact?   -- cerca una dimostrazione di T in Mathlib
```

---

## 5. Cercare in Mathlib

| Strumento | Quando |
|---|---|
| `exact?` | il goal è *esattamente* un lemma esistente |
| `apply?` | il goal è la conclusione di un lemma |
| `rw?` | cerchi una riscrittura utile |
| [Loogle](https://loogle.lean-lang.org) | conosci la **forma** dell'enunciato: `_ * _ = _ * _`, `Nat.Prime`, `⊢ Continuous _` |
| [LeanSearch](https://leansearch.net) | sai dirlo in inglese: «sum of first n naturals» |
| [Moogle](https://www.moogle.ai) | idem, ricerca semantica |
| [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) | navigazione per modulo |

**Convenzioni di nome** (impararle vale quanto un motore di ricerca):
il nome descrive l'enunciato da sinistra a destra, in `snake_case`, con
`_of_` per le ipotesi.

- `add_comm` : `a + b = b + a`
- `mul_le_mul_left` : moltiplicare a sinistra preserva `≤`
- `Nat.succ_le_of_lt` : da `<` segue `succ ≤`
- `le_antisymm` : `a ≤ b → b ≤ a → a = b`
- `not_forall` : `¬∀ ↔ ∃¬`

---

## 6. Simboli Unicode e come digitarli

In VSCode si scrive la sequenza e si preme <kbd>Tab</kbd> (o spazio).

| Simbolo | Sequenza | Simbolo | Sequenza |
|---|---|---|---|
| `→` | `\to` `\r` | `∀` | `\forall` `\all` |
| `←` | `\l` | `∃` | `\exists` `\ex` |
| `↔` | `\iff` | `¬` | `\not` `\n` |
| `∧` | `\and` | `∨` | `\or` |
| `λ` | `\lam` | `Π` | `\Pi` |
| `⟨⟩` | `\<` `\>` | `·` | `\.` |
| `ℕ ℤ ℚ ℝ ℂ` | `\N \Z \Q \R \C` | `∅` | `\empty` |
| `≤ ≥ ≠` | `\le \ge \ne` | `∈` | `\in` |
| `⁻¹` | `\inv` | `∑` | `\sum` |
| `≡` | `\equiv` | `∘` | `\comp` |
| `α β γ` | `\a \b \g` | `⊢` | `\vdash` |

Se non ricordi la sequenza: posiziona il cursore sul simbolo, l'Infoview la
mostra in fondo.

---

## 7. Errori frequenti al primo laboratorio

| Sintomo | Causa | Rimedio |
|---|---|---|
| «unknown identifier» su un simbolo unicode | copiato male, o carattere sbagliato (`→` vs `⟶`) | ridigitalo con `\to` |
| il file non viene controllato | l'editor non ha trovato il progetto | apri **la cartella radice** `aila2026-lean/` (quella con `lakefile.toml`), non il singolo file né la sottocartella |
| «unsolved goals» a fine dimostrazione | manca un caso | leggi l'Infoview: mostra i goal residui |
| `rw` non fa nulla | il termine nel goal non è *sintatticamente* uguale | usa `simp only [...]`, o `show` per riscrivere il goal |
| `rfl` fallisce ma «è ovvio» | uguaglianza proposizionale, non definizionale | serve `induction` o un lemma (cfr. Foglio 2) |
| tutto è rosso e lento | Mathlib non compilato | `lake exe cache get` |
| «declaration uses sorry» | è solo un promemoria | va bene finché stai lavorando |

---

## 8. Bibliografia minima

- *Theorem Proving in Lean 4* — <https://lean-lang.org/theorem_proving_in_lean4/>
- Avigad, Massot, *Mathematics in Lean* — <https://leanprover-community.github.io/mathematics_in_lean/>
- *The Mechanics of Proof* (Macbeth) — <https://hrmacbeth.github.io/math2001/>
- Natural Number Game — <https://adam.math.hhu.de/> (un'ora ben spesa prima della scuola)
- Zulip della comunità — <https://leanprover.zulipchat.com>
