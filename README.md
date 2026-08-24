# Esercizi Lean — Scuola Estiva di Logica AILA 2026

Materiale per i laboratori delle **Lezioni 4 e 5** del corso *Teoria della
dimostrazione. Teoria dei tipi, Proof Assistants e AI*.

Scuola Estiva di Logica AILA 2026 — Villaggio Olimpico di Bardonecchia,
31 agosto – 5 settembre 2026. Marino Miculan (Università di Udine).

**NB: versione preliminare, può cambiare in corso d'opera.**

---

## ⚠️ Da fare PRIMA di arrivare a Bardonecchia

Il primo scaricamento di Mathlib è di **alcuni gigabyte**. 
**Fallo a casa, con una connessione decente, e verifica che funzioni.**

---

## Installazione

### 1. `elan` (il gestore di versioni di Lean)

**macOS / Linux**

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

**Windows (PowerShell)**

```powershell
curl -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -f elan-init.ps1
```

Riapri il terminale e verifica:

```bash
elan --version
lake --version
```

### 2. VSCode + estensione Lean 4

1. Installa [Visual Studio Code](https://code.visualstudio.com/).
2. Estensioni → cerca **`lean4`** (editore: *leanprover*) → Install.

> Va bene anche Emacs con `lean4-mode`, o Neovim (ma in aula useremo VSCode).

### 3. Questo progetto

```bash
git clone https://github.com/miculan/aila2026-lean.git
cd aila2026-lean
lake exe cache get      # scarica Mathlib già compilata: alcuni GB, molti minuti
lake build              # compila i fogli: qualche minuto la prima volta
```

`lake exe cache get` è **il passo che non si può fare in loco**. Se lo salti,
Lean ricompilerà Mathlib da sorgente sulla tua macchina: sono ore.

### 4. Verifica

```bash
lake env lean Esercizi/Foglio0.lean
```

Deve stampare solo dei warning `declaration uses 'sorry'` (sono gli esercizi da
fare) e nessun errore.

Poi apri **la cartella** del progetto — `aila2026-lean/`, quella che
contiene `lakefile.toml` — in VSCode:

```bash
code .
```

e apri `Esercizi/Foglio0.lean`. In alto a destra compare l'icona `∀`: cliccala
per aprire il pannello **Lean Infoview**. Mettendo il cursore dentro una
dimostrazione, l'Infoview mostra il goal corrente. Se lo vedi, sei pronto.

> **Errore tipico**: aprire il *file* invece della *cartella*, oppure aprire la
> sottocartella `Esercizi/` invece della radice `aila2026-lean/`. In entrambi i
> casi l'estensione non trova `lakefile.toml`, non carica Mathlib e sembra
> tutto rotto.

---

## Piano B: niente installazione

Se proprio l'installazione non riesce:

| Opzione | Indirizzo | Limiti |
|---|---|---|
| **Lean 4 Web** | <https://live.lean-lang.org> | ha Mathlib, ma è lento e non salva il lavoro |
| **Natural Number Game** | <https://adam.math.hhu.de> | ottimo per allenarsi sui Fogli 0–2, ambiente separato |
| **GitHub Codespaces** | [dal repo](https://github.com/miculan/aila2026-lean), «Code → Codespaces» | serve un account GitHub; consuma ore gratuite |

Per i Fogli 0–3 il Lean 4 Web basta: incolli il contenuto del file e lavori lì.

---

## Contenuto

| File | Lezione | Argomento |
|---|---|---|
| `Esercizi/Foglio0.lean` | L4 blocco 1 | Riscaldamento: `#check`, `#eval`, term vs tactic mode |
| `Esercizi/Foglio1.lean` | L4 blocco 2 | Logica proposizionale come esercizio di Curry–Howard |
| `Esercizi/Foglio2.lean` | L4 blocco 3 | Tipi induttivi, induzione, uguaglianza def. vs prop. |
| `Esercizi/Foglio3.lean` | L5 blocco 1 | Monoidi e gruppi da zero, con `calc` |
| `Esercizi/Foglio4.lean` | L5 blocco 2 | Mathlib: automazione, ricerca dei lemmi, formalizzare |
| `Soluzioni/Foglio*.lean` | — | tutte le soluzioni, commentate |
| `CHEATSHEET.md` | — | tattiche, notazione, ricerca in Mathlib, errori comuni |

Gli esercizi da svolgere sono 76 in tutto: 10 nel Foglio 0, 15 nel Foglio 1,
11 nel Foglio 2, 15 nel Foglio 3, 25 nel Foglio 4.

I fogli sono pensati per **due sessioni da due ore**, ma sono più lunghi di
quanto si riesca a fare in aula: la coda di ciascun foglio è materiale per chi
va veloce e per chi vuole continuare in settimana.

**Non guardare le soluzioni** prima di esserti bloccato per qualche minuto.
Il valore del laboratorio sta tutto nel momento in cui l'Infoview mostra un
goal che non sai chiudere.

---

## Come si lavora su un foglio

Ogni esercizio è un enunciato la cui dimostrazione è `sorry`:

```lean
theorem comb_K : A → B → A := by
  sorry
```

`sorry` è l'ammissione «lo do per buono senza dimostrarlo»: chiude qualunque
goal e fa comparire un warning giallo. Sostituiscilo con la dimostrazione.

Quando il file non ha più warning, il foglio è finito. Per controllare da riga
di comando:

```bash
lake build                                   # tutto (esercizi + soluzioni)
lake build Esercizi                          # solo i fogli di esercizi
lake build Soluzioni                         # solo le soluzioni
lake env lean Esercizi/Foglio1.lean          # un singolo foglio
grep -c sorry Esercizi/Foglio1.lean          # quanti ne restano
```

## Versioni

Il progetto è agganciato a **Lean v4.33.0** e **Mathlib v4.33.0**
(`lean-toolchain` e `lakefile.toml`). Tutti i fogli e tutte le soluzioni sono
stati compilati con successo su questa combinazione: le soluzioni non
contengono alcun `sorry`, i fogli contengono solo i `sorry` degli esercizi.

Per aggiornare a una versione più recente di Mathlib prima della scuola:

```bash
# allinea lean-toolchain a quello di Mathlib, poi:
lake update mathlib
lake exe cache get
lake build
```

Dopo un aggiornamento **ricompila le soluzioni**: qualche nome di lemma di
Mathlib può essere cambiato.

---

## Riferimenti

- *Theorem Proving in Lean 4* — <https://lean-lang.org/theorem_proving_in_lean4/>
- Avigad, Massot, *Mathematics in Lean* — <https://leanprover-community.github.io/mathematics_in_lean/>
- Documentazione Mathlib — <https://leanprover-community.github.io/mathlib4_docs/>
- Loogle (ricerca per forma) — <https://loogle.lean-lang.org>
- LeanSearch (ricerca in inglese) — <https://leansearch.net>
- Zulip della comunità — <https://leanprover.zulipchat.com>
