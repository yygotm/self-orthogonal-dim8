# Three nonexistence proofs for binary self-orthogonal codes of dimension 8

This repository contains proofs, with checking scripts, of the nonexistence of three binary self-orthogonal (SO) codes of dimension 8. They are referred to in footnote 12 of S. Kurz, *Optimal self-orthogonal binary linear codes*, arXiv:2610.39870v1 (https://arxiv.org/abs/2610.39870v1). Lemma numbers below are those of arXiv:2610.39870v1 (submitted on 29 October 2026; its lemma numbers are the same as in Kurz's draft dated 29 October 2026).

| Code | Claim | Place in Kurz's paper | Folder |
|---|---|---|---|
| SO [97,8,46]_2 | no binary SO [97,8,≥46] code exists | one case of Lemma 21 | `proofs/97/` |
| SO [90,8,42]_2 | no binary SO [90,8,≥42] code exists | one case of Lemma 21 | `proofs/90/` |
| SO [121,8,58]_2 | no binary SO [121,8,≥58] code exists, assuming Lemma 20 | Lemma 22 | `proofs/121/` |

## What "computer-free" means here

- The proofs do **not** use exhaustive computer enumerations of codes.
- They **do** use finite exact computations: rational (Farkas) certificates for linear programs, and complete lists of candidate integer weight distributions (20 candidates for [90]; computer-generated lists of about 318,000 rows for [121]).
- The proof for [121] **assumes Lemma 20** of the paper (nonexistence of SO [120,8,58]_2). Whether the dimension-7 bounds used there depend on computer enumeration has not been checked.

## Status

- The proofs were found with AI tools.
- They have been checked by independent AI reviews and by exact computer checks (the scripts in this repository).
- **They have not yet been checked by a human expert.**
- The author is not a specialist in coding theory.

## Contents

```
proofs/97/               PROOF.en.md (English), PROOF.ja.md (Japanese original), verify_final.py and its input files
proofs/90/               same
proofs/121/              PROOF.en.md, PROOF.ja.md, the checking scripts, data.tar.xz (input files)
formalization/griesmer/  Lean 4 proof of the Griesmer bound and of six dimension-8 SO upper bounds
formalization/97/        Lean 4 proof of the [97] result, with Ward's divisibility theorem as an explicit hypothesis
MANIFEST.sha256          SHA-256 of every file
```

The English texts translate the Japanese originals, keeping the mathematical content and the numerical data. Two kinds of change were made in the English texts: references to Kurz's draft use the numbering of 29 October (see below), and the file-name placeholder `<row>` is written in English. Line *i* of each Japanese original corresponds to line *i*+6 of the English text.

The full search pipeline that produced the certificates is not included; only the files needed to check them are. For [121], five historical generation-side source files (`bmodels.py`, `dscreen.py`, `exact_lp.py`, `models.py`, `split_models.py`) are kept solely for provenance-hash checks; the verification scripts do not import them.

`data.tar.xz` for [121] contains one historical Japanese proof draft, `subcode-proof-before-1300.md`. It is there only because the checker compares its SHA-256 with a recorded provenance hash. The checker does not read any mathematical content from it, and it is an earlier, incomplete version of the argument. The proofs to read are `PROOF.en.md` and `PROOF.ja.md`.

## Numbering

The Japanese originals were written against Kurz's draft dated 26 October 2026 and keep its numbering. The English texts use the numbering of the draft dated 29 October 2026, which is also the numbering of arXiv:2610.39870v1:

| Draft of 26 October | Draft of 29 October (arXiv:2610.39870v1) |
|---|---|
| Lemma 19 | Lemma 20 |
| Lemma 20 | Lemma 21 |
| Lemma 21 | Lemma 22 |

Bibliographic labels such as `[65]` inside the proof texts refer to the draft of 26 October.

## Reproducing the checks

Requirements: Python 3.10 or later, standard library only. Run the commands from the top folder of the repository.

```console
python -X utf8 -B proofs/97/verify_final.py
python -X utf8 -B proofs/90/verify_final.py
```

For [121], first unpack the input files next to the scripts (about 16,400 files, 1.07 GB):

```console
tar -xJf proofs/121/data.tar.xz -C proofs/121
python -X utf8 -B proofs/121/verify_final.py
```

| Proof | Expected result | Time on the author's machine |
|---|---|---|
| 97 | exit code 0, last line starting `CHECK_OK` | about 6 s |
| 90 | exit code 0, a line starting `VERIFIED` | about 1 s |
| 121 | exit code 0, last line starting `PASS FINAL NONEXISTENCE CERTIFICATE CHAIN` | 2 to 5 min |

Each script also accepts `--negative-control`, which feeds it a deliberately broken certificate; the expected result is exit code 1.

Do not run the scripts with `python -O`, which disables the assertions.

The scripts check the finite computations. They do not check the mathematical arguments in the proof texts.

## Lean

Lean 4 `v4.34.1`, Mathlib `v4.34.1`. Requirements: [elan](https://github.com/leanprover/elan) and git. `lake exe cache get` downloads the prebuilt Mathlib files.

```console
cd formalization/97
lake exe cache get
lake build
```

For `formalization/griesmer`, start from the top folder, run `cd formalization/griesmer`, and then the same two `lake` commands.

- `formalization/97`: the main theorem `no_so_97_8_46` takes Ward's divisibility theorem for binary codes meeting the Griesmer bound as an explicit hypothesis `WardBinary`. No `sorry`, no `native_decide`, and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
- `formalization/griesmer`: the Griesmer bound and the nonexistence of SO [137,8,66], [183,8,90], [200,8,98], [207,8,102], [215,8,106] and [231,8,114]. No hypotheses.
- There is no Lean proof for [90] or [121].

## Role of AI

The proofs, the checking scripts and the Lean code were written by OpenAI GPT models (via Codex). Anthropic Claude coordinated the work, extracted the files needed for reproduction, and ran independent reviews and checks. The author chose the problems, directed the work and decided what to publish.

## License

MIT. See `LICENSE`.

Hirotaka Shimizu
