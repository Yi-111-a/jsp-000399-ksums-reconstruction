# ACCEPTANCE — JSP-000399 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000399
- Erdős Problems #494: https://www.erdosproblems.com/494
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

Catalog wording:

> Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements?

(Equivalent PROBLEM.md title uses “uniquely recovered” / “prescribed number of distinct elements”.)

The accepted answer is the **full uniqueness/reconstruction (UR) characterization** of Selfridge–Straus (SeSt58) and Gordon–Fraenkel–Straus (GFS62) for Erdős #494: for each \(k\), for which cardinalities \(n\) every \(n\)-element set of numbers is uniquely recoverable from its \(k\)-sum multiset (with the known exceptional families, e.g. powers of two for \(k=2\), and the finite exceptional sets for \(k\ge 3\)).

Counterexamples alone, duality lemmas, or partial positive cases are **not** the full original statement.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `UR_characterization` | Full UR characterization matching SeSt58 / GFS62 / Erdős 494 (for each \(k\), the precise set of \(n\) for which `UR ℤ k n` holds, including all exceptional families). |

**Not sufficient for prize_ready:** `not_UR_two_four`, `not_UR_two_pow`, `not_UR_two_mul`, `UR_one`, `UR_pred_card`, Thue–Morse constructions, or other fragment lemmas.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.

Zero-sorry partial results are milestones to commit, **not** SUCCESS.
