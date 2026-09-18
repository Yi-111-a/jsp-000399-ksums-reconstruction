# JSP-000399 — Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements?

- **id:** JSP-000399
- **title:** Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements?
- **area:** Analysis / Additive combinatorics
- **status:** Solved
- **Lean:** No (JSP screening)
- **Eligible / Claim:** No / Unavailable
- **role:** Trial order #3 (good parallel track)

## Statement

Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements?

## Catalog / Erdős source

- Catalog anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000399
- Erdős Problems #494 (PROVED): https://www.erdosproblems.com/494
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [SeSt58] Selfridge–Straus — Pacific J. Math. (1958). PDF: https://msp.org/pjm/1958/8-4/pjm-v8-n4-p17-s.pdf
- [GFS62] Gordon–Fraenkel–Straus — Pacific J. Math. (1962). PDF: https://msp.org/pjm/1962/12-1/pjm-v12-n1-p17-s.pdf
- [Er61] Erdős, Some unsolved problems (1961): https://users.renyi.hu/~p_erdos/1961-22.pdf
- Survey / follow-ups: Fomin arXiv https://arxiv.org/abs/1709.06046 ; counterexample (12,4): https://arxiv.org/abs/1702.04166
- Guy C5 (catalog cites Gu04)

## Lean / related libraries (important)

- **Statement skeleton with many `sorry` (NOT JSP-eligible):** https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/494.lean
- Fork pointer inside that file: https://github.com/hjyuh/formal-conjectures
- Other traces: `plby/lean-proofs` (Erdos494), `Mnehmos/llm-driven-proof-search` (erdos-494) — do **not** assume they are sorry-free.
- Warning: FC’s `k_eq_3_card_gt_6` was reviewed as missing exception cardinalities 27/486. Harness statements must follow **SeSt58** (and catalog), not an over-wide FC lemma.

Suggested parallel path: align with `ErdosProblems/494.lean`, clear sorry on narrower variants (e.g. k=2 uniqueness/counterexamples) before full GFS asymptotics.

## Success criteria

- `lake build` succeeds
- `sorry` and `admit` counts are zero
- no new axioms
- final commit SHA and build evidence recorded
- statement scope matches SeSt58 / catalog (no silent strengthenings)

## Notes

A sorry-heavy skeleton is a starting point only. Partial formalizations are not submission-eligible under Justin Sun Prize rules.
