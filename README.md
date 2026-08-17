# PRINCIPIA PHYSICA — bounded pilot

**Compositional Foundations of Finite-Dimensional Classical Mechanics**

This repository is a **bounded pilot run**, not a research programme and not a finished
theory. It was chartered to answer one question inside one scope:

> Can finite-dimensional Hamiltonian mechanics be represented as an empirically interpreted
> compositional theory object, without conflating mathematical equivalence with physical
> equivalence?

The founding thesis under investigation — *physics is the study of empirically realized
compositional mathematical structures* — is **tested, not assumed**. The pilot's own conclusion
is that the thesis **as stated is not a falsifiable physical hypothesis**; what survives is an
explicit empirical contract whose compositional clauses can fail.

---

## Website

A static, self-contained site presenting the whole bundle:

- [`website/index.html`](website/index.html) — one HTML file, one stylesheet, no JavaScript,
  no external fonts, no analytics, no network requests.
- [`website/styles.css`](website/styles.css)
- [`website/og.png`](website/og.png) — 1200×630 social card drawn for this bundle.

**Production URL — <https://principia-physica-pilot.vercel.app> —** deployed to the existing Vercel
project `principia-physica-pilot` and read back from that origin before this line was written.
The bundle contains no machine-specific absolute paths.

## The four papers

| # | Paper | Pages | PDF | LaTeX source |
|---|-------|-------|-----|--------------|
| I | Compositional Systems in Finite-Dimensional Classical Mechanics | 9 | [PDF](website/papers/pdf/compositional-systems.pdf) | [.tex](website/papers/latex/compositional-systems.tex) |
| II | Hamiltonian Reconstruction as a Physical Theory Object | 9 | [PDF](website/papers/pdf/hamiltonian-reconstruction.pdf) | [.tex](website/papers/latex/hamiltonian-reconstruction.tex) |
| III | Empirical Realization, Observational Equivalence, and the Limits of Finite-Dimensional Classical Models | 10 | [PDF](website/papers/pdf/empirical-limits.pdf) | [.tex](website/papers/latex/empirical-limits.tex) |
| — | Synthesis, Obstructions, and an Empirical Contract | 7 | [PDF](website/papers/pdf/synthesis.pdf) | [.tex](website/papers/latex/synthesis.tex) |

The same files are also kept at their working locations, [`papers/pdf/`](papers/pdf) and
[`papers/latex/`](papers/latex); the copies under `website/` are byte-identical (see
*Reproducible local inspection* below).

Each paper is self-contained arXiv-style LaTeX with no external bibliography file; references are
embedded in each paper. Every claim carrying epistemic status is typed by one of **twelve epistemic
labels** required by the pilot contract: Definition, Axiom, Assumption, Conjecture, Lemma,
Proposition, Theorem, Corollary, Interpretation, Empirical statement, Established physical result,
and New result claimed by this work.

Two further environments share the same counter and are deliberately *not* among the twelve:
`Counterexample` (10 occurrences), which exhibits a witness against a claim rather than asserting a
new one, and `Remark` (7 occurrences), which carries no independent claim. Counts across the four
published sources are 14 / 5 / 14 / 4 / 5 / 17 / 10 / 7 / 6 / 7 / 13 / 11 in the order listed above,
totalling 113 labelled claim environments.

## Formal companions — what they are, and what they are not

The pilot ships two small formal artifacts. **They are representative companions to a single
argument each. They are not a formalization of the papers, and they are not machine-checked
support for the founding thesis or for any complete result in the series.**

- [`website/formal/lean/Proofs.lean`](website/formal/lean/Proofs.lean) (89 lines, Lean 4.33.0) —
  formalizes the elementary metric content of one theorem: closeness at a tolerance is reflexive
  and symmetric, is transitive *only* under an explicit gap hypothesis, and fails transitivity on
  a concrete arithmetic witness (gravitational parameters 9.8 / 9.9 / 10.0 m s⁻² at a 0.2 m
  tolerance). The transitivity-under-a-gap result is a restriction under an added hypothesis, not a
  converse of the failure. It deliberately does **not** encode empirical realization as a theorem.
- [`website/formal/haskell/Core.hs`](website/formal/haskell/Core.hs) (193 lines, GHC 9.14.1) —
  an executable vocabulary whose types keep mathematical structure, empirical interpretation,
  and equivalence evidence separate. It does **not** prove smoothness, symplecticity, or
  Hamilton's equations; those remain stated obligations on the values a user supplies.

## Review evidence

All review records are published unedited, including the two that did not accept.

| Record | Verdict | What it says |
|--------|---------|--------------|
| [`reviews/topic-series-review.json`](reviews/topic-series-review.json) | `ACCEPT` | No blocking findings, no required changes; three supported claim assessments; seven counterexamples catalogued. |
| [`reviews/synthesis-review.json`](reviews/synthesis-review.json) | `REJECT` | Three blocking findings at the time of review: the synthesis paper, the Lean draft, and the Haskell draft were unwritten after a native-team execution failure. Retained as-is. |
| [`reviews/website-self-review.json`](reviews/website-self-review.json) | `changes-required` | First-pass findings on this website from the parent build plus two independent reviewers, before repair: one blocker, three major, six minor. |
| [`website/reviews/website-review.json`](website/reviews/website-review.json) | accepted | The re-run website review after every finding was repaired. |

The rejecting synthesis review was **not** edited or superseded. It is published next to the
recovery receipt that answers it.

**One caveat on reading the topic-series review.** It was carried out against the pre-acceptance
drafts, and the item numbers it cites are the drafts' numbering. The accepted papers published here
were renumbered, so the reviewed results appear under different numbers — for example the review's
"Theorem 4.3 / Proposition 4.2" on the absence of Cartesian structure is Theorem 4.2 (*No diagonal*)
and Proposition 4.1 in the published Paper I, its "Counterexample 3.7" is Counterexample 3.3
(*Composition that is not a submanifold*), and its "Theorem 3.8 / Corollary 3.9" on the tolerance
relation is Theorem 3.5 / Corollary 3.6 in the published Paper III. The substance the review
assessed is present in the published papers; only the numbering moved. The review is published as
written rather than renumbered after the fact.

## Verification receipts

Each receipt records a tool, the exact command, and the observed exit status for a check that
actually ran. These are records of mechanical checks — **not** claims about the correctness of
the physics.

| Receipt | Records |
|---------|---------|
| [`receipts/latex.json`](receipts/latex.json) | `latexmk 4.88` / pdfTeX 1.40.29 builds, exit status 0 for all four papers; 9 + 9 + 10 + 7 pages via `pdfinfo`; SHA-256 of every `.tex` and `.pdf`. |
| [`receipts/formal.json`](receipts/formal.json) | Lean check exit 0 with zero `sorry`/`admit` matches; GHC compile exit 0 with zero warnings under `-Wall -Wextra -Werror`. |
| [`receipts/recovery.json`](receipts/recovery.json) | Three repair agents with non-overlapping ownership; zero unresolved compiler or verifier errors; bounded fix limit respected. |
| [`receipts/website.json`](receipts/website.json) | The tools and checks used to build and validate this website, with their observed exit statuses. |

Copies of all four receipts are served with the site under
[`website/receipts/`](website/receipts).

## Limitations

Carried forward from the synthesis paper rather than dropped in presentation:

- **No novel empirical prediction** is produced anywhere in this pilot.
- No total category of canonical relations is constructed; composition remains **partial**.
- No universal interconnection operation is given.
- No uniqueness theorem for reconstruction is proved — exact data do not in general identify a
  unique Hamiltonian.
- Long-range forces, dissipation, singular constraints, and incomplete flows defeat common
  idealizations used in the scope.
- Eleven claims across the four papers are labelled *new*. Of these, the synthesis records that
  literature priority for the exact formulations of its two headline claims is less certain than
  their correctness.
- The Lean and Haskell files are representative companions to one argument each (see above).
- Scope is finite-dimensional classical mechanics. Field theory, infinite-dimensional analysis,
  general relativity, quantum mechanics, quantum field theory, theory-space geometry, and new
  experimental claims appear **only as boundary tests**.

## Reproducible local inspection

All commands are run from the repository root. Nothing below needs network access, a secret, or
an absolute path.

**1. Read the site.**

```sh
python3 -m http.server 8000 --directory website
# then open http://localhost:8000/
```

Or open `website/index.html` directly in a browser — the site is static and needs no build step.

**2. Confirm the published papers and formal artifacts match the receipts.**

```sh
shasum -a 256 website/papers/latex/*.tex website/papers/pdf/*.pdf \
              website/formal/lean/Proofs.lean website/formal/haskell/Core.hs
jq -r '.papers[] | "\(.tex_sha256)  \(.name).tex", "\(.pdf_sha256)  \(.name).pdf"' receipts/latex.json
jq -r '.lean.sha256, .haskell.sha256' receipts/formal.json
```

**3. Confirm the site copies are byte-identical to the working copies.**

```sh
diff -r papers/latex website/papers/latex
for f in papers/pdf/*.pdf; do cmp "$f" "website/papers/pdf/$(basename "$f")"; done
cmp formal/lean/Proofs.lean website/formal/lean/Proofs.lean
cmp formal/haskell/Core.hs  website/formal/haskell/Core.hs
```

Silence means identical.

**4. Check the page counts claimed by the site.**

```sh
for f in website/papers/pdf/*.pdf; do printf '%s ' "$f"; pdfinfo "$f" | awk '/^Pages:/{print $2}'; done
```

**5. Re-run the website validation.**

```sh
npx --yes html-validate website/index.html          # HTML5 conformance
npx --yes csstree-validator website/styles.css      # CSS syntax and value grammar
sips -g pixelWidth -g pixelHeight website/og.png    # must be 1200 x 630
```

**6. Count the epistemic labels the site reports.**

```sh
for l in definition axiom assumption conjecture lemma proposition theorem corollary \
         interpretation empirical established newresult; do
  printf '%-16s %s\n' "$l" "$(grep -ho "\\\\begin{$l}" papers/latex/*.tex | wc -l | tr -d ' ')"
done
```

**7. Re-verify the formal companions** (only if Lean 4 and GHC are installed locally):

```sh
lean formal/lean/Proofs.lean
grep -nE '\b(sorry|admit)\b' formal/lean/Proofs.lean   # expect no matches
ghc -fno-code -fforce-recomp -Wall -Wextra -Werror -Wcompat -Widentities \
    -Wincomplete-uni-patterns -Wincomplete-record-updates -Wpartial-fields \
    formal/haskell/Core.hs
```

That is the exact flag set recorded in `receipts/formal.json`, not a reduced one.

---

## Repository layout

```
papers/latex/     four accepted LaTeX sources
papers/pdf/       four compiled PDFs
formal/lean/      representative Lean companion
formal/haskell/   representative Haskell companion
reviews/          review records, including the rejecting one
receipts/         verification receipts
pilot/            charter, epistemic contract, and pilot context
website/          the static site, with its own copy of every artifact it links
```

## Honesty note

Claims on the website are drawn from the papers, reviews, and receipts in this repository.
Where a claim is contested, unproved, or conjectural, the papers say so at the point of use, and
neither the website nor this README upgrades it. Mathematical admissibility is never identified
with physical realization.
