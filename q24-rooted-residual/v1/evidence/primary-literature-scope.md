# Primary-literature scope audit: q24 rooted-residual graft

Private additive literature audit, 10 October 2026. No public release, priority claim, or external-review claim.

## Scope and exact target

This audit compares the frozen q24 rooted-residual statement in the two pinned internal reports below against primary literature on α/graceful vertex amalgamation and tree substitution. It is a targeted comparison, not an exhaustive search of all graph-labeling literature.

The exact internal claim is: for each `t ≥ 1`, let `K=23+24t`, `d₀=20+22t`, `d₁=21+22t`, and `M=2K`. Given a finite indexed graph `H` with `Q` edges, a conventional graceful labeling `g:V(H)→{0,…,Q}` that is injective, has edge differences exactly `1,…,Q`, and a selected actual root `r` with `g(r)=0`, identify `r` with the midpoint of a `2K`-edge path. For either named new arm and either depth `d₀` or `d₁`, the actual graft graph has a conventional graceful labeling with zero at that selected vertex. The four cases use separate witnesses. If the residual vertex labels are onto `{0,…,Q}`, the constructed labeling is also onto its full vertex band. This does not claim zero at old H vertices, tips, or every depth.

The q24 proof uses an α-labeled path whose midpoint is at boundary `A=K−1`, with the designated interior path labels equal to `0` and `M=2K`. For a target carrying `0`, it retains low labels, shifts path labels above `A` by `Q`, and labels H by `A+g`. For the `M` target it complements the whole output by `M+Q−x`. Path reversal handles the opposite arm. This is a positional consequence of the path certificate combined with a standard α/graceful splice.

## Closest primary result: α graph plus graceful graph

Christian Barrientos, “On the generation of alpha graphs,” *Journal of Algebra Combinatorics Discrete Structures and Applications* 9(2) (2022), 101–114, DOI [10.13069/jacodesmath.1111733](https://doi.org/10.13069/jacodesmath.1111733). Publisher record and article page: [JACODES article page](https://jacodesmath.com/index.php/jacodesmath/article/view/194); direct full-text PDF: [publisher PDF](https://www.jacodesmath.com/index.php/jacodesmath/article/download/194/149).

The article’s introduction (printed p. 103) defines vertex amalgamation and states that when `G₁,G₂` are α-labeled, a chain/amalgamation can be formed by identifying the zero-labeled vertex of `G₂` with the boundary-labeled vertex of `G₁`; it then states that replacing the second α input by merely a graceful graph gives a graceful chain graph. The same page describes the conventional amplification: for α-label boundary `λ`, add `d−1` to labels above `λ` to obtain the `d`-graceful labeling with shifted edge interval. This is the same interval-separation mechanism as shifting the path’s high side by `Q` (here `d−1=Q`).

**Comparison.** For connected residual `H`, the old theorem applies directly to the generic topology: take `G₁` to be the `2K`-edge path with its midpoint at boundary `A`, take `G₂=H` with `g(r)=0`, and identify those two vertices. It therefore subsumes the bare conclusion “the graft is graceful,” subject to the paper’s graph/chain conventions. The q24 report additionally supplies a particular all-`t` α-path certificate and reserves two named interior path positions at its extreme labels. Neither the cited introductory amalgamation statement nor the cited amplification description gives those positions or says that either designated new-arm vertex can be made zero. Thus the overlap is substantial at the composition-operation level; the cited statement does not itself subsume the target-position conclusion.

The source search index exposes the article text and its exact amalgamation passage, but the journal’s direct PDF endpoint timed out in this audit. I could read the indexed full-text excerpt and the publisher’s metadata (title, author, issue, pages, DOI, publication details), not independently inspect every page of the rendered PDF. I therefore do not make a claim about unsearched theorems elsewhere in the article. The passage itself speaks of a chain graph and the article’s graph conventions should be checked against the exact desired disconnected-residual scope before claiming literal subsumption for disconnected `H`; the internal theorem does allow any residual satisfying its conventional labeling hypotheses.

## Earlier tree amalgamation theorem

Huang, Kotzig, and Rosa, “Further results on tree labellings,” *Utilitas Mathematica* 21C (1982), 31–48. Bibliographic identity and pagination are corroborated by [Zhao (1989), references](https://nyaspubs.onlinelibrary.wiley.com/doi/pdf/10.1111/j.1749-6632.1989.tb16451.x) and other bibliographies. The 1982 paper’s full text was not located in an accessible primary copy during this audit.

A later primary article by Panpa et al., “Graceful Labeling of Spider Graphs With at Most Five Legs,” *Journal of Applied Mathematics* (2025), theorem 2.5, explicitly attributes to Huang et al. the following result: if `G` has an α-labeling with index `α` and a vertex `u` labeled `0` or `α`, and `H` has a graceful labeling with a vertex `v` labeled `0`, then identifying `u` and `v` gives a graceful graph. Its proof sketch is the same high-side shift and low-side matching operation. The accessible source gives theorem number and exact conditions, but the browser extract did not expose a stable printed page number; the theorem is in the paper’s preliminaries. The original 1982 theorem is stated for trees in the accessible secondary restatement of that result. Consequently, this source supports historical overlap for tree operands, but not the q24 theorem’s arbitrary finite residual graph as stated. Also, the q24 splice uses a path midpoint labeled at the α-boundary; it is not the cited `u`-labeled-0/α form verbatim unless an appropriate path labeling/reversal is separately shown.

A further relevant primary source is Mavronicolas and Michael, “A substitution theorem for graceful trees and its applications,” *Discrete Mathematics* 309(12) (2009), 3757–3766, DOI [10.1016/j.disc.2008.10.006](https://doi.org/10.1016/j.disc.2008.10.006). The publisher abstract states that it constructs larger graceful trees by combining smaller, not necessarily identical, graceful trees. The authors’ [full-text PDF](https://www.cs.ucy.ac.cy/~mavronic/pdf/GRACEFUL.pdf) timed out in this audit. Its abstract alone does not establish that it covers this exact midpoint splice, arbitrary cyclic/disconnected `H`, or prescribed interior zero locations. It is recorded as potentially related tree-substitution literature, not as a result shown to subsume the q24 claim.

## Other vertex-amalgamation paper checked

Ramon M. Figueroa-Centeno, Rikio Ichishima, and Francesc A. Muntaner-Batle, “Labeling the vertex amalgamation of graphs,” *Discussiones Mathematicae Graph Theory* 23(1) (2003), 129–139, DOI [10.7151/dmgt.1190](https://doi.org/10.7151/dmgt.1190). Metadata/abstract and full-text access are available through [EuDML](https://eudml.org/doc/270335) and the [Polish Digital Mathematics Library PDF](https://pldml.icm.edu.pl/pldml/element/bwmeta1.element.bwnjournal-article-doi-10_7151_dmgt_1190/c/dmgt.1190.pdf). The abstract and accessible full-text excerpts describe results on vertex amalgamations for graceful, felicitous, and harmonious graphs, with substantial focus on amalgamated cycles. The passages accessible in the search results do not state the specific α-path plus root-zero graceful residual operation with prescribed target positions. This paper is relevant background for vertex-amalgamation operations, but the inspected evidence does not show subsumption of the q24 target-zero conclusion.

## Older α-amalgamation construction

Barrientos, “Alpha graphs with different pendent paths,” *Electronic Journal of Graph Theory and Applications* 8(2) (2020), 301–317, DOI [10.5614/ejgta.2020.8.2.8](https://doi.org/10.5614/ejgta.2020.8.2.8). Publisher article page: [EJGTA](https://ejgta.org/index.php/ejgta/article/view/1036); direct [publisher PDF](https://ejgta.org/index.php/ejgta/article/download/1036/pdf_143). The article page states that it constructs α-trees by attaching pendent paths and combines α graphs; its introductory definitions and Lemma 1.1 (printed pp. 302–303) show that two α inputs admit some vertex amalgamation whose result is α, using interval shifts and a unique repeated label. This is operation-level overlap but is narrower in its input assumptions than the 2022 α-plus-graceful statement and does not prescribe the two q24 interior target labels. The publisher PDF endpoint returned a server parse error; the indexed PDF text was readable. The primary landing page gives bibliographic details and the abstract.

## Assessment and limits

1. The underlying splice is not presented as a new amalgamation principle. The closest match is Barrientos (2022): α-labeled first graph, graceful second graph rooted at label 0, identification of the first graph’s boundary vertex with the second graph’s zero vertex, graceful output. The q24 construction instantiates that old interval-shift operation with a long path.
2. The q24-specific content visible in the frozen proof is a uniform certificate for every `t≥1` whose two selected positions on each orientation carry the extrema `0` and `2K`, together with the target-dependent whole-output complement. The reviewed primary passages do not state this position-controlled two-target corollary.
3. The literature evidence is not enough to assert novelty or priority. The 2022 source’s full PDF could not be rendered directly by the browser, and the 1982 Huang–Kotzig–Rosa source was not obtained. Related primary papers may contain further consequences. **Priority is not assessed here and remains unknown.**
4. This is not an independent proof or a Lean replay. It compares the mathematical statement and proof architecture described in the pinned reports with retrieved literature text. It does not verify the q24 path recurrence, the formal theorem, or its compiled objects.

## Exact internal evidence pins

- q24 rooted-residual theorem report: `research-audits/graceful-q24-rooted-residual-generalization-2026-10-10-a/report.md`, SHA-256 `f0fd75067fa68c66c39a6d445e520776fdf0807abca0189e5f1ae6f491454166`.
- Separate mathematical QA report: `research-audits/graceful-q24-rooted-residual-independent-qa-2026-10-10-a/report.md`, SHA-256 `2562646cae28766997529b198d957f1fdf1d1c10425819968920594b34c1f061`.
- Related rooted conventional graft source inspected as interface context only: `research-audits/graceful-k71-rooted-residual-formal-2026-10-10-a/source/RootedInjective.lean`, SHA-256 `688e8761808978138bf749497295928d13a3e7903bdd21f95ab2c78f22d5f186`.
- q24 terminal path source inspected as interface context only: `research-audits/graceful-q24-zero-order-formal-2026-10-10-a/source/Q24Terminal.lean`, SHA-256 `088fd226e1c2adb57556ebd1fc047ba8494546511cb8096d4d089f679aefcc91`.
- Rooted-residual author formal status was separately pinned in the math report; no source objects or build logs are being used here.

## Access log

- Barrientos 2022, JACODES publisher article page and indexed full-text PDF passage: title, publication metadata, intro p. 103, and amalgamation/high-side-shift wording inspected. Direct publisher PDF open timed out; no local PDF hash is claimed.
- Barrientos 2020, EJGTA publisher article page and indexed full-text PDF: abstract, Lemma 1.1, intro definitions pp. 302–303 inspected. Direct publisher PDF open failed with a server parse error; no local PDF hash is claimed.
- Figueroa-Centeno et al. 2003, EuDML metadata/abstract and indexed DML-PL PDF full-text passages inspected; direct retrieval through the web opener was blocked, so claims are limited to surfaced text and metadata.
- Mavronicolas–Michael 2009, publisher abstract and bibliographic data inspected; author-hosted PDF open timed out. No exact theorem condition is inferred from the abstract.
- Huang–Kotzig–Rosa 1982: original full text not obtained; theorem conditions are only attributed as restated by later literature, and the original is not treated as fully inspected.

This note is a private literature-scope artifact. It does not make a priority, novelty, external-review, or publication claim.
