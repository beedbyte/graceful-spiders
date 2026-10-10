# Primary-source scope: moving-midpoint H1 append



Private additive assessment, 10 October 2026. **The append operation is an exact specialization of an older published graceful-permutation concatenation, after explicit alpha relabeling.** It should not be presented as a new concatenation operation. The prior-publication status of the specific positional corollary and its three spider families remains **UNKNOWN**. This assessment does not change the separately frozen mathematical GO or confer Lean/external-review status.



## 1. Exact target and evidence binding



The frozen claim starts with an odd k>=3 source X with H inventory0..k, L inventory0..k-1, sums0..2k-1, midpoint X[k]=k-1, prefix[H1,L0,H0,L2] and terminal H(k-1). It appends a shifted balanced core of radius p=3(k+1), giving K=4k+3 and a new physical midpoint Low(K-1). Iteration from k0 in{3,7,17} gives k_t=(k0+1)4^t-1. The actual S(k_t^n,1^m) has separate zero labelings for every selected named arm at depths k_t-2 and k_t-1, all n>=2,m>=0.



Exact author report: `../graceful-h1-midpoint-jump-recurrence-2026-10-10-a/report.md`, SHA39105bbd403610b73acfd11e1a87e8c1452e70d8d47d4cd01e5c17186890aef5. Separate mathematical QA report: `../graceful-h1-core-append-independent-2026-10-10-a/report.md`, SHA40ef92964a7d975890d1f8e3bafb125b81c04a674df311762efe537718c524b6. The 13 exact source/evidence paths and hashes are in input-pins.json. Older records remain unchanged.



## 2. Original sources actually inspected



| Primary source / location | Access and relevant scope |

|---|---|

| [Hicks–Ollis–Schmitt, *Distinct Partial Sums in Cyclic Groups: Polynomial Method and Constructive Approaches*](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf), proof of Lemma4.5, author-PDF p14 | Complete author PDF accessible and the actual construction read. The filename says2018; this version is dated29January2019. [Published metadata](https://onlinelibrary.wiley.com/doi/abs/10.1002/jcd.21652) gives J.Combin.Designs27(6)(2019),369–385. Lemma4.5's statement concerns the first absolute difference; the concatenation used here is in its proof. The authors credit an earlier construction in reference[1], Abrham–Kotzig1990. Exact retained PDF SHA120a134c58571c26b40f9b305919f5cae06e321aaaa8a16d9638c9d0f6a14bfc. |

| [Ollis, *Sequences in dihedral groups with distinct partial products*](https://ajc.maths.uq.edu.au/pdf/78/ajc_v78_p035.pdf), AJC78(1)(2020), printed pp53–54, Lemma5.5 and Theorem5.6 | Full original PDF and section5 read. Lemma5.5 gives bipartite endpoint existence and the endpoint gap p; it attributes this to [21]=Kotzig1973, not Gvozdjak. Theorem5.6 inserts a balanced path at adjacent x,y subject to x<y<2(y-x)=p, preserving translated endpoint labels. Exact retained PDF SHA943d6067b69b307c4fea44f909cc189887881710a355be31c77911aa164f46af. |

| [Adamaszek, *Efficient enumeration of graceful permutations*, arXiv:math/0608513v1](https://arxiv.org/pdf/math/0608513), 21August2006, Lemma1 and its proof, p4 | Complete original five-page PDF accessible through the web reader. It explicitly constructs the endpoint-matched concatenation, with a counting inequality. Its proof cites Klove1995 and Aldred–Siran–Siran2003. It is an earlier accessible primary exposition of the same operation. The first sandbox download failed; a subsequently approved read-only public download succeeded. Its exact PDF SHA is 70080ec51e5ec40f71475f27603882f4576af14e45f2451e4f134a6c79027235. The access/mathematical locator is recorded in source-access.json. |

| [Cattell, *Graceful labellings of paths*](https://www.sciencedirect.com/science/article/pii/S0012365X07001215), DM307(24)(2007),3161–3176 | Publisher-indexed abstract accessible; direct full-page open failed. It includes alpha-characterization and pi-representations, not only ordinary path gracefulness. The original proof remains uninspected. No inference excluding its constructions is justified. |

| Abrham–Kotzig, *Exponential lower bounds for the number of graceful numberings of snakes*, Congr.Numer.72(1990),163–174 | Exact citation/ancestry appears in the HOS original bibliography and proof. The original full article was not obtained in the bounded search. Its scope is therefore not independently reconstructed here. |



McGill–Ollis2019, DOI10.1016/j.disc.2018.10.046, was also located through publisher abstract/introduction excerpts, but its full construction section was not obtained and is not used as a proof premise. The extra contemporary alpha-tree search lead and unrelated search hits are not treated as evidence of exact subsumption. Missing results from these searches are access/search limitations, never evidence of novelty.



## 3. Exact reduction to the HOS construction



The following algebra is this audit's comparison calculation. All labels here are zero-based; the conversion back to the paper's one-based notation is explicitly checked in code.



Write ell=2k+1, p=3(k+1), K=k+p. From source offsets X define a graceful permutation gamma of0..2k by



    gamma_i = k-X_i       (i even),

              k+1+X_i     (i odd).



Its edge differences are1 plus X's adjacent sums, and gamma_last=1. From the balanced core C define a bipartite permutation alpha of0..2p-1 by



    alpha_i = p+C_i       (i even),

              p-1-C_i     (i odd).



Its differences are1 plus the core sums. It begins high, alpha_0=p+1=gamma_last+p. In one-based labels the matching endpoints are gamma_last+1=2 and alpha_0+1=p+2, with2<=p. Thus the exact hypothesis of the concatenation in the proof of HOS Lemma4.5 holds.



That construction produces the zero-based permutation



    T = (gamma+p) ++ (alpha_even+ell, alpha_odd).



T has cut K. Apply the elementary alpha relabeling



    R(v)=v+K       for 0<=v<=K,

         v-K-1     for K+1<=v<=2K.



R bijects the label interval and changes each cross-cut difference d to2K+1-d, so it preserves gracefulness. It interchanges the two size classes, giving cut K-1. Direct substitution gives:



* On the old even positions, R(T_i)=2K-X_i; on old odd positions it equals X_i.

* On appended local even positions, R(T)=k+C_i; on appended local odd positions it equals2K-(k+1+C_i).



These are **exactly**, entry by entry, the decoded labels of the frozen H1 append X++(C_even+k,C_odd+k+1). This is not merely matching inventory, a similarity of methods or a failed attempt at exclusion.



The same construction is the reversal of Adamaszek's Lemma1 gluing with r=ell, m=p, j=1: use reverse(alpha), whose endpoints are1,p+1, and reverse(gamma), whose initial element is1, and reverse the glued output. This gives precisely T. Accordingly the old-operation overlap is already supported by an accessible original exposition from2006, as well as HOS's later proof and its explicit earlier credit.



## 4. What still needs the positional calculation



HOS's general concatenation does not state our selected spider-depth result. The specific core supplies C_(2(k+1))=p-1. Since the core starts at global index2k+1, that location is global K when p=3(k+1). In T it carries maximum2K; after R it carries K-1, the correct low midpoint. The unchanged old prefix supplies zero at source index1 and maximum at2. The separately proved alpha-amalgamation residual then supplies actual named graphs for every n,m. These explicit identities establish the graph corollary from the old operation and chosen core; they do not establish that the corollary is historically new.



There is a concrete control separating generic concatenation from midpoint control. Use the valid k3 seed but the smaller old core p6. The same HOS reduction is perfectly graceful and yields K9; its physical midpoint label is7 instead of the required8. Thus arbitrary use of the old operation does not automatically give the present transfer interface. The audited p=3(k+1) choice supplies the missing positional equality.



The old private WholeArm proof, SHA1e475c51db4e401b9dc6b5d10720209b45b44c3a3e8c7c1d065c9e4347d66513, already contains the exact residue-three permutation and symmetric core. Its single-arm placement requires p<=r for target length2r+1. Here p=3(k+1)>2k+1=(K-1)/2, so that old placement theorem cannot be directly substituted to obtain the new position. This narrow fact does not rescue a new-operation claim: section3 supplies the actual old concatenation specialization. The historical ancestry of the residue-three core itself remains unresolved.



Ollis's endpoint lemma is consistent with the constructed alpha, and its insertion is another prior mechanism. No claim that this append is disjoint from all Ollis transformations is needed or justified. The literal HOS reduction is sufficient. Cattell's uninspected pi machinery and Abrham–Kotzig's uninspected original construction could further subsume the joint positional corollary.



## 5. Reproducible checks and scope



`python check.py` and `python -O check.py` are byte-identical. The checker imports no author program, revalidates 13 input hashes and independently reconstructs the core and exact HOS formula. It checks 18 entire label-word equalities: six append steps for each of the three frozen bases, including source conjugation, both indexing conventions, endpoint match, output alpha cut, rotation, exact midpoint and both extreme indices. Full resulting permutations reach K73727.



Eight negative controls detect omission of the rotation, use of ordinary complement alone, a wrong rotation boundary, direct untransformed input, off-by-one endpoint, wrong HOS side translation, uniform alpha translation and the false claim that generic append fixes the physical midpoint. The last is a valid graceful output that fails the required midpoint, rather than an invalid path. The unbounded equivalence rests on section3's entrywise identities; finite checks detect transcription mistakes.



Mathematical correctness remains the separate QA's GO. Methodological novelty of the concatenation is **excluded by exact specialization**. Historical priority of the precise joint-position and actual-spider corollary remains **UNKNOWN**. Extra coverage above D8 is a project-relative statement and does not imply worldwide novelty. This is internal AI-assisted comparison work, not external review, and makes no new formal-verification claim. No frozen record or public text was changed.



## 6. Concrete unsent external question



We have verified that our H1 append is exactly the endpoint-matched concatenation appearing in HOS Lemma4.5's proof and in Adamaszek2006 Lemma1, under the explicit alpha relabeling R above. Is the residue-three graceful permutation beginning (1,p-3,4,p-6,...) with its residue-two Walecki tail, or its doubled core with the simultaneous anchor C_(2s)=3s-1, already identified in Abrham–Kotzig, Cattell or another original source? In particular, does an existing theorem explicitly or immediately give, for p=3(k+1), the new physical midpoint K=4k+3 labeled K-1 together with source extreme indices1/2, hence the selected depth K-2 for every S(K^n,1^m)? Please identify an exact theorem/page or the stronger construction it specializes.



This question asks about the remaining positional-corollary provenance, not about whether concatenation is new. No specialist was contacted.

