# 2LTT-Agda
Formalization of 2LTT in Agda

Tested with **Agda 2.9.0**

This library is a formalization of two-level type theory (2LTT) in Agda, using the features of Agda that allow us
to work with two levels of types. The library is described in the paper

- E. Uskuplu, [Formalizing two-level type theory with cofibrant exo-nat](https://doi.org/10.1017/S0960129525100297),
  *Mathematical Structures in Computer Science* 35 (2025), e30.

The theory itself follows

- D. Annenkov, P. Capriotti, N. Kraus, C. Sattler, [Two-level type theory and applications](https://doi.org/10.1017/S0960129523000130),
  *Mathematical Structures in Computer Science* (2023) ([arXiv:1705.03307](https://arxiv.org/abs/1705.03307)),
- T. Altenkirch, P. Capriotti, N. Kraus, [Extending Homotopy Type Theory with Strict Equality](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2016.21),
  *CSL 2016*, LIPIcs 62, 21:1–21:17,
- B. Ahrens, P. R. North, M. Shulman, D. Tsementzis, [The Univalence Principle](https://bookstore.ams.org/memo-305-1541) (UP),
  *Memoirs of the American Mathematical Society* 305 (2025), no. 1541 ([arXiv:2102.06275](https://arxiv.org/abs/2102.06275)).

The library contains the basics of 2LTT (types, exo-types, and the relation between them) together with the three
classes of exo-types: fibrant, cofibrant, and sharp ones. The notion of sharpness is taken from the UP paper, and
the **2LTT** version of the library assumes cumulativity (every type is an exo-type), as in that paper.

**Note.** Earlier versions of the library used the `--type-in-type` flag in some files. This flag has been removed:
all results are now proved with carefully chosen universe levels.

The directory has two parts:

1) **2LTT** is the initial attempt of the formalization. We use Agda's `--two-level` and `--cumulativity` flags together. 

2) **2LTT_C** is the version without `--cumulativity`.

---

For questions and suggestions, please write to uskupluelif@gmail.com
