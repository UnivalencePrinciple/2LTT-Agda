# 2LTT-Agda
Formalization of 2LTT in Agda

This library is an experiment about some new features of Agda that allows us work with two level type theory. 
We are mainly formalizing the content of the [Univalence Principle](https://arxiv.org/abs/2102.06275) (UP) paper, 
but the second chapter of the paper is about two level type theory ([2LTT](https://arxiv.org/abs/1705.03307)), 
and the rest of the paper makes use of it. Thus, the library also contains the basics of 2LTT. As far as the UP paper
assumes, we have completed all the 2LTT content, but the other parts of the paper are in progress.

The directory has two parts:

1) **2LTT** is the initial attempt of the formalization. We use Agda's `--two-level` and `--cumulativity` flags together. 

2) **2LTT_C** is the version without `--cumulativity`.

---

For questions and suggestions, please write to euskuplu@usc.edu
