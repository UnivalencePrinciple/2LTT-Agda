# 2LTT-Agda

This is an attempt to a formalization of 2LTT and UP paper in Agda. Generally, the notation in UP paper is followed. 
For the difference between exo-types and types, the superscript `` _ᵉ`` is used. For example, we have two different universes: 

```agda
--exo-universe
UUᵉ i = SSet i
--universe
UU i = Set i
```

The main flags we used are ``--two-level`` and ``cumulativity``. 
However, currently, there is a bug about the usage of these flags together (See https://github.com/agda/agda/issues/5761).
