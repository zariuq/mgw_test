# Megapedia - Formal Mathematics Contributions

This directory contains formal mathematics developments in Megalodon.

## Contents

### Knuth-Skilling Triad (Foundations of Physics from Symmetry)

**spacetime_foundations.mg** (1.1K)
- Causal set theory
- Representation theorem: Causal order → Minkowski spacetime
- Derives relativistic spacetime from causal structure alone
- Reference: Knuth "Arithmetic of Uncertainty" paper

**quantum_foundations.mg** (1.7K)
- Quantum algebras from symmetric operations
- Feynman path integral rules
- Born rule derivation
- Reference: Knuth-Skilling quantum foundations

**symmetry_foundations.mg** (2.3K)
- Symmetric operations and probability
- Partition tree equivalence
- Representation theorem for probability measures
- Reference: Knuth-Skilling probability foundations

### Ramsey Theory

**ramsey36_complete.mg** (118K)
- Complete formalization of Ramsey(3,6) = 18
- Adj17 witness graph for lower bound
- Upper bound proof structure (5-regular graph argument)
- WIP: Many theorems still admitted

**cardinality_lemmas.mg** (1.8K)
- Infrastructure for cardinality arguments
- equip_singleton and other cardinal lemmas
- Used by Ramsey36 proofs

### Graph Theory

**graph_basics.mg** (71K)
- Complete graph theory library
- Definitions: graphs, paths, cycles, trees
- Classic theorems: Hamiltonian, Eulerian, planarity
- Many theorems admitted (framework for future work)

### Probability Theory

**full_probability_theory.mg** (16K)
- Sigma-algebras and measure spaces
- Probability axioms (Kolmogorov)
- Conditional probability
- Independence
- WIP: Gemini's work on Billingsley formalization

## Status

All files compile with Megalodon + Egal preamble.

Many theorems are admitted (stated but not proven) - these represent
open problems and future work for the community.

## Verification

To check these files locally:
```bash
/path/to/megalodon -I sig/RamseyPreamble.mgs mglib/megapedia/file.mg
```

Or use the MGWiki build system (GitHub Actions will auto-check on push).

## Bounties

- ramsey36_complete.mg targets the 800 bar bounty for TwoRamseyProp_3_6_18
- See mglib/conj/ramsey/RamseyConjsWithBounties.mg for all Ramsey bounties

## Authors

These formalizations were developed collaboratively between:
- Claude (Sonnet 4.5)
- Gemini (Experimental)
- Human guidance and review

Generated November 2025
