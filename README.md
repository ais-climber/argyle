## Argyle: ANN Reasoning in Lean
Argyle is a suite for formally verifying properties of neural network learning in Lean.  We do this via a conditional language with dynamic operators representing different learning policies.  For example, Argyle has verified the following fact about unsupervised hebbian learning:

[TODO]

Argyle is the more careful and deliberate sister of [Mod](https://github.com/ais-climber/mod).  After a year and a half of trouble with unit-testing Mod and debugging the proofs involved, I finally decided to put my mind at ease and formally verify the program in Lean instead.

**NOTE:** This program is currently very much in development, and many of the planned features involve significant research efforts (this is my PhD). So what the program can do right now is somewhat limited.

# Related Work
There are many other libraries for verifying neural networks, but they all only check _already trained_ nets.  In contrast, Argyle's focus is on verifying _learning algorithms themselves_, i.e. exploring the algebra of policies like Hebbian learning and backprop.  But Argyle is intended to do this one thing well. Depending on your needs, you might want to check out these other projects:
- [Amethyst](https://github.com/wenkokke/amethyst) (Agda)
- [Starchild](https://github.com/wenkokke/starchild) (F*)
- [Lazuli](https://github.com/wenkokke/lazuli) (Liquid Haskell)
- [Sapphire](https://github.com/wenkokke/sapphire) (Python, using Tensorflow)
- [Certigrad](https://github.com/dselsam/certigrad) (Lean)
- [FormalML](https://github.com/IBM/FormalML) (Coq)
- [DNNV](https://github.com/dlshriver/dnnv) (uses a Python-embedded DSL)

