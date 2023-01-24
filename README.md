## Argyle: An Agda Library for Reasoning about Learning
Argyle is a suite for formally verifying a neural network's learning in Agda.  We do this using a succinct modal language that packs a punch.  

Argyle is the more careful and deliberate sister of [à la Mode](https://github.com/ais-climber/a-la-mode).  Both share the same core features, but whereas à la Mode releases very quickly and is easy to use, Argyle promises to be formally verified at the cost of slow releases.

**NOTE:** This program is currently very much in development, and many of the planned features involve significant research efforts (this is my PhD). So what the program can do right now is somewhat limited.

# Related Projects
There are many other libraries for verifying neural networks, but they all only check _already trained_ nets.  In contrast, Argyle's focus is on verifying _learning algorithms themselves_, i.e. exploring the algebra of policies like Hebbian learning and backprop.  But Argyle is intended to do this one thing well. Depending on your needs, you might want to check out these other projects:
- [Amethyst](https://github.com/wenkokke/amethyst) (Agda)
- [Starchild](https://github.com/wenkokke/starchild) (F*)
- [Lazuli](https://github.com/wenkokke/lazuli) (Liquid Haskell)
- [Sapphire](https://github.com/wenkokke/sapphire) (Python, using Tensorflow)
- [Certigrad](https://github.com/dselsam/certigrad) (Lean)
- [FormalML](https://github.com/IBM/FormalML) (Coq)
- [DNNV](https://github.com/dlshriver/dnnv) (uses a Python-embedded DSL)

