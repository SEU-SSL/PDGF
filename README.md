# PDGF
PDGF is a Predecessor-aware Directed Greybox Fuzzing tool. It can maintain a target-reachable code area (predecessors) and conduct regional fuzzing within this area.

The instrumentation process relies on the [SVF](https://github.com/SVF-tools/SVF).

The fuzzing process is based on the [AFL](https://github.com/google/AFL)

We recommend using docker:
```
docker pull seussl/pdgf:latest
```

