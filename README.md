# MMP computation in Macaulay2

Macaulay2 implementation project for the algorithms in Takehiko Yasuda,
*An algorithm for the minimal model program in dimension three*.

This repository is the integration layer. It pins the paper and the two
existing prototype implementations as Git submodules, and will contain the
remaining algorithms and the top-level MMP driver.

## Checkout

```sh
git clone --recurse-submodules <repository-url>
cd Coding_MMP
make test-upstreams
```

For an existing checkout:

```sh
git submodule update --init --recursive
```

The current development environment uses Macaulay2 1.26.06.

## Repository layout

| Path | Role |
| --- | --- |
| `references/AlgoMMP` | pinned paper revision |
| `third_party/SteinFactorizationM2` | bigraded Hom and Stein-factorization prototype |
| `third_party/flip-computation` | relative canonical model / flip prototype |
| `docs/IMPLEMENTATION-STATUS.md` | trusted scope, known failures, and paper-to-code map |
| `docs/ROADMAP.md` | implementation order for the full MMP |
| `scripts/test-upstreams.sh` | reproducible baseline test runner |

## Important status warning

The pinned Stein package does **not** yet implement the graph construction in
the pinned paper revision. Its `directSteinGraph` uses a known incorrect
bigrading and must not be used as a mathematical result. The paper now computes
the graph as the kernel of

```text
B tensor C^[k]  -->  R_gamma.
```

Updating the Stein implementation and its regression tests is the first coding
milestone. See `docs/IMPLEMENTATION-STATUS.md` for the precise boundary between
trusted and experimental functionality.

## License

The two implementation submodules are dedicated to the public domain under
CC0 1.0. A license for new integration-layer code will be added before its
first public release.
