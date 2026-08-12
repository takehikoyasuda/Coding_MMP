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

## Stein graph status

The Stein development branch now implements the graph construction in the
pinned paper revision as the kernel of

```text
B tensor C^[k]  -->  R_gamma.
```

The output ring contains the source and Stein coordinates, but not the original
target coordinates. New dimension regressions detect the extra scaling
parameter produced by the old construction. See `docs/IMPLEMENTATION-STATUS.md`
for the verification scope and remaining review items.

## License

The two implementation submodules are dedicated to the public domain under
CC0 1.0. A license for new integration-layer code will be added before its
first public release.
