# The ELF fixtures of test_symbols.py

## two.c

`two.c` is compiled and linked once, in the C and C++ toolchain image of theorem-labs/oss-verify (the
`oss-fuzz-theorems-2026.10` row of its `infra/toolchains.tsv`), with the compile flags of its
`infra/base-builder/toolchain.sh` (`BASE_CFLAGS`, less the `-fno-builtin-*` flags, which change nothing here) and the
link of its `infra/base-builder/link-fuzz-target`: `-static -no-pie -Wl,--gc-sections`, then the same link with
`-Wl,--strip-all`.  The program needs no C library, so it links with `-nostdlib` and its `_start` is in assembly, a
function of no size, as musl's is.
The image's `musl.cfg` gives the target (`riscv64-unknown-linux-musl`), `-march=rv64g -mabi=lp64d` and lld.

Run in this folder:

```sh
image=ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b
docker pull "$image"
docker run --rm --user "$(id -u):$(id -g)" -v "$PWD":/src -w /src "$image" sh -euc '
  cfg=--config=/opt/asan-static/musl.cfg
  flags="-march=rv64g -mabi=lp64d -Os -g -ffunction-sections -fdata-sections -fno-stack-protector -Wdate-time"
  clang $cfg $flags -c two.c -o /tmp/two.o
  clang $cfg -static -no-pie -Wl,--gc-sections -nostdlib /tmp/two.o -o two.unstripped
  clang $cfg -static -no-pie -Wl,--gc-sections -nostdlib -Wl,--strip-all /tmp/two.o -o two.stripped
  llvm-dwarfdump --debug-line two.unstripped > two.lines.txt'
```

The image has clang and llvm-dwarfdump 20.1.8.  The folder is mounted at `/src`, the compilation directory, so the
line table names `two.c` and no path of the machine that built it.  clang warns that `-no-pie` is unused: a static
link is not position independent anyway.

| file | bytes | sha256 |
|---|---|---|
| `two.unstripped` | 4104 | `43a20eaf6aff6f9016167ed3b548b4d22048f32296a174325e398e02c3a442a1` |
| `two.stripped` | 1720 | `5bfde43310ed9ace655eed147acc43fc7553d2ed0e0058ccb7f569cc98f2dfb9` |

Its symbols, as `llvm-readelf -s two.unstripped` lists them: the functions `_start` at `0x1129c` (size 0), `f` at
`0x112a8` (108 bytes), `g` and `h` at `0x11314` (40 bytes each), and the data objects `seed` at `0x1233c` in `.data`
and `counter` at `0x12340` in `.bss` (4 bytes each).

## computed_goto_global.c and computed_goto_biased.c

Each is a GNU C computed goto whose target is a label difference from the function's entry, `&&start +
offsets[which]`, kept in a volatile global so that the jump reads a reloaded value, and each binary holds no address
of an instruction of the function.  The tests that read them check that `symbols.mask` lets the jump go anywhere in
the function.

- `computed_goto_global.c`: GCC 13.3 compiles it for rv64 to `lla a3,.L2` (the entry), `add`, `sd`, `ld`, `jr a5`,
  with the offsets 0 and 60 in `.rodata`: the jump goes to `0x1003c`, inside the function.
- `computed_goto_biased.c`: the entry is also stored biased by 8192, `encoded = &&start + 8192`, and taken back as
  `encoded - 8192 + offsets[which]`. GCC 13.3 compiles it to `lla a5,.L2+8192` (8 KiB past the function), `sd`,
  `ld`, `sub`, `add`, `sd`, `ld`, `jr a5`, with the offsets 0 and 76: the jump goes to `0x1004c`.

They are compiled with Ubuntu 24.04's cross GCC and binutils, from their packages, with no C library and no unwind
tables, and linked at `0x10000` without relaxation.  Run in an empty folder that holds a copy of the two `.c` files,
on an amd64 Ubuntu 24.04 machine:

```sh
apt-get download cpp-13-riscv64-linux-gnu=13.3.0-6ubuntu2~24.04.1cross1 binutils-riscv64-linux-gnu=2.42-4ubuntu2.10
dpkg-deb -x cpp-13-riscv64-linux-gnu_13.3.0-6ubuntu2~24.04.1cross1_amd64.deb cc
dpkg-deb -x binutils-riscv64-linux-gnu_2.42-4ubuntu2.10_amd64.deb bu
export LD_LIBRARY_PATH=$PWD/bu/usr/lib/x86_64-linux-gnu
for f in computed_goto_global computed_goto_biased; do
  cc/usr/libexec/gcc-cross/riscv64-linux-gnu/13/cc1 -quiet -O2 -march=rv64g -mabi=lp64d \
    -fno-asynchronous-unwind-tables -fno-unwind-tables $f.c -o $f.s
  bu/usr/bin/riscv64-linux-gnu-as -march=rv64g -mabi=lp64d $f.s -o $f.o
  bu/usr/bin/riscv64-linux-gnu-ld --no-relax -e $f -Ttext=0x10000 $f.o -o $f.elf
done
```

| file | bytes | sha256 |
|---|---|---|
| `computed_goto_global.elf` | 5600 | `d24e6b3307f5b9a71e19839d154a8e50a184dabd17fc7e23b2c496568e5f0c5d` |
| `computed_goto_biased.elf` | 5648 | `f80852c101dfc40f02e3442e4faaa88c0c58cb6d3b1d171df4306e7bebff8b29` |

Their symbols, as `llvm-readelf -s` lists them: `computed_goto_global` at `0x10000` (68 bytes), with the data objects
`offsets.0` at `0x10048` in `.rodata` (16 bytes) and `saved` at `0x11058` in `.bss` (8 bytes); `computed_goto_biased`
at `0x10000` (84 bytes), with `offsets.0` at `0x10058` in `.rodata` (16 bytes), and `encoded` at `0x11068` and `saved`
at `0x11070` in `.bss` (8 bytes each).
