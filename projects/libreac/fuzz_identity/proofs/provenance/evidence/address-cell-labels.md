# The address-cell labels of lib/A/AB1w.v and lib/ReusableB/YB1w.v

`lib/A/AB1w.v` and `lib/ReusableB/YB1w.v` give the address range of each runtime function as a pair of cells,
`tfib_A_<label>` and `tfib_E_<label>`. The label is documentation: the proofs read the addresses. Which labels
stay in these files is decided by one test, `label_test.py` beside this note, run on every label of each file.
`address-cell-labels.tsv` beside this note is its output: one row for every label, kept or removed, with the
evidence of each clause of the test.

## The images

`lib/A/AB1w.v` describes image A, `fuzz_identity.asan`, and `lib/ReusableB/YB1w.v` describes image B,
`fuzz_identity.asan-ubsan`. This unit's `harness.yaml` pins them:

| image | build | sha256 | its `.debug` twin, sha256 |
|---|---|---|---|
| A | `fuzz_identity.asan` | `c954b804786cb87fc218414447199e35235b9788453ec0db312f97cd0dc4291b` | `5b0cbe57303630895c71979f5c3209f1d343f0f42aad36e87c9f5193408da124` |
| B | `fuzz_identity.asan-ubsan` | `baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66` | `43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064` |

Symbols, sizes and inline records come from each twin; the test checks that the twin's loaded segments hold the
same bytes as the image, except the ELF header and the build-id note. Both label files were copied from the cgif
donor, `projects/cgif/cgif_file_fuzzer`, as their headers say; that unit's `harness.yaml` pins its asan image at
`7093581aab04…` and its asan-ubsan image at `1c29845fe605…`.

## The test

The test runs `lib/A/AB1w.v` against image A and `lib/ReusableB/YB1w.v` against image B, apart: no verdict of one
image is used for the other. This is the test as `label_test.py` states it in its own text, copied here from that
text:

```
THE TEST

The held functions of a cell are the function symbols of the image that start in [tfib_A_<label>, tfib_E_<label>).
Clauses (a) to (d) are tested for each function the label names (WHAT A LABEL NAMES, below), one name at a time.
A label that THE NAME AFTER THE PREFIX (below) shows false is REMOVED, whatever (a) to (e) show. Any other label
that names at least one function is KEPT when (a), (b), (c) or (d) holds for at least one of the functions it
names, and REMOVED otherwise; its words are not counted, so a true word does not keep a label whose names are all
shown false. Any other label that names no function is KEPT when (e) holds, and REMOVED otherwise. A token that
names no function of the image is a word: it cannot make a label false.

 (a) symbol   A function the label names is a held function.
 (b) inlined  The debug information records a function the label names as inlined at an address inside the cell.
 (c) call     The code of the cell calls, or tail-jumps to, a function the label names; or the code of a function
              the label names, or of an inlined copy of it, calls or tail-jumps to a held function.
 (d) value    The code of the cell loads a global byte that the code of a function the label names, or of an
              inlined copy of it, stores. Or some function calls a function the label names, and the value
              returned in a0 then reaches, in that caller's code after the call (in address order, up to its next
              return or jump out of it), either an argument register (a0-a7) of a call to a held function that
              the held function reads, or a store to a global byte that the code of the cell loads. The value
              moves through mv and through stack slots. A held function reads an argument register when, in
              address order from its entry, an instruction uses the register before one writes it; a call, a
              tail jump or an ecall before any write passes the register on and counts as a use.
 (e) words    The label names no function, at least one of its words is shown true of the held functions, and
              no word is shown false (WORDS, below).

THE NAME AFTER THE PREFIX

This rule is the ruling of 2026-10-31T08:48:10Z on tfib cells, which a ruling of 2026-11-01T09:59Z applies to this
test: "A cell is WRONG when the name after its prefix is ITSELF a function symbol of the image and the value is a
DIFFERENT function with no relation the suffix states." The test reads it this way, regardless of inlining or call
edges. The prefix is tfib_A_ or tfib_E_. The name after it is the longest leading run of the label (WHAT A LABEL
NAMES; the cut rule does not apply) that is a spelling of at least one function symbol of the image; inline records
do not count. A label with no such run has no name after its prefix, and this rule does not apply to it. The suffix
is the label's tokens after that run; it may be empty. The value is a different function when the function symbol
whose range holds tfib_A_<label> is none of the symbols the name spells, or no function symbol holds it. The suffix
states a relation when one of its tokens is at least 3 characters long and is not a number (a number as in WORDS);
whether the relation it states holds is decided by (a) to (e), as for any label. A label whose name after its prefix
is a function symbol, whose value is a different function, and whose suffix states no relation is false.

WHAT A LABEL NAMES

The label is split at "_" into tokens. A run of consecutive tokens, joined again by "_", names a function F when it
is one of F's spellings. Every spelling is written with each run of underscores shortened to one underscore and
without leading or trailing underscores (so internal__exit is spelled internal_exit). The spellings are:
 - a C function f: f; and, when f begins with __asan_, __lsan_, __ubsan_ or __sanitizer_, also f without that
   prefix (so __asan_stack_malloc_0 is also spelled stack_malloc_0);
 - an interceptor, trampoline or wrapper symbol P+f, P one of __interceptor_trampoline_, ___interceptor_,
   __interceptor_, __wrap_: also the spellings of f, so the plain name f also names it; and for ___interceptor_
   and __interceptor_ also icpt_ followed by the spelling of f;
 - a C++ function c1::c2::...::cn (template arguments and "(anonymous namespace)" left out): ck_..._cn for each
   k; so a namespace or class may be left out, and a class name also names its constructors;
 - a function that the debug information records as inlined, by its recorded name n with template arguments
   left out (the record carries no class or namespace; names of destructors, which begin with "~", are not
   spellings): the spellings that a C function named n would have (above), and K_n where K is a component other
   than the last of the qualified name of any C++ function symbol.
In a label of 48 characters, the longest a label is, the label may have been cut: its last run also names F when
it is at least 5 characters long and begins one of F's spellings other than the K_n ones. The label names the
functions of every naming run that is not part of a longer naming run.

A function the label names is found in the image as: its symbols (all symbols with that spelling), and its inline
records (all inline records whose recorded name has that spelling).

WORDS

The words of a label are its tokens that are in no naming run, except tokens shorter than 3 characters and
numbers (decimal, 0x hex, or hex that has a decimal digit). A decimal number followed by "insns", "insn" or "ins"
is one count word, and the tokens "no" and "op" side by side are the word "no_op". A word is shown true or false
of the held functions by these tests, on the instructions of the cell [tfib_A, tfib_E):
 - count word N:    true when the cell holds N instructions, false otherwise;
 - ctor:            true when a held symbol is a constructor (its last two name components are equal) or the
                    held address is an entry of .init_array or .preinit_array, false otherwise;
 - dtor:            true when a held symbol is a destructor (last component begins with "~") or the held address
                    is an entry of .fini_array, false otherwise;
 - weak:            true when a held symbol has weak binding, false otherwise;
 - ret:             true when the last instruction of the cell is ret, false otherwise;
 - getter:          true when the cell stores nothing except through sp and makes no call, false otherwise;
 - no_op:           true when the cell holds at most 2 instructions, stores nothing and makes no call, false
                    otherwise;
 - stub, tiny, shim, thunk, trampoline:
                    true when the cell holds at most 4 instructions, false otherwise;
 - any other word:  true when, ignoring case, it is part of the demangled name of a held symbol or of the file name
                    of the held code (the compile unit of the first held function, and the line-table file of its
                    first instruction); otherwise it is not shown either way.

WHAT THE CODE IS

The code is the image's .text, decoded as RV64GC. A call is jal or jalr with rd = ra; a tail jump is j to an
address outside the jumping function, or jr through a register that holds a known address. A register holds a
known address after auipc, and keeps it through addi, andi, mv, and a load from a .got slot (which gives the
address the slot holds); any other write forgets it; a call forgets a0-a7, t0-t6 and ra; at a forward branch
target it keeps only what every incoming path agrees on. A load or store through a register that holds a known
address accesses that address (lr, sc and amo name their address register as a plain operand; lr is a load, sc
a store, amo both); such an address is a global byte. Loads from .got slots are not counted as loads of a value.
Symbols, sizes and inline records come from the debug twin of each image, whose loaded segments the script
checks against the image.

LIMITS

 - The cut rule matches widely: the last run of a 48-character label names every function with a spelling that
   begins with it, so a short common last run (for example "sanitizer") names many functions.
 - Names are matched on tokens, so a token that is both a plain word and the name of some function (add, lock,
   exit, call) counts as a name.
 - Spellings are normalised (WHAT A LABEL NAMES): runs of underscores count as one, and the prefixes __asan_,
   __lsan_, __ubsan_ and __sanitizer_ of a C name may be left out. Names that differ only in these are the same
   spelling, and a short spelling made this way (for example __asan_init spelled init) is a name too.
 - All three add names. A name added this way can keep a label, when (a) to (d) hold for it, and it stops the
   label's words from counting.
 - The value clause (d) follows a value one step only: from a store to a load of the same global byte, or from a
   return to an argument or a global store in one caller. A value that travels further, or through an object in
   memory, is not followed.
 - Code is read in address order; a path through a backward branch is not followed.
 - THE NAME AFTER THE PREFIX does not read what a suffix says: a suffix with any token of 3 or more characters that
   is not a number counts as stating a relation, and (a) to (e) then decide the label as for any other label.

The table's names_shown column gives, for each name the label spells, the clauses of (a) to (d) that hold for it;
its name_after_prefix column gives that name, the function symbols it spells, the function that holds the value,
and the suffix.
```

## How to run it

From the unit root, with the four files of the table above:

```
python3 proofs/provenance/evidence/label_test.py --unit . \
    --image-a <fuzz_identity.asan> --debug-a <its .debug twin> \
    --image-b <fuzz_identity.asan-ubsan> --debug-b <its .debug twin> \
    --cells-a proofs/provenance/evidence/address-cell-labels.tsv \
    --cells-b proofs/provenance/evidence/address-cell-labels.tsv > fresh.tsv
diff fresh.tsv proofs/provenance/evidence/address-cell-labels.tsv
```

`--cells-*` takes the cells to test from the table, because a removed label's cells are no longer in the tree. The
run of record used Python 3.12, pyelftools 0.33, capstone 5.0.7 and the system libstdc++ for demangling. The
script refuses an image whose sha256 is not the one `harness.yaml` pins.

## The six runs

The test was committed before it was run, in commit `c83f22450860`. Its first run showed three faults in the
program, places where the code did not do what the stated test says; the test itself did not change:

1. `lr`, `sc` and `amo` were not counted as memory accesses: the disassembler gives their address register as a
   plain operand, and the code only read memory operands.
2. Clause (d) asked only that a returned value reach an argument register of a call to a held function; the
   test is that the held function reads the value. The first run therefore kept `AsanCheckIncompatibleRT`, whose
   held function is a 4-byte `ret`.
3. Inline records were spelled by their raw recorded names, so an inlined function whose name begins with
   underscores could not be named, while a symbol of the same name could.

Commit `fed2d7a952d8` corrects the three; against the first run, its run changed three verdicts in both images
(`AsanCheckIncompatibleRT` removed, `icpt_vfprintf_2` and `IncreaseTotalMmap` kept). Commit `0cf3878fdf98` sorts
the items inside an evidence cell before printing, because their order depended on Python's string-hash seed;
its run, the third, agrees with the second on every verdict and clause. Up to the third run a true word could
keep a label whose named functions are all shown false: clause (e) kept the crossed pair
`sanitizer_free_hook_weak_default` / `sanitizer_ignore_free_hook_weak_default_ret_0` on the word "weak", although
each names the other's function. Commit `2d273a084a9e` narrows the test, prompted by that output: a label that
names a function stays only by (a) to (d) on one of its names, and its words are not counted; (e) decides only
for a label that names no function. A token that names no function is a word and cannot make a label false, so
`DieOnMapFailure_sealed` stays kept by (e) on "sealed": `DieOnMapFailure` names no function of the image. The
narrowing moved 27 labels in each image from kept to removed, all of them kept by (e) before. Among them were
correct labels removed only because the name test did not see the held function's own name: `stack_malloc_0`
holds `__asan_stack_malloc_0` and `internal_exit_exit_group` holds `__sanitizer::internal__exit`, so an
incidental token (`malloc`, `exit`) that names some other function decided them. That was a fault of the program,
and commit `1ccbe70596c4` corrects it: spellings shorten runs of underscores to one, and a C name with the prefix
`__asan_`, `__lsan_`, `__ubsan_` or `__sanitizer_` is also spelled without it; the clauses did not change. Its run,
the fifth, kept `stack_malloc_0`, `stack_malloc_3`, `stack_malloc_4` and `internal_exit_exit_group` again by (a),
and changed no other verdict. The fifth run, on the tree that carried its verdicts, was the run of record up to
commit `241451cf067f`, and gave the table at that commit. The labels the narrowing removed are marked in the removed
tables below. The test states its own limits in its text (LIMITS, above).

Up to the fifth run, a label could stay by (b), (c) or (d) although it was itself the name of another function of
the image: `asan_register_globals` held `__asan_register_elf_globals` and stayed by (c), because the held function
calls `__asan_register_globals`. A ruling of 2026-10-31 at 08:48:10Z had called such a cell wrong: "A cell is WRONG
when the name after its prefix is ITSELF a function symbol of the image and the value is a DIFFERENT function with
no relation the suffix states." A ruling of 2026-11-01 at 09:59Z applied that rule to this test; the approval of
the test at 23:54Z on 2026-10-31 had not overridden it. Commit `df96aa536d49`, made at 2026-11-01T10:08:56Z, put the
rule into the test text, under THE NAME AFTER THE PREFIX, with how the test reads it, and added the column
`name_after_prefix`; clauses (a) to (e) did not change. Its run, the sixth, started at 10:09:07Z on the tree at that
commit, before any cell was removed. It moved 9 labels in each image from kept to removed and changed no other
verdict. All nine were among the 34 labels that the fifth run had restored (The result, below). In each of them the
name after the prefix was a function symbol, the value was in a different function, and the suffix stated no
relation. The fifth run had kept each of them by the clause in the last column, which the rule overrode:

| label | the name's symbol, image A / B | the function that holds the value, image A / B | suffix | the fifth run kept it by |
|---|---|---|---|---|
| `LargeMmapAllocator_EnsureSortedChunks` | `__sanitizer::LargeMmapAllocator::EnsureSortedChunks` at 0x37220 / 0x37288 | `__sanitizer::LargeMmapAllocator::ForEachChunk` at 0x37378 / 0x373e0 | none | (c): the cell calls the named function (A 0x373a4, B 0x3740c) |
| `asan_register_globals` | `__asan_register_globals` at 0x3ece0 / 0x3ed48 | `__asan_register_elf_globals` at 0x400c8 / 0x40130 | none | (c): the cell calls the named function (A 0x400fc, B 0x40164) |
| `asan_unregister_globals` | `__asan_unregister_globals` at 0x3fafc / 0x3fb64 | `__asan_unregister_elf_globals` at 0x40134 / 0x4019c | none | (c): the cell calls the named function (A 0x40168, B 0x401d0) |
| `icpt_vfprintf_2` | `__interceptor_vfprintf` at 0x455dc / 0x45644 | `__interceptor_fprintf` at 0x459a8 / 0x45a10 | `2` | (b): `___interceptor_vfprintf` is recorded as inlined in the cell, 88 bytes |
| `IsStackTraceSuppressed` | `__asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*)` at 0x5b91c / 0x5b984 | `__asan::IsAddrSuppressed(char const*, __sanitizer::Symbolizer*, unsigned long)` at 0x5b6f4 / 0x5b75c | none | (c): the named function calls the held one (A 0x5ba48, B 0x5bab0) |
| `IncreaseTotalMmap` | `__sanitizer::IncreaseTotalMmap(unsigned long)` at 0x602c8 / 0x60330 | `__sanitizer::DecreaseTotalMmap(unsigned long)` at 0x6030c / 0x60374 | none | (d): the named function stores the global byte 0x134a78 / 0x134d78 (A 0x602e0, B 0x60348) and the cell loads it (A 0x60328, B 0x60390) |
| `GetThreadStackAndTls` | `__sanitizer::GetThreadStackAndTls` at 0x6cbd4 / 0x6cc3c | `__sanitizer::GetTls(unsigned long*, unsigned long*)` at 0x6c7e4 / 0x6c84c | none | (c): the named function calls the held one (A 0x6cc14, B 0x6cc7c) |
| `MmapFixedNoReserve` | `__sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*)` at 0x6e0a4 / 0x6e10c | `__sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*)` at 0x6e1d4 / 0x6e23c | none | (c): the cell calls the named function (A 0x6e1f0, B 0x6e258) |
| `MmapFixedOrDie` | `__sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*)` at 0x660f0 / 0x66158 | `__sanitizer::ReservedAddressRange::MapOrDie(unsigned long, unsigned long, char const*)` at 0x6e480 / 0x6e4e8 | none | (c): the cell tail-jumps to the named function (A 0x6e48c, B 0x6e4f4) |

`icpt_vfprintf_2` was the only one of the nine with a suffix. The test read its suffix `2`, a number, as stating no
relation (LIMITS, above). A ruling of 2026-11-01 at 10:10Z on this label gave the reason: "a numeric suffix is a
disambiguator, not a stated relation — `_2` says "another cell", not "the function that calls vfprintf", so the
name claims `__interceptor_vfprintf` at a value that is `__interceptor_fprintf`: WRONG under my 08:48:10Z rule as
written."

The qualifier "with no relation the suffix states" decided labels in the sixth run. In 42 labels of each image the
name after the prefix was a function symbol and the value was in a different function, but the suffix had a word,
so the rule left them to (a) to (e). Those clauses kept 17 of them in each image, among them
`asan_before_dynamic_init_asan_after_dynamic_init` and `MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve`, and
removed the other 25, as the fifth run had. A test of the name alone would have removed those 17 too.

The deletion commit, whose parent is `df96aa536d49`, removed the definition line of each of the nine labels from
each file (The nine cells removed by the sixth run, below). The same script, run again with the same cells on the
tree after that removal, gave the table beside this note: it differed from the output of the sixth run only in
`in_tree`, on the 18 rows of the nine labels. The sixth run, at commit `df96aa536d49`, is the run of record.

## The result

- `lib/A/AB1w.v` against image A, in the sixth run: 522 labels tested, 454 kept, 68 removed. At the deletion commit the file held exactly the 454 kept labels and none of the 68 removed: `in_tree` equals the verdict on 522 of the 522 rows of the table beside this note.
- `lib/ReusableB/YB1w.v` against image B, in the sixth run: 537 labels tested, 469 kept, 68 removed. At the deletion commit the file held exactly the 469 kept labels and none of the 68 removed: `in_tree` equals the verdict on 537 of the 537 rows.

Against the two files as they stood before this test, at commit `0a3a06762f6b`, the sixth run's verdicts restored
25 labels to each file, each with its line byte for byte from the base and in the base's order; removed 10 labels
from each file that were in it; and left 429 labels of `lib/A/AB1w.v` and 444 of `lib/ReusableB/YB1w.v` unchanged.
The fifth run had restored 34 labels to each file; the nine that the sixth run removed were among them. At the
deletion commit no `.v` file of this unit named a removed cell.

Two removed labels name a function whose value does reach the held function, but further than the one step that
clause (d) follows, so (d) does not hold for them:

- `SealedTopOfMemory_check` holds `__asan::CheckSealedAddressSpace`. `SealedTopOfMemory` has no symbol and is
  inlined only into `GetMaxUserVirtualAddress`, which returns the value to `InitializeHighMemEnd` (image A call
  0x590fc, image B 0x59164); that function stores it in `kHighMemEnd` (A 0x59104, B 0x5916c), and the held
  function loads `kHighMemEnd` (A 0x59b8c, B 0x59bf4). That is two steps: a return, then a store and a load.
- `HeapProfile_Insert_asan_memory_profile` holds `__asan::HeapProfile::Print`. `HeapProfile::Insert` stores the
  record count at offset 0x38 of its object (A 0x537b8, B 0x53820) and reads the record array at offset 0x28
  (A 0x537b0, B 0x53818); the held function reads offsets 0x28 and 0x38 of its own object (A 0x53408 and 0x5340c,
  B 0x53470 and 0x53474). The value travels through an object in memory, not through a global byte.

## The columns of the table

`image`, `label`, `lo`, `hi`: the cell. `held`: the function symbols that start in it, with address and size.
`names`: each naming run of the label, with the symbols and inline records it names. `names_shown`: for each of
those names, the clauses of (a) to (d) that hold for it. `a_symbol` to `d_value`: the evidence of each clause over
all the names, `no` when the clause found nothing; a clause that found more than three things lists three and the
count of the rest. `e_words`: the words and their tests, and whether they count. `name_after_prefix`: the name after
the label's prefix (THE NAME AFTER THE PREFIX, above), the function symbols it spells, the function that holds the
value, and the suffix; it begins with `false:` when it makes the label false. `verdict` and `clauses`: kept or
removed, and the clauses that hold. `in_tree`: whether the label is in the tree's file. In the removed tables
below, the why of a label that the narrowing moved says so, and the why of a label that the sixth run moved gives
its `name_after_prefix`.

## The removed labels of lib/A/AB1w.v, image A

| # | label | cell | held | names | names_shown | (a) symbol | (b) inlined | (c) call | (d) value | (e) words | why |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `QuarantineCache_DequeueBatch` | 0x3398c..0x33b10 | __sanitizer::QuarantineCache::MergeBatches at 0x3398c, 388 B | QuarantineCache_DequeueBatch: 2 inline records | QuarantineCache_DequeueBatch: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 2 | `LargeMmapAllocator_EnsureSortedChunks` | 0x37378..0x37474 | __sanitizer::LargeMmapAllocator::ForEachChunk at 0x37378, 252 B | LargeMmapAllocator_EnsureSortedChunks: __sanitizer::LargeMmapAllocator::EnsureSortedChunks at 0x37220 | LargeMmapAllocator_EnsureSortedChunks: c | no | no | call 0x373a4 to __sanitizer::LargeMmapAllocator::EnsureSortedChunks | no | no words | removed: the name after the prefix is false, in the sixth run: LargeMmapAllocator_EnsureSortedChunks: __sanitizer::LargeMmapAllocator::EnsureSortedChunks at 0x37220; the value is in __sanitizer::LargeMmapAllocator::ForEachChunk at 0x37378, a different function; there is no suffix; the fifth run kept it by (c) |
| 3 | `asan_register_globals` | 0x400c8..0x40134 | __asan_register_elf_globals at 0x400c8, 108 B | asan_register_globals: __asan_register_globals at 0x3ece0 | asan_register_globals: c | no | no | call 0x400fc to __asan_register_globals | no | no words | removed: the name after the prefix is false, in the sixth run: asan_register_globals: __asan_register_globals at 0x3ece0; the value is in __asan_register_elf_globals at 0x400c8, a different function; there is no suffix; the fifth run kept it by (c) |
| 4 | `asan_unregister_globals` | 0x40134..0x4019c | __asan_unregister_elf_globals at 0x40134, 104 B | asan_unregister_globals: __asan_unregister_globals at 0x3fafc | asan_unregister_globals: c | no | no | call 0x40168 to __asan_unregister_globals | no | no words | removed: the name after the prefix is false, in the sixth run: asan_unregister_globals: __asan_unregister_globals at 0x3fafc; the value is in __asan_unregister_elf_globals at 0x40134, a different function; there is no suffix; the fifth run kept it by (c) |
| 5 | `RoundUpTo_size_CHECK_helper_sanitizer_common_h_C` | 0x41508..0x41658 | __sanitizer::RoundUpToPowerOfTwo(unsigned long) at 0x41508, 336 B | RoundUpTo: 92 inline records; size: 118 inline records | RoundUpTo: none; size: none | no | no | no | no | not counted, the label names a function: CHECK - (not shown); helper - (not shown); sanitizer true (in the held name); common true (in the file name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 6 | `memcmp_2` | 0x421a0..0x421a4 | __wrap_bcmp at 0x421a0, 4 B | memcmp: __wrap_memcmp at 0x4219c, __interceptor_memcmp at 0x437f0, memcmp at 0x945e4 | memcmp: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 7 | `vfprintf_2` | 0x421c8..0x421cc | __wrap_fprintf at 0x421c8, 4 B | vfprintf: __wrap_vfprintf at 0x421c0, __interceptor_vfprintf at 0x455dc, vfprintf at 0x90e50, 1 inline records | vfprintf: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 8 | `icpt_vfprintf_2` | 0x459a8..0x45a80 | __interceptor_fprintf at 0x459a8, 216 B | icpt_vfprintf: __interceptor_vfprintf at 0x455dc, 1 inline records | icpt_vfprintf: b | no | ___interceptor_vfprintf 88 B | no | no | no words | removed: the name after the prefix is false, in the sixth run: icpt_vfprintf: __interceptor_vfprintf at 0x455dc; the value is in __interceptor_fprintf at 0x459a8, a different function; the suffix 2 states no relation; the fifth run kept it by (b) |
| 9 | `icpt_diouxXn` | 0x47cd8..0x47e70 | format_get_value_size(char, char const*, bool) at 0x47cd8, 408 B | none | no names | no | no | no | no | no: icpt - (not shown); diouxXn - (not shown) | removed: the label names no function, and (e) showed no word true |
| 10 | `InitializeSignalInterceptors_or_syscall_hooks` | 0x516f4..0x51850 | __sanitizer::Sort at 0x516f4, 348 B | InitializeSignalInterceptors: 1 inline records; syscall: syscall at 0x8f15c | InitializeSignalInterceptors: none; syscall: none | no | no | no | no | not counted, the label names a function: hooks - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 11 | `AsanCheckIncompatibleRT` | 0x52a3c..0x52a40 | __asan::AsanCheckDynamicRTPrereqs() at 0x52a3c, 4 B | AsanCheckIncompatibleRT: __asan::AsanCheckIncompatibleRT() at 0x52a40 | AsanCheckIncompatibleRT: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 12 | `AsanCheckDynamicRTPrereqs` | 0x52a40..0x52ba8 | __asan::AsanCheckIncompatibleRT() at 0x52a40, 360 B | AsanCheckDynamicRTPrereqs: __asan::AsanCheckDynamicRTPrereqs() at 0x52a3c | AsanCheckDynamicRTPrereqs: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 13 | `icpt_cfree_or_DlsymFree` | 0x52edc..0x52fa8 | __sanitizer::DlSymAllocator<DlsymAlloc>::Allocate(unsigned long, unsigned long) at 0x52edc, 204 B | none | no names | no | no | no | no | no: icpt - (not shown); cfree - (not shown); DlsymFree - (not shown) | removed: the label names no function, and (e) showed no word true |
| 14 | `HeapProfile_Insert_asan_memory_profile` | 0x533d4..0x53540 | __asan::HeapProfile::Print(unsigned long, unsigned long) at 0x533d4, 364 B | HeapProfile_Insert: __asan::HeapProfile::Insert(unsigned int, unsigned long) at 0x53744 | HeapProfile_Insert: none | no | no | no | no | not counted, the label names a function: asan true (in the held name); memory true (in the file name); profile true (in the held name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 15 | `asan_poison_stack_memory_PoisonAlignedStackMemor` | 0x54084..0x54224 | __asan_poison_memory_region at 0x54084, 416 B | asan_poison_stack_memory: __asan_poison_stack_memory at 0x54850; PoisonAlignedStackMemor: 2 inline records | asan_poison_stack_memory: none; PoisonAlignedStackMemor: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 16 | `asan_unpoison_stack_memory` | 0x54224..0x543a4 | __asan_unpoison_memory_region at 0x54224, 384 B | asan_unpoison_stack_memory: __asan_unpoison_stack_memory at 0x548ec | asan_unpoison_stack_memory: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 17 | `SealedTopOfMemory_check` | 0x59b6c..0x59bd0 | __asan::CheckSealedAddressSpace() at 0x59b6c, 100 B | SealedTopOfMemory: 1 inline records | SealedTopOfMemory: none | no | no | no | no | not counted, the label names a function: check true (in the held name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 18 | `asan_handle_no_return_tiny_rtl_stub_2_insns` | 0x59d44..0x59d4c | __asan::OnLowLevelAllocate(unsigned long, unsigned long) at 0x59d44, 8 B | asan_handle_no_return: __asan_handle_no_return at 0x5996c | asan_handle_no_return: none | no | no | no | no | not counted, the label names a function: tiny true (2 instructions); rtl true (in the file name); stub true (2 instructions); 2_insns true (2 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 19 | `IsStackTraceSuppressed` | 0x5b6f4..0x5b840 | __asan::IsAddrSuppressed(char const*, __sanitizer::Symbolizer*, unsigned long) at 0x5b6f4, 332 B | IsStackTraceSuppressed: __asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*) at 0x5b91c | IsStackTraceSuppressed: c | no | no | call 0x5ba48 from __asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*) | no | no words | removed: the name after the prefix is false, in the sixth run: IsStackTraceSuppressed: __asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*) at 0x5b91c; the value is in __asan::IsAddrSuppressed(char const*, __sanitizer::Symbolizer*, unsigned long) at 0x5b6f4, a different function; there is no suffix; the fifth run kept it by (c) |
| 20 | `asan_thread_tiny_getter_3_insns` | 0x5bacc..0x5bad8 | __asan::AsanThreadContext::OnCreated(void*) at 0x5bacc, 12 B | none | no names | no | no | no | no | no: asan true (in the held name); thread true (in the held name); tiny true (3 instructions); getter false (2 stores, 0 calls, first store 0x5bacc); 3_insns true (3 instructions) | removed: the label names no function, and (e) showed a word false |
| 21 | `AsanThread_SetThreadStackAndTls` | 0x5c088..0x5c22c | __asan::AsanThread::ClearShadowForThreadStackAndTLS() at 0x5c088, 420 B | AsanThread_SetThreadStackAndTls: __asan::AsanThread::SetThreadStackAndTls(__asan::AsanThread::InitOptions const*) at 0x5c900 | AsanThread_SetThreadStackAndTls: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 22 | `AsanThread_ClearShadowForThreadStackAndTLS` | 0x5c900..0x5ca0c | __asan::AsanThread::SetThreadStackAndTls(__asan::AsanThread::InitOptions const*) at 0x5c900, 268 B | AsanThread_ClearShadowForThreadStackAndTLS: __asan::AsanThread::ClearShadowForThreadStackAndTLS() at 0x5c088 | AsanThread_ClearShadowForThreadStackAndTLS: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 23 | `weak_default_hook_ret` | 0x5dc44..0x5dc48 | __sanitizer::ThreadContextBase::OnStarted(void*) at 0x5dc44, 4 B | none | no names | no | no | no | no | no: weak false (no weak symbol); default - (not shown); hook - (not shown); ret true (last instruction ret) | removed: the label names no function, and (e) showed a word false |
| 24 | `InternalAlloc_RawInternalAlloc` | 0x5dc50..0x5de90 | __asan::GetAsanThreadContext(unsigned int) at 0x5dc50, 576 B | InternalAlloc: __sanitizer::InternalAlloc at 0x5e23c; RawInternalAlloc: 1 inline records | InternalAlloc: none; RawInternalAlloc: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 25 | `internal_allocator_getter` | 0x5e428..0x5e434 | __sanitizer::GetGlobalLowLevelAllocator() at 0x5e428, 12 B | internal_allocator: __sanitizer::internal_allocator() at 0x5e0e4 | internal_allocator: none | no | no | no | no | not counted, the label names a function: getter true (0 stores, 0 calls) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 26 | `LowLevelAllocator_InternalAlloc_bump_allocator` | 0x5e434..0x5e580 | __sanitizer::LowLevelAllocator::Allocate(unsigned long) at 0x5e434, 332 B | InternalAlloc: __sanitizer::InternalAlloc at 0x5e23c | InternalAlloc: none | no | no | no | no | not counted, the label names a function: LowLevelAllocator true (in the held name); bump - (not shown); allocator true (in the held name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 27 | `AllocatorMayReturnNull` | 0x5e620..0x5e630 | __sanitizer::IsRssLimitExceeded() at 0x5e620, 16 B | AllocatorMayReturnNull: __sanitizer::AllocatorMayReturnNull() at 0x5e5f8 | AllocatorMayReturnNull: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 28 | `IncreaseTotalMmap` | 0x6030c..0x60330 | __sanitizer::DecreaseTotalMmap(unsigned long) at 0x6030c, 36 B | IncreaseTotalMmap: __sanitizer::IncreaseTotalMmap(unsigned long) at 0x602c8 | IncreaseTotalMmap: d | no | no | no | store 0x134a78 at 0x602e0, load at 0x60328 | no words | removed: the name after the prefix is false, in the sixth run: IncreaseTotalMmap: __sanitizer::IncreaseTotalMmap(unsigned long) at 0x602c8; the value is in __sanitizer::DecreaseTotalMmap(unsigned long) at 0x6030c, a different function; there is no suffix; the fifth run kept it by (d) |
| 29 | `sanitizer_free_hook_weak_default` | 0x609a4..0x609ac | __sanitizer_ignore_free_hook at 0x609a4, 8 B | sanitizer_free_hook: __sanitizer_free_hook at 0x609ac | sanitizer_free_hook: none | no | no | no | no | not counted, the label names a function: weak true (weak symbol); default - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 30 | `sanitizer_ignore_free_hook_weak_default_ret_0` | 0x609ac..0x609b0 | __sanitizer_free_hook at 0x609ac, 4 B | sanitizer_ignore_free_hook: __sanitizer_ignore_free_hook at 0x609a4 | sanitizer_ignore_free_hook: none | no | no | no | no | not counted, the label names a function: weak true (weak symbol); default - (not shown); ret true (last instruction ret) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 31 | `ReportFile_SetReportPath` | 0x6153c..0x61680 | __sanitizer::CommonFlags::SetDefaults() at 0x6153c, 324 B | ReportFile_SetReportPath: __sanitizer::ReportFile::SetReportPath(char const*) at 0x60ce8 | ReportFile_SetReportPath: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 32 | `FlagParser_ParseString_parse_flags` | 0x619d0..0x62c74 | __sanitizer::RegisterCommonFlags(__sanitizer::FlagParser*, __sanitizer::CommonFlags*) at 0x619d0, 4772 B | FlagParser_ParseString: __sanitizer::FlagParser::ParseString(char const*, char const*) at 0x635a0, 2 inline records; parse_flags: 3 inline records | FlagParser_ParseString: none; parse_flags: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 33 | `FlagParser_PrintFlagDescriptions_gate_Verbosity` | 0x62c74..0x62c98 | __sanitizer::InitializeCommonFlags(__sanitizer::CommonFlags*) at 0x62c74, 36 B | FlagParser_PrintFlagDescriptions: __sanitizer::FlagParser::PrintFlagDescriptions() at 0x6302c; Verbosity: 80 inline records | FlagParser_PrintFlagDescriptions: none; Verbosity: none | no | no | no | no | not counted, the label names a function: gate - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 34 | `internal_strcmp` | 0x63c98..0x63ccc | __sanitizer::internal_strchr(char const*, int) at 0x63c98, 52 B | internal_strcmp: __sanitizer::internal_strcmp(char const*, char const*) at 0x63d54 | internal_strcmp: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 35 | `internal_strncmp` | 0x63d54..0x63d98 | __sanitizer::internal_strcmp(char const*, char const*) at 0x63d54, 68 B | internal_strncmp: __sanitizer::internal_strncmp(char const*, char const*, unsigned long) at 0x63d98 | internal_strncmp: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 36 | `internal_strchr` | 0x63d98..0x63de4 | __sanitizer::internal_strncmp(char const*, char const*, unsigned long) at 0x63d98, 76 B | internal_strchr: __sanitizer::internal_strchr(char const*, int) at 0x63c98, 2 inline records | internal_strchr: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 37 | `GetNamedMappingFd_ReadProcess_openat_getdents64` | 0x64c90..0x6508c | __sanitizer::ThreadLister::ListThreads(__sanitizer::InternalMmapVector<unsigned long long>*) at 0x64c90, 1020 B | GetNamedMappingFd: __sanitizer::GetNamedMappingFd(char const*, unsigned long, int*) at 0x66790 | GetNamedMappingFd: none | no | no | no | no | not counted, the label names a function: ReadProcess - (not shown); openat - (not shown); getdents64 - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 38 | `internal_sigaction_syscall_wrapper_selector` | 0x6562c..0x65688 | __sanitizer::GetHandleSignalMode(int) at 0x6562c, 92 B | internal_sigaction: __sanitizer::internal_sigaction(int, void const*, void*) at 0x6c4e4; syscall: syscall at 0x8f15c | internal_sigaction: none; syscall: none | no | no | no | no | not counted, the label names a function: wrapper - (not shown); selector - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 39 | `internal_errno_mapping_helper` | 0x65aa8..0x65ab4 | __sanitizer::ErrorIsOOM(int) at 0x65aa8, 12 B | none | no names | no | no | no | no | no: internal - (not shown); errno - (not shown); mapping - (not shown); helper - (not shown) | removed: the label names no function, and (e) showed no word true |
| 40 | `MmapFixedNoAccess_3_insn_arg_shim_0x65c98` | 0x660f0..0x660fc | __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) at 0x660f0, 12 B | MmapFixedNoAccess: __sanitizer::MmapFixedNoAccess(unsigned long, unsigned long, char const*) at 0x6e300, 1 inline records | MmapFixedNoAccess: none | no | no | no | no | not counted, the label names a function: 3_insn true (3 instructions); arg - (not shown); shim true (3 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 41 | `MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co` | 0x66274..0x66280 | __sanitizer::MmapFixedOrDieOnFatalError(unsigned long, unsigned long, char const*) at 0x66274, 12 B | MmapFixedSuperNoReserve: __sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*) at 0x6e1d4; MmapFixed: 1 inline records | MmapFixedSuperNoReserve: none; MmapFixed: none | no | no | no | no | not counted, the label names a function: 3_insn true (3 instructions); shim true (3 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 42 | `DTLS_Destroy_ForEachDVT_no_op_4_insns` | 0x69acc..0x69adc | __sanitizer::DTLS_Get() at 0x69acc, 16 B | DTLS_Destroy: __sanitizer::DTLS_Destroy() at 0x69588; ForEachDVT: 2 inline records | DTLS_Destroy: none; ForEachDVT: none | no | no | no | no | not counted, the label names a function: no_op false (4 instructions, 0 stores, 0 calls); 4_insns true (4 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 43 | `InternalAllocatorLock_Unlock_or_stats_add_17_ins` | 0x69d18..0x69d5c | __sanitizer::ThreadContextBase::ThreadContextBase(unsigned int) at 0x69d18, 68 B | Unlock: __sanitizer::ScopedErrorReportLock::Unlock() at 0x79250, 104 inline records; stats: 1 inline records; add: libunwind::DwarfFDECache::add at 0x84d4c, 2 inline records | Unlock: none; stats: none; add: none | no | no | no | no | not counted, the label names a function: InternalAllocatorLock - (not shown); 17_ins true (17 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 44 | `ThreadContextBase_ctor_ThreadRegistry_init_helpe` | 0x69d5c..0x69dbc | __sanitizer::ThreadRegistry::ThreadRegistry(__sanitizer::ThreadContextBase* (*)(unsigned int)) at 0x69d5c, 96 B | ThreadContextBase: __sanitizer::ThreadContextBase::ThreadContextBase(unsigned int) at 0x69d18; ThreadRegistry_init: 1 inline records | ThreadContextBase: none; ThreadRegistry_init: none | no | no | no | no | not counted, the label names a function: ctor true (constructor or init_array entry); helpe - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 45 | `ThreadRegistry_ThreadArgRetval_vector_growth` | 0x6ae20..0x6af24 | __sanitizer::InternalMmapVectorNoCtor::Realloc at 0x6ae20, 260 B | ThreadRegistry_ThreadArgRetval: 15 inline records | ThreadRegistry_ThreadArgRetval: none | no | no | no | no | not counted, the label names a function: vector true (in the held name); growth - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 46 | `weak_default_hook_ret_2` | 0x6c7e0..0x6c7e4 | __sanitizer::InitTlsSize() at 0x6c7e0, 4 B | none | no names | no | no | no | no | no: weak false (no weak symbol); default - (not shown); hook - (not shown); ret true (last instruction ret) | removed: the label names no function, and (e) showed a word false |
| 47 | `GetThreadStackAndTls` | 0x6c7e4..0x6cbd4 | __sanitizer::GetTls(unsigned long*, unsigned long*) at 0x6c7e4, 1008 B | GetThreadStackAndTls: __sanitizer::GetThreadStackAndTls at 0x6cbd4 | GetThreadStackAndTls: c | no | no | call 0x6cc14 from __sanitizer::GetThreadStackAndTls | no | no words | removed: the name after the prefix is false, in the sixth run: GetThreadStackAndTls: __sanitizer::GetThreadStackAndTls at 0x6cbd4; the value is in __sanitizer::GetTls(unsigned long*, unsigned long*) at 0x6c7e4, a different function; there is no suffix; the fifth run kept it by (c) |
| 48 | `weak_default_hook_ret_3` | 0x6d350..0x6d354 | __sanitizer::InitializePlatformCommonFlags(__sanitizer::CommonFlags*) at 0x6d350, 4 B | none | no names | no | no | no | no | no: weak false (no weak symbol); default - (not shown); hook - (not shown); ret true (last instruction ret) | removed: the label names no function, and (e) showed a word false |
| 49 | `SetShadowRegionHugePageMode_DontDumpShadow_madvi` | 0x6d888..0x6d8a8 | __sanitizer::DontDumpShadowMemory(unsigned long, unsigned long) at 0x6d888, 32 B | SetShadowRegionHugePageMode: 1 inline records | SetShadowRegionHugePageMode: none | no | no | no | no | not counted, the label names a function: DontDumpShadow true (in the held name); madvi - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 50 | `internal_pthread_weak_stub_ret` | 0x6d994..0x6d998 | __sanitizer::Atexit(void (*)()) at 0x6d994, 4 B | none | no names | no | no | no | no | no: internal - (not shown); pthread - (not shown); weak false (no weak symbol); stub true (1 instructions); ret false (last instruction j) | removed: the label names no function, and (e) showed a word false |
| 51 | `MmapFixedNoReserve` | 0x6e1d4..0x6e234 | __sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*) at 0x6e1d4, 96 B | MmapFixedNoReserve: __sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*) at 0x6e0a4 | MmapFixedNoReserve: c | no | no | call 0x6e1f0 to __sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*) | no | no words | removed: the name after the prefix is false, in the sixth run: MmapFixedNoReserve: __sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*) at 0x6e0a4; the value is in __sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*) at 0x6e1d4, a different function; there is no suffix; the fifth run kept it by (c) |
| 52 | `MprotectNoAccess` | 0x6e314..0x6e334 | __sanitizer::MmapNoAccess(unsigned long) at 0x6e314, 32 B | MprotectNoAccess: __sanitizer::MprotectNoAccess(unsigned long, unsigned long) at 0x66280 | MprotectNoAccess: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 53 | `MmapFixedOrDie` | 0x6e480..0x6e490 | __sanitizer::ReservedAddressRange::MapOrDie(unsigned long, unsigned long, char const*) at 0x6e480, 16 B | MmapFixedOrDie: __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) at 0x660f0 | MmapFixedOrDie: c | no | no | jump 0x6e48c to __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) | no | no words | removed: the name after the prefix is false, in the sixth run: MmapFixedOrDie: __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) at 0x660f0; the value is in __sanitizer::ReservedAddressRange::MapOrDie(unsigned long, unsigned long, char const*) at 0x6e480, a different function; there is no suffix; the fifth run kept it by (c) |
| 54 | `MaybeStartBackgroudThread` | 0x6fc88..0x6fccc | __sanitizer::InitializeCoverage(bool, char const*) at 0x6fc88, 68 B | MaybeStartBackgroudThread: 1 inline records | MaybeStartBackgroudThread: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 55 | `Atexit_internal_exit_hook_runner_12_insns_execut` | 0x6fccc..0x6fcfc | __sanitizer_cov_dump at 0x6fccc, 48 B | Atexit: __sanitizer::Atexit(void (*)()) at 0x6d994; internal_exit: __sanitizer::internal__exit(int) at 0x645a8 | Atexit: none; internal_exit: none | no | no | no | no | not counted, the label names a function: hook - (not shown); runner - (not shown); 12_insns true (12 instructions); execut - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 56 | `StackDepotBase_find_bucket_chain_walk` | 0x72ec0..0x72f50 | __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72ec0, 144 B | StackDepotBase_find: __sanitizer::StackDepotBase::find at 0x72e0c, 4 inline records | StackDepotBase_find: none | no | no | no | no | not counted, the label names a function: bucket - (not shown); chain - (not shown); walk - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 57 | `StackDepotBase_lock_bucket_spin_lock` | 0x72f50..0x73050 | __sanitizer::TwoLevelMap::Create at 0x72f50, 256 B | StackDepotBase_lock: __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72ec0; lock: __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72ec0, __lock at 0x94ee4 | StackDepotBase_lock: none; lock: none | no | no | no | no | not counted, the label names a function: bucket - (not shown); spin - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 58 | `Unwind_GetIP_slow_unwind_helper` | 0x79c10..0x79e84 | __sanitizer::BufferedStackTrace::UnwindSlow(unsigned long, void*, unsigned int) at 0x79c10, 628 B | Unwind_GetIP: _Unwind_GetIP at 0x84564, 1 inline records | Unwind_GetIP: none | no | no | no | no | not counted, the label names a function: slow true (in the held name); unwind true (in the held name); helper - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 59 | `lsan_flags_init_helper` | 0x7a1b0..0x7a1f4 | __lsan::Flags::SetDefaults() at 0x7a1b0, 68 B | init: __asan_init at 0x59ad4, __sanitizer::ListOfModules::init() at 0x6cca4, dummy at 0x8a3dc, 1 inline records | init: none | no | no | no | no | not counted, the label names a function: lsan true (in the held name); flags true (in the held name); helper - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 60 | `lsan_ubsan_default_options_weak_stub` | 0x7d068..0x7d074 | __lsan_default_options at 0x7d068, 12 B | ubsan_default_options: __ubsan_default_options at 0x80254 | ubsan_default_options: none | no | no | no | no | not counted, the label names a function: lsan true (in the held name); weak true (weak symbol); stub true (3 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 61 | `asan_malloc_hook_RunMallocHooks_target_sanitizer` | 0x7fc2c..0x7fc44 | __lsan::DisabledInThisThread() at 0x7fc2c, 24 B | asan_malloc: __asan::asan_malloc(unsigned long, __sanitizer::BufferedStackTrace*) at 0x31ba0; malloc_hook: __sanitizer_malloc_hook at 0x608f4; RunMallocHooks: __sanitizer::RunMallocHooks(void*, unsigned long) at 0x6083c; sanitizer: __sanitizer_get_allocated_size at 0x32e00, __sanitizer_get_allocated_begin at 0x32eec, __sanitizer::SizeClassAllocator64::Init at 0x32f48, 535 more symbols, 5 inline records | asan_malloc: none; malloc_hook: none; RunMallocHooks: none; sanitizer: none | no | no | no | no | not counted, the label names a function: target - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 62 | `fini_stub_ret` | 0x8ace0..0x8ace4 | __cxa_finalize at 0x8ace0, 4 B | fini: dummy at 0x8adac | fini: none | no | no | no | no | not counted, the label names a function: stub true (1 instructions); ret true (last instruction ret) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 63 | `libc_exit_fini_array_walker_stub` | 0x8ada8..0x8adac | call at 0x8ada8, 4 B | libc_exit_fini: libc_exit_fini at 0x8adb0 | libc_exit_fini: none | no | no | no | no | not counted, the label names a function: array - (not shown); walker - (not shown); stub true (1 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 64 | `musl_exit_helper_stub` | 0x8adac..0x8adb0 | dummy at 0x8adac, 4 B | exit: __wrap__exit at 0x421e0, __interceptor__exit at 0x466ac, exit at 0x8adfc, 1 more symbols | exit: none | no | no | no | no | not counted, the label names a function: musl - (not shown); helper - (not shown); stub true (1 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 65 | `fprintf` | 0x9049c..0x90500 | dprintf at 0x9049c, 100 B | fprintf: __wrap_fprintf at 0x421c8, __interceptor_fprintf at 0x459a8 | fprintf: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 66 | `syscall_cp_c_tail_sccp_9_insns` | 0x95208..0x9522c | __tls_get_addr at 0x95208, 36 B | syscall_cp_c: sccp at 0x951e0; sccp: sccp at 0x951e0 | syscall_cp_c: none; sccp: none | no | no | no | no | not counted, the label names a function: tail - (not shown); 9_insns true (9 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 67 | `lock_unlock_pair_user_futex` | 0x969dc..0x96a80 | __pthread_rwlock_unlock at 0x969dc, 164 B | lock: __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72ec0, __lock at 0x94ee4; unlock: __unlock at 0x9516c, 3 inline records | lock: none; unlock: none | no | no | no | no | not counted, the label names a function: pair - (not shown); user - (not shown); futex - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 68 | `pthread_key_atfork_tsd_table_init_11_insns` | 0x96b9c..0x96bc8 | __pthread_rwlock_trywrlock at 0x96b9c, 44 B | init: __asan_init at 0x59ad4, __sanitizer::ListOfModules::init() at 0x6cca4, dummy at 0x8a3dc, 1 inline records | init: none | no | no | no | no | not counted, the label names a function: pthread true (in the held name); key - (not shown); atfork - (not shown); tsd - (not shown); table - (not shown); 11_insns true (11 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |

## The removed labels of lib/ReusableB/YB1w.v, image B

| # | label | cell | held | names | names_shown | (a) symbol | (b) inlined | (c) call | (d) value | (e) words | why |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `QuarantineCache_DequeueBatch` | 0x339f4..0x33b78 | __sanitizer::QuarantineCache::MergeBatches at 0x339f4, 388 B | QuarantineCache_DequeueBatch: 2 inline records | QuarantineCache_DequeueBatch: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 2 | `LargeMmapAllocator_EnsureSortedChunks` | 0x373e0..0x374dc | __sanitizer::LargeMmapAllocator::ForEachChunk at 0x373e0, 252 B | LargeMmapAllocator_EnsureSortedChunks: __sanitizer::LargeMmapAllocator::EnsureSortedChunks at 0x37288 | LargeMmapAllocator_EnsureSortedChunks: c | no | no | call 0x3740c to __sanitizer::LargeMmapAllocator::EnsureSortedChunks | no | no words | removed: the name after the prefix is false, in the sixth run: LargeMmapAllocator_EnsureSortedChunks: __sanitizer::LargeMmapAllocator::EnsureSortedChunks at 0x37288; the value is in __sanitizer::LargeMmapAllocator::ForEachChunk at 0x373e0, a different function; there is no suffix; the fifth run kept it by (c) |
| 3 | `asan_register_globals` | 0x40130..0x4019c | __asan_register_elf_globals at 0x40130, 108 B | asan_register_globals: __asan_register_globals at 0x3ed48 | asan_register_globals: c | no | no | call 0x40164 to __asan_register_globals | no | no words | removed: the name after the prefix is false, in the sixth run: asan_register_globals: __asan_register_globals at 0x3ed48; the value is in __asan_register_elf_globals at 0x40130, a different function; there is no suffix; the fifth run kept it by (c) |
| 4 | `asan_unregister_globals` | 0x4019c..0x40204 | __asan_unregister_elf_globals at 0x4019c, 104 B | asan_unregister_globals: __asan_unregister_globals at 0x3fb64 | asan_unregister_globals: c | no | no | call 0x401d0 to __asan_unregister_globals | no | no words | removed: the name after the prefix is false, in the sixth run: asan_unregister_globals: __asan_unregister_globals at 0x3fb64; the value is in __asan_unregister_elf_globals at 0x4019c, a different function; there is no suffix; the fifth run kept it by (c) |
| 5 | `RoundUpTo_size_CHECK_helper_sanitizer_common_h_C` | 0x41570..0x416c0 | __sanitizer::RoundUpToPowerOfTwo(unsigned long) at 0x41570, 336 B | RoundUpTo: 92 inline records; size: 118 inline records | RoundUpTo: none; size: none | no | no | no | no | not counted, the label names a function: CHECK - (not shown); helper - (not shown); sanitizer true (in the held name); common true (in the file name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 6 | `memcmp_2` | 0x42208..0x4220c | __wrap_bcmp at 0x42208, 4 B | memcmp: __wrap_memcmp at 0x42204, __interceptor_memcmp at 0x43858, memcmp at 0x948d0 | memcmp: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 7 | `vfprintf_2` | 0x42230..0x42234 | __wrap_fprintf at 0x42230, 4 B | vfprintf: __wrap_vfprintf at 0x42228, __interceptor_vfprintf at 0x45644, vfprintf at 0x9113c, 1 inline records | vfprintf: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 8 | `icpt_vfprintf_2` | 0x45a10..0x45ae8 | __interceptor_fprintf at 0x45a10, 216 B | icpt_vfprintf: __interceptor_vfprintf at 0x45644, 1 inline records | icpt_vfprintf: b | no | ___interceptor_vfprintf 88 B | no | no | no words | removed: the name after the prefix is false, in the sixth run: icpt_vfprintf: __interceptor_vfprintf at 0x45644; the value is in __interceptor_fprintf at 0x45a10, a different function; the suffix 2 states no relation; the fifth run kept it by (b) |
| 9 | `icpt_diouxXn` | 0x47d40..0x47ed8 | format_get_value_size(char, char const*, bool) at 0x47d40, 408 B | none | no names | no | no | no | no | no: icpt - (not shown); diouxXn - (not shown) | removed: the label names no function, and (e) showed no word true |
| 10 | `InitializeSignalInterceptors_or_syscall_hooks` | 0x5175c..0x518b8 | __sanitizer::Sort at 0x5175c, 348 B | InitializeSignalInterceptors: 1 inline records; syscall: syscall at 0x8f448 | InitializeSignalInterceptors: none; syscall: none | no | no | no | no | not counted, the label names a function: hooks - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 11 | `AsanCheckIncompatibleRT` | 0x52aa4..0x52aa8 | __asan::AsanCheckDynamicRTPrereqs() at 0x52aa4, 4 B | AsanCheckIncompatibleRT: __asan::AsanCheckIncompatibleRT() at 0x52aa8 | AsanCheckIncompatibleRT: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 12 | `AsanCheckDynamicRTPrereqs` | 0x52aa8..0x52c10 | __asan::AsanCheckIncompatibleRT() at 0x52aa8, 360 B | AsanCheckDynamicRTPrereqs: __asan::AsanCheckDynamicRTPrereqs() at 0x52aa4 | AsanCheckDynamicRTPrereqs: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 13 | `icpt_cfree_or_DlsymFree` | 0x52f44..0x53010 | __sanitizer::DlSymAllocator<DlsymAlloc>::Allocate(unsigned long, unsigned long) at 0x52f44, 204 B | none | no names | no | no | no | no | no: icpt - (not shown); cfree - (not shown); DlsymFree - (not shown) | removed: the label names no function, and (e) showed no word true |
| 14 | `HeapProfile_Insert_asan_memory_profile` | 0x5343c..0x535a8 | __asan::HeapProfile::Print(unsigned long, unsigned long) at 0x5343c, 364 B | HeapProfile_Insert: __asan::HeapProfile::Insert(unsigned int, unsigned long) at 0x537ac | HeapProfile_Insert: none | no | no | no | no | not counted, the label names a function: asan true (in the held name); memory true (in the file name); profile true (in the held name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 15 | `asan_poison_stack_memory_PoisonAlignedStackMemor` | 0x540ec..0x5428c | __asan_poison_memory_region at 0x540ec, 416 B | asan_poison_stack_memory: __asan_poison_stack_memory at 0x548b8; PoisonAlignedStackMemor: 2 inline records | asan_poison_stack_memory: none; PoisonAlignedStackMemor: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 16 | `asan_unpoison_stack_memory` | 0x5428c..0x5440c | __asan_unpoison_memory_region at 0x5428c, 384 B | asan_unpoison_stack_memory: __asan_unpoison_stack_memory at 0x54954 | asan_unpoison_stack_memory: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 17 | `SealedTopOfMemory_check` | 0x59bd4..0x59c38 | __asan::CheckSealedAddressSpace() at 0x59bd4, 100 B | SealedTopOfMemory: 1 inline records | SealedTopOfMemory: none | no | no | no | no | not counted, the label names a function: check true (in the held name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 18 | `asan_handle_no_return_tiny_rtl_stub_2_insns` | 0x59dac..0x59db4 | __asan::OnLowLevelAllocate(unsigned long, unsigned long) at 0x59dac, 8 B | asan_handle_no_return: __asan_handle_no_return at 0x599d4 | asan_handle_no_return: none | no | no | no | no | not counted, the label names a function: tiny true (2 instructions); rtl true (in the file name); stub true (2 instructions); 2_insns true (2 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 19 | `IsStackTraceSuppressed` | 0x5b75c..0x5b8a8 | __asan::IsAddrSuppressed(char const*, __sanitizer::Symbolizer*, unsigned long) at 0x5b75c, 332 B | IsStackTraceSuppressed: __asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*) at 0x5b984 | IsStackTraceSuppressed: c | no | no | call 0x5bab0 from __asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*) | no | no words | removed: the name after the prefix is false, in the sixth run: IsStackTraceSuppressed: __asan::IsStackTraceSuppressed(__sanitizer::StackTrace const*) at 0x5b984; the value is in __asan::IsAddrSuppressed(char const*, __sanitizer::Symbolizer*, unsigned long) at 0x5b75c, a different function; there is no suffix; the fifth run kept it by (c) |
| 20 | `asan_thread_tiny_getter_3_insns` | 0x5bb34..0x5bb40 | __asan::AsanThreadContext::OnCreated(void*) at 0x5bb34, 12 B | none | no names | no | no | no | no | no: asan true (in the held name); thread true (in the held name); tiny true (3 instructions); getter false (2 stores, 0 calls, first store 0x5bb34); 3_insns true (3 instructions) | removed: the label names no function, and (e) showed a word false |
| 21 | `AsanThread_SetThreadStackAndTls` | 0x5c0f0..0x5c294 | __asan::AsanThread::ClearShadowForThreadStackAndTLS() at 0x5c0f0, 420 B | AsanThread_SetThreadStackAndTls: __asan::AsanThread::SetThreadStackAndTls(__asan::AsanThread::InitOptions const*) at 0x5c968 | AsanThread_SetThreadStackAndTls: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 22 | `AsanThread_ClearShadowForThreadStackAndTLS` | 0x5c968..0x5ca74 | __asan::AsanThread::SetThreadStackAndTls(__asan::AsanThread::InitOptions const*) at 0x5c968, 268 B | AsanThread_ClearShadowForThreadStackAndTLS: __asan::AsanThread::ClearShadowForThreadStackAndTLS() at 0x5c0f0 | AsanThread_ClearShadowForThreadStackAndTLS: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 23 | `weak_default_hook_ret` | 0x5dcac..0x5dcb0 | __sanitizer::ThreadContextBase::OnStarted(void*) at 0x5dcac, 4 B | none | no names | no | no | no | no | no: weak false (no weak symbol); default - (not shown); hook - (not shown); ret true (last instruction ret) | removed: the label names no function, and (e) showed a word false |
| 24 | `InternalAlloc_RawInternalAlloc` | 0x5dcb8..0x5def8 | __asan::GetAsanThreadContext(unsigned int) at 0x5dcb8, 576 B | InternalAlloc: __sanitizer::InternalAlloc at 0x5e2a4; RawInternalAlloc: 1 inline records | InternalAlloc: none; RawInternalAlloc: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 25 | `internal_allocator_getter` | 0x5e490..0x5e49c | __sanitizer::GetGlobalLowLevelAllocator() at 0x5e490, 12 B | internal_allocator: __sanitizer::internal_allocator() at 0x5e14c | internal_allocator: none | no | no | no | no | not counted, the label names a function: getter true (0 stores, 0 calls) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 26 | `LowLevelAllocator_InternalAlloc_bump_allocator` | 0x5e49c..0x5e5e8 | __sanitizer::LowLevelAllocator::Allocate(unsigned long) at 0x5e49c, 332 B | InternalAlloc: __sanitizer::InternalAlloc at 0x5e2a4 | InternalAlloc: none | no | no | no | no | not counted, the label names a function: LowLevelAllocator true (in the held name); bump - (not shown); allocator true (in the held name) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 27 | `AllocatorMayReturnNull` | 0x5e688..0x5e698 | __sanitizer::IsRssLimitExceeded() at 0x5e688, 16 B | AllocatorMayReturnNull: __sanitizer::AllocatorMayReturnNull() at 0x5e660 | AllocatorMayReturnNull: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 28 | `IncreaseTotalMmap` | 0x60374..0x60398 | __sanitizer::DecreaseTotalMmap(unsigned long) at 0x60374, 36 B | IncreaseTotalMmap: __sanitizer::IncreaseTotalMmap(unsigned long) at 0x60330 | IncreaseTotalMmap: d | no | no | no | store 0x134d78 at 0x60348, load at 0x60390 | no words | removed: the name after the prefix is false, in the sixth run: IncreaseTotalMmap: __sanitizer::IncreaseTotalMmap(unsigned long) at 0x60330; the value is in __sanitizer::DecreaseTotalMmap(unsigned long) at 0x60374, a different function; there is no suffix; the fifth run kept it by (d) |
| 29 | `sanitizer_free_hook_weak_default` | 0x60a0c..0x60a14 | __sanitizer_ignore_free_hook at 0x60a0c, 8 B | sanitizer_free_hook: __sanitizer_free_hook at 0x60a14 | sanitizer_free_hook: none | no | no | no | no | not counted, the label names a function: weak true (weak symbol); default - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 30 | `sanitizer_ignore_free_hook_weak_default_ret_0` | 0x60a14..0x60a18 | __sanitizer_free_hook at 0x60a14, 4 B | sanitizer_ignore_free_hook: __sanitizer_ignore_free_hook at 0x60a0c | sanitizer_ignore_free_hook: none | no | no | no | no | not counted, the label names a function: weak true (weak symbol); default - (not shown); ret true (last instruction ret) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 31 | `ReportFile_SetReportPath` | 0x615a4..0x616e8 | __sanitizer::CommonFlags::SetDefaults() at 0x615a4, 324 B | ReportFile_SetReportPath: __sanitizer::ReportFile::SetReportPath(char const*) at 0x60d50 | ReportFile_SetReportPath: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 32 | `FlagParser_ParseString_parse_flags` | 0x61a38..0x62cdc | __sanitizer::RegisterCommonFlags(__sanitizer::FlagParser*, __sanitizer::CommonFlags*) at 0x61a38, 4772 B | FlagParser_ParseString: __sanitizer::FlagParser::ParseString(char const*, char const*) at 0x63608, 2 inline records; parse_flags: 3 inline records | FlagParser_ParseString: none; parse_flags: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 33 | `FlagParser_PrintFlagDescriptions_gate_Verbosity` | 0x62cdc..0x62d00 | __sanitizer::InitializeCommonFlags(__sanitizer::CommonFlags*) at 0x62cdc, 36 B | FlagParser_PrintFlagDescriptions: __sanitizer::FlagParser::PrintFlagDescriptions() at 0x63094; Verbosity: 80 inline records | FlagParser_PrintFlagDescriptions: none; Verbosity: none | no | no | no | no | not counted, the label names a function: gate - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 34 | `internal_strcmp` | 0x63d00..0x63d34 | __sanitizer::internal_strchr(char const*, int) at 0x63d00, 52 B | internal_strcmp: __sanitizer::internal_strcmp(char const*, char const*) at 0x63dbc | internal_strcmp: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 35 | `internal_strncmp` | 0x63dbc..0x63e00 | __sanitizer::internal_strcmp(char const*, char const*) at 0x63dbc, 68 B | internal_strncmp: __sanitizer::internal_strncmp(char const*, char const*, unsigned long) at 0x63e00 | internal_strncmp: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 36 | `internal_strchr` | 0x63e00..0x63e4c | __sanitizer::internal_strncmp(char const*, char const*, unsigned long) at 0x63e00, 76 B | internal_strchr: __sanitizer::internal_strchr(char const*, int) at 0x63d00, 2 inline records | internal_strchr: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 37 | `GetNamedMappingFd_ReadProcess_openat_getdents64` | 0x64cf8..0x650f4 | __sanitizer::ThreadLister::ListThreads(__sanitizer::InternalMmapVector<unsigned long long>*) at 0x64cf8, 1020 B | GetNamedMappingFd: __sanitizer::GetNamedMappingFd(char const*, unsigned long, int*) at 0x667f8 | GetNamedMappingFd: none | no | no | no | no | not counted, the label names a function: ReadProcess - (not shown); openat - (not shown); getdents64 - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 38 | `internal_sigaction_syscall_wrapper_selector` | 0x65694..0x656f0 | __sanitizer::GetHandleSignalMode(int) at 0x65694, 92 B | internal_sigaction: __sanitizer::internal_sigaction(int, void const*, void*) at 0x6c54c; syscall: syscall at 0x8f448 | internal_sigaction: none; syscall: none | no | no | no | no | not counted, the label names a function: wrapper - (not shown); selector - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 39 | `internal_errno_mapping_helper` | 0x65b10..0x65b1c | __sanitizer::ErrorIsOOM(int) at 0x65b10, 12 B | none | no names | no | no | no | no | no: internal - (not shown); errno - (not shown); mapping - (not shown); helper - (not shown) | removed: the label names no function, and (e) showed no word true |
| 40 | `MmapFixedNoAccess_3_insn_arg_shim_0x65c98` | 0x66158..0x66164 | __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) at 0x66158, 12 B | MmapFixedNoAccess: __sanitizer::MmapFixedNoAccess(unsigned long, unsigned long, char const*) at 0x6e368, 1 inline records | MmapFixedNoAccess: none | no | no | no | no | not counted, the label names a function: 3_insn true (3 instructions); arg - (not shown); shim true (3 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 41 | `MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co` | 0x662dc..0x662e8 | __sanitizer::MmapFixedOrDieOnFatalError(unsigned long, unsigned long, char const*) at 0x662dc, 12 B | MmapFixedSuperNoReserve: __sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*) at 0x6e23c; MmapFixed: 1 inline records | MmapFixedSuperNoReserve: none; MmapFixed: none | no | no | no | no | not counted, the label names a function: 3_insn true (3 instructions); shim true (3 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 42 | `DTLS_Destroy_ForEachDVT_no_op_4_insns` | 0x69b34..0x69b44 | __sanitizer::DTLS_Get() at 0x69b34, 16 B | DTLS_Destroy: __sanitizer::DTLS_Destroy() at 0x695f0; ForEachDVT: 2 inline records | DTLS_Destroy: none; ForEachDVT: none | no | no | no | no | not counted, the label names a function: no_op false (4 instructions, 0 stores, 0 calls); 4_insns true (4 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 43 | `InternalAllocatorLock_Unlock_or_stats_add_17_ins` | 0x69d80..0x69dc4 | __sanitizer::ThreadContextBase::ThreadContextBase(unsigned int) at 0x69d80, 68 B | Unlock: __sanitizer::ScopedErrorReportLock::Unlock() at 0x792b8, 104 inline records; stats: 1 inline records; add: libunwind::DwarfFDECache::add at 0x85038, 2 inline records | Unlock: none; stats: none; add: none | no | no | no | no | not counted, the label names a function: InternalAllocatorLock - (not shown); 17_ins true (17 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 44 | `ThreadContextBase_ctor_ThreadRegistry_init_helpe` | 0x69dc4..0x69e24 | __sanitizer::ThreadRegistry::ThreadRegistry(__sanitizer::ThreadContextBase* (*)(unsigned int)) at 0x69dc4, 96 B | ThreadContextBase: __sanitizer::ThreadContextBase::ThreadContextBase(unsigned int) at 0x69d80; ThreadRegistry_init: 1 inline records | ThreadContextBase: none; ThreadRegistry_init: none | no | no | no | no | not counted, the label names a function: ctor true (constructor or init_array entry); helpe - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 45 | `ThreadRegistry_ThreadArgRetval_vector_growth` | 0x6ae88..0x6af8c | __sanitizer::InternalMmapVectorNoCtor::Realloc at 0x6ae88, 260 B | ThreadRegistry_ThreadArgRetval: 15 inline records | ThreadRegistry_ThreadArgRetval: none | no | no | no | no | not counted, the label names a function: vector true (in the held name); growth - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 46 | `weak_default_hook_ret_2` | 0x6c848..0x6c84c | __sanitizer::InitTlsSize() at 0x6c848, 4 B | none | no names | no | no | no | no | no: weak false (no weak symbol); default - (not shown); hook - (not shown); ret true (last instruction ret) | removed: the label names no function, and (e) showed a word false |
| 47 | `GetThreadStackAndTls` | 0x6c84c..0x6cc3c | __sanitizer::GetTls(unsigned long*, unsigned long*) at 0x6c84c, 1008 B | GetThreadStackAndTls: __sanitizer::GetThreadStackAndTls at 0x6cc3c | GetThreadStackAndTls: c | no | no | call 0x6cc7c from __sanitizer::GetThreadStackAndTls | no | no words | removed: the name after the prefix is false, in the sixth run: GetThreadStackAndTls: __sanitizer::GetThreadStackAndTls at 0x6cc3c; the value is in __sanitizer::GetTls(unsigned long*, unsigned long*) at 0x6c84c, a different function; there is no suffix; the fifth run kept it by (c) |
| 48 | `weak_default_hook_ret_3` | 0x6d3b8..0x6d3bc | __sanitizer::InitializePlatformCommonFlags(__sanitizer::CommonFlags*) at 0x6d3b8, 4 B | none | no names | no | no | no | no | no: weak false (no weak symbol); default - (not shown); hook - (not shown); ret true (last instruction ret) | removed: the label names no function, and (e) showed a word false |
| 49 | `SetShadowRegionHugePageMode_DontDumpShadow_madvi` | 0x6d8f0..0x6d910 | __sanitizer::DontDumpShadowMemory(unsigned long, unsigned long) at 0x6d8f0, 32 B | SetShadowRegionHugePageMode: 1 inline records | SetShadowRegionHugePageMode: none | no | no | no | no | not counted, the label names a function: DontDumpShadow true (in the held name); madvi - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 50 | `internal_pthread_weak_stub_ret` | 0x6d9fc..0x6da00 | __sanitizer::Atexit(void (*)()) at 0x6d9fc, 4 B | none | no names | no | no | no | no | no: internal - (not shown); pthread - (not shown); weak false (no weak symbol); stub true (1 instructions); ret false (last instruction j) | removed: the label names no function, and (e) showed a word false |
| 51 | `MmapFixedNoReserve` | 0x6e23c..0x6e29c | __sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*) at 0x6e23c, 96 B | MmapFixedNoReserve: __sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*) at 0x6e10c | MmapFixedNoReserve: c | no | no | call 0x6e258 to __sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*) | no | no words | removed: the name after the prefix is false, in the sixth run: MmapFixedNoReserve: __sanitizer::MmapFixedNoReserve(unsigned long, unsigned long, char const*) at 0x6e10c; the value is in __sanitizer::MmapFixedSuperNoReserve(unsigned long, unsigned long, char const*) at 0x6e23c, a different function; there is no suffix; the fifth run kept it by (c) |
| 52 | `MprotectNoAccess` | 0x6e37c..0x6e39c | __sanitizer::MmapNoAccess(unsigned long) at 0x6e37c, 32 B | MprotectNoAccess: __sanitizer::MprotectNoAccess(unsigned long, unsigned long) at 0x662e8 | MprotectNoAccess: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 53 | `MmapFixedOrDie` | 0x6e4e8..0x6e4f8 | __sanitizer::ReservedAddressRange::MapOrDie(unsigned long, unsigned long, char const*) at 0x6e4e8, 16 B | MmapFixedOrDie: __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) at 0x66158 | MmapFixedOrDie: c | no | no | jump 0x6e4f4 to __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) | no | no words | removed: the name after the prefix is false, in the sixth run: MmapFixedOrDie: __sanitizer::MmapFixedOrDie(unsigned long, unsigned long, char const*) at 0x66158; the value is in __sanitizer::ReservedAddressRange::MapOrDie(unsigned long, unsigned long, char const*) at 0x6e4e8, a different function; there is no suffix; the fifth run kept it by (c) |
| 54 | `MaybeStartBackgroudThread` | 0x6fcf0..0x6fd34 | __sanitizer::InitializeCoverage(bool, char const*) at 0x6fcf0, 68 B | MaybeStartBackgroudThread: 1 inline records | MaybeStartBackgroudThread: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 55 | `Atexit_internal_exit_hook_runner_12_insns_execut` | 0x6fd34..0x6fd64 | __sanitizer_cov_dump at 0x6fd34, 48 B | Atexit: __sanitizer::Atexit(void (*)()) at 0x6d9fc; internal_exit: __sanitizer::internal__exit(int) at 0x64610 | Atexit: none; internal_exit: none | no | no | no | no | not counted, the label names a function: hook - (not shown); runner - (not shown); 12_insns true (12 instructions); execut - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 56 | `StackDepotBase_find_bucket_chain_walk` | 0x72f28..0x72fb8 | __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72f28, 144 B | StackDepotBase_find: __sanitizer::StackDepotBase::find at 0x72e74, 4 inline records | StackDepotBase_find: none | no | no | no | no | not counted, the label names a function: bucket - (not shown); chain - (not shown); walk - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 57 | `StackDepotBase_lock_bucket_spin_lock` | 0x72fb8..0x730b8 | __sanitizer::TwoLevelMap::Create at 0x72fb8, 256 B | StackDepotBase_lock: __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72f28; lock: __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72f28, __lock at 0x951d0 | StackDepotBase_lock: none; lock: none | no | no | no | no | not counted, the label names a function: bucket - (not shown); spin - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 58 | `Unwind_GetIP_slow_unwind_helper` | 0x79c78..0x79eec | __sanitizer::BufferedStackTrace::UnwindSlow(unsigned long, void*, unsigned int) at 0x79c78, 628 B | Unwind_GetIP: _Unwind_GetIP at 0x84850, 1 inline records | Unwind_GetIP: none | no | no | no | no | not counted, the label names a function: slow true (in the held name); unwind true (in the held name); helper - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 59 | `lsan_flags_init_helper` | 0x7a218..0x7a25c | __lsan::Flags::SetDefaults() at 0x7a218, 68 B | init: __asan_init at 0x59b3c, __sanitizer::ListOfModules::init() at 0x6cd0c, dummy at 0x8a6c8, 1 inline records | init: none | no | no | no | no | not counted, the label names a function: lsan true (in the held name); flags true (in the held name); helper - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 60 | `lsan_ubsan_default_options_weak_stub` | 0x7d0d0..0x7d0dc | __lsan_default_options at 0x7d0d0, 12 B | ubsan_default_options: __ubsan_default_options at 0x802bc | ubsan_default_options: none | no | no | no | no | not counted, the label names a function: lsan true (in the held name); weak true (weak symbol); stub true (3 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 61 | `asan_malloc_hook_RunMallocHooks_target_sanitizer` | 0x7fc94..0x7fcac | __lsan::DisabledInThisThread() at 0x7fc94, 24 B | asan_malloc: __asan::asan_malloc(unsigned long, __sanitizer::BufferedStackTrace*) at 0x31c08; malloc_hook: __sanitizer_malloc_hook at 0x6095c; RunMallocHooks: __sanitizer::RunMallocHooks(void*, unsigned long) at 0x608a4; sanitizer: __sanitizer_get_allocated_size at 0x32e68, __sanitizer_get_allocated_begin at 0x32f54, __sanitizer::SizeClassAllocator64::Init at 0x32fb0, 535 more symbols, 5 inline records | asan_malloc: none; malloc_hook: none; RunMallocHooks: none; sanitizer: none | no | no | no | no | not counted, the label names a function: target - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 62 | `fini_stub_ret` | 0x8afcc..0x8afd0 | __cxa_finalize at 0x8afcc, 4 B | fini: dummy at 0x8b098 | fini: none | no | no | no | no | not counted, the label names a function: stub true (1 instructions); ret true (last instruction ret) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 63 | `libc_exit_fini_array_walker_stub` | 0x8b094..0x8b098 | call at 0x8b094, 4 B | libc_exit_fini: libc_exit_fini at 0x8b09c | libc_exit_fini: none | no | no | no | no | not counted, the label names a function: array - (not shown); walker - (not shown); stub true (1 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 64 | `musl_exit_helper_stub` | 0x8b098..0x8b09c | dummy at 0x8b098, 4 B | exit: __wrap__exit at 0x42248, __interceptor__exit at 0x46714, exit at 0x8b0e8, 1 more symbols | exit: none | no | no | no | no | not counted, the label names a function: musl - (not shown); helper - (not shown); stub true (1 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 65 | `fprintf` | 0x90788..0x907ec | dprintf at 0x90788, 100 B | fprintf: __wrap_fprintf at 0x42230, __interceptor_fprintf at 0x45a10 | fprintf: none | no | no | no | no | no words | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 66 | `syscall_cp_c_tail_sccp_9_insns` | 0x954f4..0x95518 | __tls_get_addr at 0x954f4, 36 B | syscall_cp_c: sccp at 0x954cc; sccp: sccp at 0x954cc | syscall_cp_c: none; sccp: none | no | no | no | no | not counted, the label names a function: tail - (not shown); 9_insns true (9 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |
| 67 | `lock_unlock_pair_user_futex` | 0x96cc8..0x96d6c | __pthread_rwlock_unlock at 0x96cc8, 164 B | lock: __sanitizer::StackDepotBase<__sanitizer::StackDepotNode, 1, 20>::lock(__sanitizer::atomic_uint32_t*) at 0x72f28, __lock at 0x951d0; unlock: __unlock at 0x95458, 3 inline records | lock: none; unlock: none | no | no | no | no | not counted, the label names a function: pair - (not shown); user - (not shown); futex - (not shown) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted |
| 68 | `pthread_key_atfork_tsd_table_init_11_insns` | 0x96e88..0x96eb4 | __pthread_rwlock_trywrlock at 0x96e88, 44 B | init: __asan_init at 0x59b3c, __sanitizer::ListOfModules::init() at 0x6cd0c, dummy at 0x8a6c8, 1 inline records | init: none | no | no | no | no | not counted, the label names a function: pthread true (in the held name); key - (not shown); atfork - (not shown); tsd - (not shown); table - (not shown); 11_insns true (11 instructions) | removed: (a) to (d) hold for none of the functions the label names; its words are not counted; the third run kept it by (e), before the narrowing |

## The gap hypotheses of YN0c, YN0e and YN0g

The gap hypotheses in `lib/Reusable/YN0c.v`, `YN0e.v` and `YN0g.v` are stated over `in_img1`
(`0x10000 <= a < 0x51000`, `lib/Reusable/YN0d.v:84`) and discharged by `in_img1_img`, where the donor bounds the
same gap by its read-write segment and discharges it by `src0_rwseg_img`. `lib/Reusable` describes the plain build,
`fuzz_identity.plain`, whose loaded segments run from 0x10000 to 0x50a58; its twins in `lib/U/Reusable` describe the
ubsan build, `fuzz_identity.ubsan`, whose loaded segments run from 0x10000 to 0x50f88. `in_img1` is the whole image
of each of those builds, not of image A or image B. The end of each build's third load segment is kept where it is
that build's own value: `0x1f000` at `lib/Reusable/YN0e.v:142` and `0x20000` at `lib/U/Reusable/YN0e.v:142`.

## The ASAN and BOTH tables of YK09, removed

`lib/Reusable/YK09.v` and `lib/ReusableB/YK09.v` ended their module `APC` with two literal `atable` records,
`ASAN` and `BOTH`, and six definitions beside them: `ASAN_TEXT_LO`, `ASAN_TEXT_N`, `asan_init`, `BOTH_TEXT_LO`,
`BOTH_TEXT_N` and `both_init`. port_addr_check (tool `45b78aaa48c3`), run on commit `8ff484b9e2e7`, flagged 150 rows
in them: 100 in `lib/Reusable/YK09.v` (run cgif-A-generated) and 50 in `lib/ReusableB/YK09.v` (run cgif-B-generated).
The 8 definitions, 22 lines in each file, are removed from both files. No other line of code changes.

- They describe neither image. Their `a_entry` is 0x4ba64 (`ASAN`) and 0x4ba54 (`BOTH`), and their `img_hi` is
  0x671000. Image A enters at 0x309b8 and image B at 0x30a20, and both end at 0x5fa000 (page-rounded); the donor's
  images enter at 0x302dc and 0x3030c and end at 0x5fb000. No plain, ubsan, asan or asan-ubsan image of the nine
  libreac fuzz targets enters at either address or ends at 0x671000.
- No proof reads them. Over the 2746 files that git tracks in this unit (`lib/` and `lib/U`, both images,
  evidence and provenance), each of the 8 names occurred in its own definition, and `ASAN` and `BOTH` also in
  `asan_init` and `both_init`; outside those definitions the only text that held any of them, before this
  removal as at this head, is the four rows of `address-cell-labels.tsv` described below. With the comments of
  the `.v` files removed, the other uses of each name number 0.
  The match is the whole Rocq identifier, so it also finds a qualified use (`APC.ASAN`), a `Notation`, an `Ltac`
  or a hint. None of the 98 files that `Require` YK09 (49 for each image) names one of them. Besides this note and
  three lines of `notice-claims.md` that record the removal (lines 62, 63 and 117), the only other text that holds
  one of the names is four rows of `address-cell-labels.tsv`: in two, the label `asan_init` names the image's
  function `__asan_init`; in two, `ASAN` is a word of the label `AsanInitFromRtl_ENSURE_ASAN_INITED`. Neither is the
  definition.
- The donor's `projects/cgif/cgif_file_fuzzer/proofs/lib/YK09.v` holds the same block byte for byte, so the port
  copied it, and the block is older than the donor. The 2026-10-18 proof bundle holds it in
  `libraries/cgif/proofs/submission-3/AgentSubmission/YK09.v`, where nothing reads it either, and holds the same
  table in `libraries/jsoncons/proofs/submission-2/AgentSubmission/AsanPlanCore.v`. That jsoncons tree, for
  `fuzz_ubjson_parser_max` on the task image of 2026-09-24, proves `asan` and `both` statements. It is the only
  tree of the bundle whose proofs also state 0x671000 as the image's top outside a copy of the table (about 160
  files, for example `hl_img_hi L = 0x671000` in `Ja0DrvLib.v`). So the third image is most likely the ASan and
  ASan+UBSan build of jsoncons `fuzz_ubjson_parser_max` from that task image. The bundle ships no binaries, so no
  value of the tables was checked against that image.

The removal made the donor notice on line 4 of each file less true: it said the file was copied with only its
module paths changed, and 22 lines of the source are now left out. `notice-claims.tsv` was generated again with
`notice_claims.py`, and only its two rows for these lines changed, from `agrees` to `omits changes` (2745 lines
of code, 2745 matched, 0 new or changed, 22 left out). The committed `notice_fix.py` (`c06d19b04f21`) then
rewrote the two lines from those rows, refused no row and changed no other line; its checks passed: 2 changed
lines with 2 rows, both files equal with comments removed, and 669 of 669 contributor lines equal to
`0a3a06762f6b` and, after the layout mapping, to `1aeda8ab8602`. Each line now reads "made from
projects/cgif/cgif_file_fuzzer/proofs/lib/YK09.v, with its module paths changed; 0 of its 2745 lines of code are
new or changed and 22 lines of the source are left out." The table generated once more differs from the one
before the removal in those two rows only, which agree, and its totals are the same.

`lib/B/Prog/reac_box_name.v:224` cites `lib/B/Prog/LLVMFuzzerTestOneInput.v:261-274` for uses of
`reac_box_name.<name>`. At the merge base and at the head before this commit no such use is in that range: they
are at 278-280 and 291, and after this commit's 4-line cut of that file's header comment at 274-276 and 287. The
citation is base text, not changed by this series.

Three comments, base text that this series did not change, still say that a core of this unit is not in the tree:
`lib/A/Prog/LLVMFuzzerTestOneInput.v:13-16`, `lib/B/IdentCloseImgB.v:12` and `lib/B/IdentStartupFacts.v:39-40`.

## The cell tfib_D_libc_progname_area_musl_bss, removed

`lib/A/AB1w.v` and `lib/ReusableB/YB1w.v` each defined `tfib_D_libc_progname_area_musl_bss`, at 0x5f81e0 in
`lib/A/AB1w.v` and at 0x5f84e0 in `lib/ReusableB/YB1w.v`. The one definition line is removed from each file. No other
line of code changes.

- Its name is false of both images. The name says `__progname`, but the value is the start of musl's `__libc`. In
  each image's twin, read as "The images" above says, `__libc` (a local object of 0x68 bytes in `.bss`) is the only
  named symbol that starts at the value. `__progname` starts 0x10 below it and `__progname_full` 0x8 below it:

  | image | the cell | `__libc` | `__progname` | `__progname_full` |
  |---|---|---|---|---|
  | A | 0x5f81e0 | 0x5f81e0, 0x68 bytes | 0x5f81d0, 8 bytes | 0x5f81d8, 8 bytes |
  | B | 0x5f84e0 | 0x5f84e0, 0x68 bytes | 0x5f84d0, 8 bytes | 0x5f84d8, 8 bytes |

  `program_invocation_short_name` and `program_invocation_name` are weak aliases at the addresses of `__progname`
  and `__progname_full`.
- No proof reads it. Over the 2746 files that git tracks in this unit (`lib/` and `lib/U`, both images, evidence
  and provenance), the name occurred only at its two definitions before this removal. The match is the whole Rocq
  identifier, so it also finds a qualified use (`AB1w.tfib_D_libc_progname_area_musl_bss`), a `Notation`, an `Ltac`
  or a hint. Besides this note and two lines of `notice-claims.md` that record the removal (lines 65 and 114), no
  text holds the name now. No `dune` file outside this unit names this unit's proof library, so no other unit can
  `Require` either file.
- A read-only measurement of every copy of this cell, each against its own unit's pinned image, made for the
  fuzz_grant series, gives the same values: `PROGNAME-CELLS.tsv`, sha256
  `b7dc1e0e90b5960ee6999a5ee239cb27e265d6b649e8031c354719a40290078d`. Its rows 15 and 16 are this unit's:
  `lib/A/AB1w.v:599`, 0x5f81e0, image A pin `c954b804786c`, and `lib/ReusableB/YB1w.v:600`, 0x5f84e0, image B pin
  `baf1a4d065e0`; each is `__libc+0x0` with `__progname` 0x10 below, verdict FALSE, 0 readers. Those line numbers
  are the cell's lines at origin/main `0586e4faa883` and at the merge base `1aeda8ab8602`; this series' earlier
  changes to the two files moved them to 544 and 545 before this commit. The table finds the cell false in all 33 of
  its copies, in 17 units, counted at origin/main `0586e4faa883`; the Limits section below counts what is left at
  this head. The cgif donor holds it too (`projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1w.v:589` and
  `projects/cgif/cgif_file_fuzzer/proofs/lib/YB1w.v:589`), so the port copied the label. fuzz_grant removed its two
  copies in `15d9654b354b`.

The removal made the donor notice on line 4 of each file false: its figures counted the removed line.
`notice-claims.tsv` was generated again with `notice_claims.py`, and only its two rows for these lines changed, from
`agrees` to `counts differ` (`lib/A/AB1w.v`: 529 lines of code, 522 matched, 7 new or changed, 90 left out;
`lib/ReusableB/YB1w.v`: 530, 523, 7 and 89). The committed `notice_fix.py` (`c06d19b04f21`) then wrote the figures
of the two lines again from those rows, refused no row and changed no other line; its checks passed: 2 changed lines
with 2 rows, both files equal with comments removed, and 669 of 669 contributor lines equal to `0a3a06762f6b` and,
after the layout mapping, to `1aeda8ab8602`. The lines then said "7 of its 529 lines of code are new or changed and 90
lines of the source are left out" (`lib/A/AB1w.v`) and "7 of its 530 lines of code are new or changed and 89 lines
of the source are left out" (`lib/ReusableB/YB1w.v`). The table generated once more differs from the one before the
removal in those two rows only, which agree, and its totals are the same.

Each file was then one line shorter: `lib/A/AB1w.v` had 569 lines, `lib/ReusableB/YB1w.v` 570.

## The cell tfib_D_environ_musl, removed

`lib/A/AB1w.v` and `lib/ReusableB/YB1w.v` each defined `tfib_D_environ_musl`, at 0x9d040 in `lib/A/AB1w.v` and at
0x9d320 in `lib/ReusableB/YB1w.v`. The one definition line is removed from each file. No other line of code changes.

- Its name is false of both images. The name says musl's `__environ`, but the value is a slot of `.got` that holds
  the address of `__environ`. In each image's twin, read as "The images" above says, no symbol starts at the value or
  holds it. The value is the slot 0xcf0 bytes into `.got`, which has 427 slots of 8 bytes. The 8 bytes of the slot,
  the same in the image and in the twin, are the address of `__environ`, a global object of 8 bytes in `.bss`. No
  other slot of `.got` holds that address:

  | image | the cell | `.got` | the 8 bytes at the cell | `__environ` |
  |---|---|---|---|---|
  | A | 0x9d040 | 0x9c350, 0xd58 bytes | 0x5d7e80 | 0x5d7e80, 8 bytes |
  | B | 0x9d320 | 0x9c630, 0xd58 bytes | 0x5d8180 | 0x5d8180, 8 bytes |

  `environ`, `_environ` and `___environ` are weak aliases at the address of `__environ`.
- It is not a slot cell with a short name. These two files name a slot of `.got` `tfib_D_GOT_<x>`, and the object
  itself `tfib_D_<x>`. Each file has 7 cells whose names start with `tfib_D_GOT_`. Each of them is a slot of `.got`,
  and each slot holds the address of an object that another cell of the same file names without `GOT_` (with the
  same words in 5 of the 7). The two images give the same pairs:

  | slot cell | the slot holds the address of | the cell of that object |
  |---|---|---|
  | `tfib_D_GOT_common_flags` | `__sanitizer::common_flags_dont_use` | `tfib_D_common_flags_dont_use_CommonFlags_struct_common` |
  | `tfib_D_GOT_flags` | `__asan::asan_flags_dont_use_directly` | `tfib_D_asan_flags_Flags_struct_flags` |
  | `tfib_D_GOT_asan_shadow_memory_dynamic_address` | `__asan_shadow_memory_dynamic_address` | `tfib_D_asan_shadow_memory_dynamic_address` |
  | `tfib_D_GOT_kMidMemBeg` | `__asan::kMidMemBeg` | `tfib_D_kMidMemBeg` |
  | `tfib_D_GOT_kMidMemEnd` | `__asan::kMidMemEnd` | `tfib_D_kMidMemEnd` |
  | `tfib_D_GOT_kHighMemEnd` | `__asan::kHighMemEnd` | `tfib_D_kHighMemEnd` |
  | `tfib_D_GOT_replace_intrin_cached` | `__asan::replace_intrin_cached` | `tfib_D_replace_intrin_cached` |

  The other 16 `tfib_D_` cells of each file are not slots. Each is the address its name says: the string `<sealed>`
  in `.rodata`, the starts of `.init_array` and `.fini_array`, and 13 objects in `.data` and `.bss`, each at the
  start of the symbol it names. So `tfib_D_environ_musl` is the only cell in `.got` whose name has no `GOT_`, and in
  the form of these files it names `__environ` itself. No cell of either file has the address of `__environ`. A slot
  cell for it would be named `tfib_D_GOT_environ`. No proof reads the cell (next item), so it is removed and not
  renamed, as the cell `tfib_D_libc_progname_area_musl_bss` above was.
- No proof reads it. Over the 2746 files that git tracks in this unit (`lib/` and `lib/U`, both images, evidence
  and provenance), the name occurred only at its two definitions before this removal. The match is the whole Rocq
  identifier, so it also finds a qualified use (`AB1w.tfib_D_environ_musl`), a `Notation`, an `Ltac` or a hint; and
  `environ_musl` is a part of no other word. Besides this note and three lines of `notice-claims.md` that record the
  removal (lines 67, 68 and 114), no text holds the name now. No line uses the cell's value in place of its name.
  0x9d040 and 0x9d320, in hex or in decimal (643136 and 643872), occur in other lines only as bounds of image memory:
  as the end of the 8 bytes of the slot below, at `lib/A/AFk1.v:757` and `:855`, `lib/A/AD1k.v:173`,
  `lib/ReusableB/YFk1.v:752` and `:850` and `lib/ReusableB/YD1k.v:174`; and as the start of a chunk of 80 bytes in
  the region `R_A2i` at `lib/A/AD2j.v:212` and `lib/ReusableB/YD2j.v:215`, a chunk whose bytes are the image's
  (`CImg`), not the cell's. Of the 5031 `dune` files that git tracks in the repository, the 8 that name this unit's
  proof library are all in this unit, so no other unit can `Require` either file.
- The cgif donor holds it too, after the same 7 `GOT_` cells:
  `projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1w.v:575` and `projects/cgif/cgif_file_fuzzer/proofs/lib/YB1w.v:575`,
  at the merge base `1aeda8ab8602` and at this head. So the port copied the label. In this unit the cell was at
  `lib/A/AB1w.v:585` and `lib/ReusableB/YB1w.v:586` at the merge base, and this series' earlier changes to the two
  files moved it to 530 and 531 before this commit.

The removal made the donor notice on line 4 of each file false: its figures counted the removed line.
`notice-claims.tsv` was generated again with `notice_claims.py`, and only its two rows for these lines changed, with
its totals, from `agrees` to `counts differ` (`lib/A/AB1w.v`: 528 lines of code, 521 matched, 7 new or changed, 91
left out; `lib/ReusableB/YB1w.v`: 529, 522, 7 and 90). The committed `notice_fix.py` (`c06d19b04f21`) then wrote the
figures of the two lines again from those rows, refused no row and changed no other line; its checks passed: 2
changed lines with 2 rows, both files equal with comments removed, and 669 of 669 contributor lines equal to
`0a3a06762f6b` and, after the layout mapping, to `1aeda8ab8602`. At commit `a115638ac412` the lines said "7 of its
528 lines of code are new or changed and 91 lines of the source are left out" (`lib/A/AB1w.v`) and "7 of its 529
lines of code are new or changed and 90 lines of the source are left out" (`lib/ReusableB/YB1w.v`). The table
generated once more differs from the one before the removal in those two rows only, which agree, and its totals are
the same.

At commit `a115638ac412` each file was one line shorter again: `lib/A/AB1w.v` had 568 lines, `lib/ReusableB/YB1w.v`
569. The notices on line 4 are above the cut. The other citations of these files by line number are lines of other
commits, so none moves:
`lib/A/AB1w.v:599` and `lib/ReusableB/YB1w.v:600` in the section above, and 585 and 586 here, are lines at the merge
base; 544 and 545 in the section above are lines before that section's commit, and 530 and 531 here are lines before
this commit. This commit moves line 115 of `notice-claims.md`, which the section on YK09 above cites, to 117, and
that citation is changed with it. The section above gave each file's length after its own removal, 569 and 570
lines, in the present tense; it now says "had".

## The nine cells removed by the sixth run

The deletion commit, whose parent is `df96aa536d49`, removed from `lib/A/AB1w.v` and `lib/ReusableB/YB1w.v` the
definition line of each of the nine labels that the sixth run moved to removed (The six runs, above):
`LargeMmapAllocator_EnsureSortedChunks`, `asan_register_globals`, `asan_unregister_globals`, `icpt_vfprintf_2`,
`IsStackTraceSuppressed`, `IncreaseTotalMmap`, `GetThreadStackAndTls`, `MmapFixedNoReserve` and `MmapFixedOrDie`.
Each line held both cells of its label, `tfib_A_<label>` and `tfib_E_<label>`, so 18 definitions left each file.
At `df96aa536d49` they were lines 65, 79, 80, 135, 226, 248, 347, 362 and 365 of `lib/A/AB1w.v`, and lines 66, 80,
81, 136, 227, 249, 348, 363 and 366 of `lib/ReusableB/YB1w.v`. With comments removed, each file at the deletion
commit differed from the file at `df96aa536d49` only by those nine lines. At `df96aa536d49` no file that git
tracks in this unit named any of the 36 cells except at its definition: the match was the whole Rocq identifier.

The removal made the donor notice on line 4 of each file false: its figures counted the removed lines.
`notice-claims.tsv` was generated again with `notice_claims.py`, and only its two rows for these lines changed, with
its totals, from `agrees` to `counts differ` (`lib/A/AB1w.v`: 519 lines of code, 512 matched, 7 new or changed, 100
left out; `lib/ReusableB/YB1w.v`: 520, 513, 7 and 99). The committed `notice_fix.py` (at `f1fab973e89f`), run on
those two rows only, then wrote the figures of the two lines again from them. It rewrote 2 rows, refused none and
routed 308 rows that are not ours without changing them; its checks passed: 2 changed lines with a row and 308 of
308 routed rows' lines unchanged, 2 of 2 changed files equal with comments removed, and 669 of 669 contributor lines
equal to `0a3a06762f6b` and, after the layout mapping, to `1aeda8ab8602`. At the deletion commit the lines said "7
of its 519 lines of code are new or changed and 100 lines of the source are left out" (`lib/A/AB1w.v`) and "7 of
its 520 lines of code are new or changed and 99 lines of the source are left out" (`lib/ReusableB/YB1w.v`). The
table generated once more differed from the one at `df96aa536d49` in those two rows only, which agreed, and its
totals were the same; it is the `notice-claims.tsv` of the deletion commit.

At the deletion commit each file was nine lines shorter: `lib/A/AB1w.v` had 559 lines, `lib/ReusableB/YB1w.v` 560.
The notices on line 4 are above the removed lines. The other citations of these files by line number in this note
are lines at other commits (599 and 600, 585 and 586, 544 and 545, 530 and 531, above), and those in
`notice-claims.md` are line 4, so none moved.

## Limits

- Other units still hold both cells. At this head, outside this unit, `tfib_D_libc_progname_area_musl_bss` is in 29
  `*1w.v` files of 15 units and `tfib_D_environ_musl` in 27 of 14, the cgif donor's two files in each count. Files
  with other names were not searched.
- 262 `lib/ReusableB` notices, `YCfn.v:4` among them, say "its addresses moved to libreac/fuzz_identity's ASan build";
  `lib/ReusableB` describes image B, the ASan+UBSan build. The words are base text. This series reworded 5 more such
  lines (`YFeu.v`, `YFfy.v`, `YFfz.v`, `YFg2.v`, `YFk0.v`); those five now say "ASan+UBSan build", measured on their addresses.
- `lib/B/IdentTopB.v:10`, base text, still calls the B core "cgif's A core relocated onto fuzz_identity.asan-ubsan",
  a claim this series cut from `lib/B/Prog/IdentEntryLink.v` and `lib/B/Prog/LLVMFuzzerTestOneInput.v`. The series
  changed lines 8, 11 and 12 of that sentence and not line 10.
- follow-up after merge (VERIFY 09:59Z): at the deletion commit, `tfib-mislabelled-cells.md` beside this note still
  said that the test keeps `asan_register_globals` and `asan_unregister_globals` by clause (c). The sixth run
  removed both labels (The six runs, above), and the deletion commit removed their cells.
- follow-up after merge (VERIFY 09:59Z): at the deletion commit, `notice-claims.md` still counted four runs of
  `notice_fix.py`. The run that wrote the figures of `lib/A/AB1w.v:4` and `lib/ReusableB/YB1w.v:4` again (The nine
  cells removed by the sixth run, above) was a fifth.
