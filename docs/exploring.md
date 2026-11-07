# Exploring the proofs

The headline result of each proof is an agreement statement: no
sanitizer-detectable error on any covered input
([statements.md](statements.md)). This page points to what the proofs show
beyond that. It covers three things: properties that the harnesses check and
that the proofs therefore prove; lemmas about what the library code computes;
and facts that memory safety needs. It also tells you how to find the
machine-generated data in a proof, so that you can skip it.

[index/PROOFS.md](../index/PROOFS.md) lists every proof. Paths that start with
`lib/` are relative to a harness's proofs folder,
`projects/<project>/<harness>/proofs/`. Paths that start with `projects/` are
relative to the root of the repository.

## Where to start in a proof

Each statement has a directory with a short `Proof.v`. It ends in a theorem
named after the statement, for example `asan_agrees_holds`, and proves it from a
theorem in `lib/`. The argument is in `lib/`. The specifications of the library
code are the readable part. They are in directories such as `lib/Spec/`,
`lib/FF/`, `lib/LibP/`, `lib/E2/Spec/` and `lib/Sj/`.

## Properties that the harnesses check

A harness may check a property of the library and end the process when the
property fails: with `assert()`, `abort()`, a trap, or a macro that calls one of
these. An agreement statement forbids every such ending, in both builds. So a
proof of an agreement statement also proves the property, on every input that
the statement covers. Three conditions apply:

- The check must end the process. A check that only prints a message, or only
  returns a value, is not proved.
- The check must be in the compiled program. A C `assert()` is removed when the
  program is built with `-DNDEBUG`. `abort()` and a trap do not depend on
  `NDEBUG`.
- The property is proved only for the path from this entry point, and only on
  the covered inputs.

These proofs prove such a check:

| entry point | what the harness checks | harness source | where the proof shows it |
|---|---|---|---|
| bzip2 `bzip2_compress_target` | Decompressing the compressor's output gives back the input: the same size and the same bytes. | `projects/bzip2/bzip2_compress_target/source/bzip2_compress_target.c:88-89` | `rt_small` (`lib/Bz/BzRT.v:215`): on the compressor's output, bzip2's decompressor returns `BZ_OK` and exactly the original bytes, in both of its memory modes. It rests on a theory of the Burrows-Wheeler transform, of Huffman code lengths and of the move-to-front coding in `lib/Bz/`. The walk of the compiled harness uses it (`lib/S0HarnBody.v:820`) and runs the compiled `memcmp` on the two buffers (`:507`), so the `assert`s are in the binary. |
| zstd `fse_read_ncount` | A table of normalized symbol counts that `FSE_writeNCount` writes reads back with `FSE_readNCount` to the same table, maximum symbol, table log and size, even with random bytes after it. The writer's bound fits the 512-byte buffer, and writing never fails. The harness ends the process with `FUZZ_ASSERT`, which does not depend on `NDEBUG`. | `projects/zstd/fse_read_ncount/source/fse_read_ncount.c:63-65,84-93` | `fseB_round_trip` (`lib/Spec/FseHarness.v:350`), used by the walk of the compiled harness (`lib/Plain/RF_fse_h_D.v:91`); `write_ncount_ok` (`lib/Spec/FseNCountRT.v:142`) for the write, and `write_bound_le_512` (`:102`) for the buffer check. |
| zstd `simple_decompress` | After a successful decompression, the content size in the frame headers is valid and equals the size produced, unless it is unknown. | `projects/zstd/simple_decompress/source/simple_decompress.c:47-48` | `decompress_ok_finder` (`lib/Spec/ZdFrameThm.v:559`): when the decoder succeeds, `ZSTD_findDecompressedSize` returns no error, and returns either "unknown" or the size produced. The walk of the compiled harness calls the compiled `ZSTD_findDecompressedSize` and closes each failing branch of the check with this theorem (`lib/Plain/RZ_harness.v:301-320`), so the check is in the binary. |
| yajl-ruby `json_fuzzer` | The parser reports an object key or the end of an object only inside an object, the end of an array only inside an array, and never an empty number. | `projects/yajl-ruby/json_fuzzer/source/json_fuzzer.c:40,49,59,70` | The invariant `stack_inv` (`lib/Spec/YajlFactsParse.v:66`) says that the harness's nesting counters equal the numbers of open objects and arrays on the parser's stack. `yparse_step_post` (`:333`) proves that every parse step that continues keeps it. `ylex_number_spec` (`lib/Spec/YajlFactsLex.v:331`) describes the number tokens that the lexer returns. |
| coturn `FuzzStunClient` | The STUN and ChannelData length functions never report a length past the end of the buffer. For TCP framing, the message length is also never less than the application length. A ChannelData length is never less than 4. The harness traps (`__builtin_trap`) when a check fails. | `projects/coturn/FuzzStunClient/source/FuzzStunClient.c:256-290` | No named lemma. For each build, an abstract-interpretation certificate, checked by computation in the kernel, shows that the code it covers returns normally from every start that the contract allows, so no trap instruction in it runs: `cert_src0_ok` (plain, `lib/VCertCheck_src0.v:5`), `cert_ub_ok`, `cert_asan_ok` and `cert_both_ok` (`lib/VCertCheck_ub.v`, `_asan.v`, `_both.v`). `lib/FContract.v:52` states the contract. |

coturn's address round trip (`FuzzStunClient.c:309-328`) decodes, encodes and
decodes again, but compares nothing, so it proves nothing more. simdjson
`fuzz_atpointer` asserts that a list it has just padded to two entries has at
least two entries (`fuzz_atpointer.cpp:22`). That is always true, so the check
proves nothing. Apart from the harnesses named
on this page, no harness with a proof makes a check beyond not crashing; for
them, the agreement statement is the whole result. The sources of the
boost-beast and boost-json harnesses are not in this repository yet.

**Checks that hold for a simple reason.** simdjson `fuzz_implementations`
parses its input with every backend that the processor supports, and aborts if
there are more than four backends, if some backends fail and others succeed,
or if two backends print different results
(`projects/simdjson/fuzz_implementations/source/fuzz_implementations.cpp:78-81,108-122`).
A riscv64 build has one backend, the portable fallback, so the two comparisons
have nothing to compare. The proof shows this: `grsi_cps` (`lib/P/Imp_gsi.v:39`,
and `lib/U/Imp_gsi.v:54` for the UBSan build) proves that
`get_runtime_supported_implementations` returns a list with exactly one entry,
the fallback backend (`grsi_R`, `lib/P/Imp_gsi.v:30`). So these checks say
nothing about whether simdjson's backends agree. The same holds for the
cross-backend comparisons of simdjson `fuzz_minifyimpl`
(`projects/simdjson/fuzz_minifyimpl/source/fuzz_minifyimpl.cpp:44-60`) and
`fuzz_utf8` (`projects/simdjson/fuzz_utf8/source/fuzz_utf8.cpp:50-76`). In the
`fuzz_utf8` proof, once the harness has built its backend list, the list holds
one entry, the fallback backend (`client_static`,
`lib/AsanW/AHarnessU_iface.v:48`, lines 57-59).

OpenSSL `hashtable` checks its hash table against a prediction table, with
`OPENSSL_assert`, which aborts on failure. A lookup of a key that was never
inserted must miss, and a hit must return the inserted value. After a flush,
no key is still marked as inserted. `foreach` and `filter` must find a key
exactly when the prediction says it is there
(`projects/openssl/hashtable/source/hashtable.c:260-273,299-301,306-334`).
`family_all` (`lib/VG/H0FamilyAll.v:17`) proves that the compiled program
prints one line per harness call and exits with status 0
(`t_target_ht`, `lib/T/hashtable/HTSpec.v:25`), so no assertion fails. But the
driver calls the harness 1 to 4 times on the same payload
(`ht_calls`, `lib/T/hashtable/HTSpec.v:19`). Each call therefore performs the
same operation on the same key. A lookup, `foreach`, `filter` or flush only
ever runs on a table that holds no entries, so these checks say little about
the hash table.

**A check proved directly.** simdjson `fuzz_minifyimpl` also asserts that
minifying never makes the output longer than the input (`fuzz_minifyimpl.cpp:33`).
Its proof states this fact about the compiled minifier itself, so it holds
whether or not the `assert` is compiled in (below).

**Checks that only print, proved anyway.** Two OpenSSL harnesses check an
arithmetic fact and only print the numbers when it fails, so no statement
covers the fact. Their proofs establish it anyway. Each proof has a
specification of the harness that marks the failure branch unreachable, and
proves that specification; in it, an unreachable branch has the precondition
`False`. Read these as facts that the proofs needed, not as guarantees of this
release.

| entry point | what the harness checks | harness source | where the proof shows it |
|---|---|---|---|
| OpenSSL `bndiv` | `BN_div` gives a quotient q and a remainder r with q·d + r = n and C's sign rules. | `projects/openssl/bndiv/source/bndiv.c:96-112` | `fuzz_one` (`lib/Spec/BnModel.v:590`) marks the failure branch unreachable (`:617-618`); `fuzz_one_wp` (`lib/Spec/BnCorrect.v:66`) proves it, with `wp` of an unreachable branch `False` (`lib/Spec/BnTree.v:89`). |
| OpenSSL `bignum` | `BN_mod_exp` and the simple reference `BN_mod_exp_simple` give the same result. | `projects/openssl/bignum/source/bignum.c:81-97` | `fuzz_one_g` (`lib/Spec/BgTree.v:24`) marks the failure branch unreachable (`:44-45`); `fuzz_one_gwp` (`lib/Spec/BgTop.v:404`) proves it, with `gwp` of an unreachable branch `False` (`lib/Spec/BgInv.v:53`). Both functions return the canonical a^p mod \|m\| (below). |

[analyses/harness-checks/checks.tsv](../analyses/harness-checks/checks.tsv)
lists the checks recorded in the facts of the statements under `projects/`.
It does not list every check on this page; for the harnesses with proofs, this
page is the complete list. Its column `text_in_binary` says whether the check's
assertion text or message was found in the binary. A check with no searchable
text shows "not found" even when it is compiled in
([README](../analyses/harness-checks/README.md)).

## Lemmas about what the code computes

To prove agreement, a proof must often know what the library code computes.
These lemmas are statements about the compiled code, or about a Rocq
specification of it that the proof links to the compiled code.

| entry point | lemma | what it says |
|---|---|---|
| double-conversion `string_to_double_fuzzer` | `mulpow10_spec`, `lib/BnMath.v:436` | `mulpow10` (`lib/BnModel.v:114`), the specification of the big-number multiplication by 10^e, multiplies the value by exactly 10^e: the 28-bit words take the factor 5^e·2^(e mod 28), and the word exponent grows by e/28. The walks of the compiled code use it, for example `lib/BnP_ads2.v:127`. |
| fast_float `from_chars` | `shl_inv`, `lib/FF/Bigint_shl.v:75` | The loop invariant of `bigint::shl_bits`: the shifted prefix plus the pending carry equals the original times 2^r. `shl_inv_finish_nocarry` (`:108`) and `shl_inv_finish_carry` (`:112`) give the result for the two ways the loop ends: exactly the original times 2^r. |
| fast_float `from_chars` | `pow10_spec`, `lib/FF/P_pow10.v:928` | The compiled `bigint::pow10(e)` meets `pow10_post` (`lib/FF/P_pow10_stmt.v:20`): it multiplies the big integer by exactly 10^e (`:36`), for e < 2048 and when the result fits. |
| libpcap `fuzz_pcap` | `adjust_snapshot_proof__body`, `lib/E2/S3/Pcap_iface__S3.v:1530` | The compiled `pcapint_adjust_snapshot` returns exactly the value of its specification (`lib/E2/Spec/PcapPure.v:41-42`), for every link type from 0 to 2^31-1 and every 32-bit snapshot length. The statement is `adjust_snapshot_stmt` (`:419`). |
| OpenSSL `punycode` | `bias_val`, `lib/LibA/UDecArith.v:122` | The bias that `adapt()` returns cannot wrap in 32-bit arithmetic, and lies in [0, 300]. |
| OpenSSL `bndiv` | `BN_div_spec`, `lib/Spec/BnDivSpec.v:299` | `BN_div` returns the quotient and remainder of the magnitudes, truncated toward zero; the quotient is negative exactly when the signs of the operands differ and it is not zero, and the remainder has the sign of the dividend. It also bounds the sizes of the results. |
| OpenSSL `bndiv` | `div_identity`, `lib/Spec/BnCorrect.v:50` | With those signs, the harness's `BN_mul` and `BN_add` give back the dividend: the signed product q·d plus the signed remainder r equals n. |
| OpenSSL `bignum` | `BN_mod_exp_spec`, `lib/Spec/BgExpWord.v:487` | `BN_mod_exp` returns a^p mod \|m\| as a canonical, non-negative big number (`exp_post`, `lib/Spec/BgExpSpec.v:28`), and the result is no longer than m. `BN_mod_exp_simple_spec` (`lib/Spec/BgExpSpec.v:293`) proves the same of the simple reference. |
| OpenSSL `bignum` | `mont_reduce_loop_spec`, `lib/Spec/BgMontCorrect.v:163` | The word-by-word Montgomery reduction loop gives T·R⁻¹ modulo N: the upper half of the result, with the final carry, times R equals T plus a multiple of N smaller than N·R. |
| jsoncons `fuzz_bigint` | `detail_ok`, `lib/L5Detail.v:468` | The compiled routine that turns a string of 1 to 4,999 decimal digits into a `bigint` writes exactly the base-2^64 words of the decimal value (`parse_post`, `lib/L5ParseSpecs.v:61`). It keeps up to two words inside the object and otherwise uses one fresh heap block. For an empty string or a non-digit, it reports the error code 22 in its second result register and leaves the number 0 (`detail_spec`, `:86`). |
| simdjson `fuzz_atpointer`, `fuzz_dump`, `fuzz_dump_raw_tape`, `fuzz_element` | `stage1_S1OUT`: `lib/Sj/Zph.v:204` in `fuzz_atpointer`, `lib/Sj/SjStage1Out.v:204` in the others | When simdjson's first pass over the input succeeds, the list of structural positions it returns is not empty, strictly increasing and inside the input, never points at white space, and each opening quote that it lists has its closing quote before the next listed position (`S1OUT`: `lib/Sj/Zpf.v:22` in `fuzz_atpointer`, `lib/Sj/SjS1Out.v:22` in the others). |
| simdjson `fuzz_minifyimpl` | `minify_proof`, `lib/Plain/PM_minify.v:366` (UBSan build: `lib/Ubsan/UM_minify.v:416`) | The compiled fallback `minify` writes only its output buffer and the result size. The size it reports lies between 0 and the input length. It returns error 15 exactly when the input ends inside an unclosed string, and 0 otherwise (`mf_post`, `lib/Plain/PM_minify.v:193`; `unclosed`, `lib/Spec/HarnessM.v:16`). |
| yajl-ruby `json_fuzzer` | `yparse_step_post`, `lib/Spec/YajlFactsParse.v:333` | Every step of yajl's parser that continues keeps the invariant `stack_inv`: the harness's nesting counters equal the numbers of open objects and arrays on the parser's stack (above). |

## What memory safety needs

An agreement proof must show that no access goes out of bounds. Some of the
facts it needs are worth reading on their own:

| entry point | lemma | what it says |
|---|---|---|
| OpenSSL `punycode` | `decode_spec`, `lib/LibP/PSpecs.v:16` | `ossl_punycode_decode` writes only its own stack frame, `out[0..max)` and `*outlen`, and on success reports `outlen <= max`. The harness calls it with `max = 16`. |
| OpenSSL `bndiv` | `BN_bin2bn_spec`, `lib/Spec/BnSpecs2.v:219` | An input of at most 256,000 bytes gives a big number of at most 32,000 64-bit words. `BN_div_spec` (above) then bounds the size of each result of the division. |
| OpenSSL `ct` | `o2i_sct_spec`, `lib/Spec/CtSpecs3.v:101` | Parsing one signed certificate timestamp from L bytes (1 ≤ L ≤ 65533) either fails and leaves the heap as it was, or returns a timestamp that owns exactly the heap blocks added for it, and whose encoding takes at most L bytes. `o2i_sct_list_spec` (`:406`) gives the same heap fact for the whole list. |
| simdjson `fuzz_dump`, `fuzz_dump_raw_tape`, `fuzz_element` | `memmove_overlap_test_w`, `lib/Sj/SjNumber.v:162` | The compiled `memmove` decides with one unsigned comparison of the addresses whether it can copy forward. When the source starts below the destination, the lemma proves that this comparison implies the source range ends at or before the start of the destination, so the two ranges do not overlap. The walk of the compiled `memmove` in `fuzz_dump` uses it (`lib/P/Sj_num_memmove.v:148`). |
| bzip2 `bzip2_compress_target` | `mtf_inv_bounds`, `lib/Bz/BzLemmasMtf.v:17` | The decoder keeps 16 move-to-front blocks of 16 entries. The base of block l (0 ≤ l < 16) lies between 1 + 16·l and 4080 − 16·(15 − l), so every block stays inside the 4096-byte array. |
| skcms `iccprofile_info` | `parse_Ub_ok`, `lib/Info/LibParseUb.v:4297` | The compiled `skcms_Parse` meets `parse_contract` (`lib/Info/LibTagsSpec.v:283`): it returns 0 or 1, and on 1 every curve table and the A2B grid that the harness reads lie inside the input buffer (`curve_ok`, `lib/Info/LibDefs.v:103`; `grid_ok_A2B`, `:141`; `parsed_ok_profile_ok`, `lib/Info/LibTagsSpec.v:243`). So the harness's reads of the first and last entries of each table are in bounds. The theorem assumes the contracts of the functions that `skcms_Parse` calls; `lib/Info/ProofInfoLib.v:1314` supplies their proofs. |

## Machine-generated data

Most of the bytes of a proof are data that a program generated, not argument.
Skip them when you read.

- Memory images are never stored. `elf-snapshot` makes them from the pinned
  ELF files at build time.
- A `*_code_<lo>_<hi>.v` file holds, for each machine instruction in its range,
  the instruction word and two lemmas: the image holds that word, and the word
  decodes to that instruction.
- `RefImg.v` and `UbImg.v` hold facts read from the program image. `VCertS_*`
  files hold certificate data.
- Files that call a `KReplay` function (`run`, `run1`, `run1z` and others) on a
  long string expand an encoded proof term. Such terms are most of the bytes of
  the boost-beast, boost-json and jsoncons `fuzz_ubjson_encoder` proofs. In
  boost-json and jsoncons `fuzz_ubjson_parser_max`, many lemma statements are
  encoded too, so you cannot read them without running Rocq.
- In the proofs made from Anthropic's proofs, the first line of a file tells you
  its kind. A file that starts with the licence header is argument. A file that
  starts with `(* This file states or restates instruction words of the task's
  compiled program` transcribes instructions.
- Statements that name code addresses (`0x…`) are usually step lemmas of a
  machine walk: argument, but mechanical.

<!-- control: docs/ is unowned, so this needs no code owner -->
