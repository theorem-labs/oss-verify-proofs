(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: the call contexts and allocation traces are omx-clap-core/fuzz_preset's own, GENERATED from image B' (the asan-ubsan build of the #102 harness, facts 8f3e7e1a07f1) in the trace-carrier form (YG00.v Univ). Tfib_fixed holds the FIXED part of the universe closure of walkkit-next f97c8b2f046b (lib/A/PRH_Base.v git blob fdb45545469b28dc7004f04c6ee7e10d1ad2845b, prh_univ_closure: its four conjuncts, the same text as K0 Batch 1's blob 361b59abafd8) together with K0's approved fifth conjunct for the frame-pointer-less callees of fp functions (forall F G c r rt q j, prh_reach CTX0 F c -> pi_fp F = true -> pi_fp G = false -> In r (pi_call_rets F G) -> In q (pi_ret_sites G rt) -> In (prh_trace (prh_pc0 rt) q (firstn j c)) U), at CTX0 = [[0x815c8]] and no data word, over lib/B/PRH_ImgB.v prh_img_B git blob 3216eca6834281dfa75d81a58da0d8ba39e4345b (pi_ret_sites, pi_call_rets, pi_fp, pi_tails), plus padded's inherited chain and the driver's traces of main and target_run: 170 traces, the 92 of a working branch ddc322f99b75 (YCej.v blob 201786a6721b) and the 78 the fifth conjunct adds. Tfib_wild holds the 3 prefixes of the per-run traces, [0x53964; 0x87f34] and [0x53964; 0x885e4] (the cursor frees of parse_items and parse_string, whose third word is a word of the run's DW) and [0x53d60; 0x8529c] (tx_put's realloc, whose third word is a fake-stack address). The allocator call sites agree with the listing of record lib/B/Listing_prog.v git blob c97cc46b3e13b53ab71ad99b1e4b1dc515f72bf5, function by function through lib/B/PAImg_prog.v git blob 15fab93fe702a1d9f611ee01c6602d6bbe336c99 (a working branch). SOURCES, sha256: pin bin/fuzz_preset/fuzz_preset.asan-ubsan d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994 (index/binaries.tsv at 8f3e7e1a07f1; the #102 pin B' (sha256 d663f82d7f48)); unstripped twin c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175 (its unstripped twin (sha256 c90d4fa54d43)). Generator: gen_traces.py (sha256 1a805d8ee52106122694c5be987a4bf0f9841865004ca72ca6cdc3f0213db913) (a Theorem Labs lane pg-core/reloc/gen_traces.py 59966c88351063828f3118687401542cb3d9512b4e218916c1b930fbdc1d0a8f with eight options added - repeated --fp, --tail, --cursor, --inherit, --univ, --wild, --callees, and --fp through a tail call; its older options give the older files byte for byte), which reads only the pin and the twin, through ycejuniv/resolve_code.py 81803218fe79932a07aa3422ff95e35208212d3b870871543062ba6beb67e6a5 (a Theorem Labs lane's, unchanged) and rvelf.py (sha256 23152d9ca11cb6287ab13e27265103520e7fb9c3816093c893f68a23f5c7dd5b). Options file: ycejuniv/make_ycej.sh 80622c3a9f131c7b13ac97236daa9715a1ebb2cc817c2c66816c4e494a197b02 (mode b102f), which holds the command below and joins its definitions to this file's lemma text with ycejuniv/assemble.py 63e0862c739e178b91de7e7b197d90f433b57f61ae7a16083b3ec249b1d7070b, reading the lemma text from ycejuniv/tail.YCej.univ.v 08c979a0617ac36101bc010b0f2928830528f92dc57964b888b943f2ace85bd8 (the trace-carrier form of a Theorem Labs lane's univcore c57efc1cefa4: Tfib_universe_ok through YG01.v univ_of_ok) and these header lines from the internal file header.b102f.txt. Control: ycejuniv/check_ycej.py 6bcd354d95ad64b8deb613d1b170942ada8702dfc870c824ee41cae5cc630a6d re-derives the demanded set (the closure's four clauses, after checking that the closure text and the definitions it uses are the text it implements; the fifth conjunct; the inherited chains; the driver's traces; the wild prefixes) from the image table, the closure text blob above and the twin (capstone, through elfdis.py (sha256 6edf458084a6a3aed114ebb3aebedd233567b56125d67e07aef31c9c6f9584ad)) and finds Tfib_fixed and Tfib_wild equal to it; the internal file make_ycej.sh runs it as a gate and refuses to write a file it fails on (a wild prefix the closure does not demand, a demanded trace missing, an extra one). Command: `the internal file gen_traces.py <pin> <twin> --univ --wild tx_put --wild parse_items --wild parse_string --callees --ipc malloc=0x53ac4 --ipc free=0x53964 --ipc realloc=0x53d60 --fp LLVMFuzzerTestOneInput=0x815c8 --fp check_no_overread=0x81818 --fp check_reject_clean_starved=0x819c0 --fp check_reject_clean_starved=0x819ec --fp check_round_trip=0x819d4 --fp round_trip_text=0x829cc --fp round_trip_text=0x829ec --fp parse_value=0x8633c --fp parse_value=0x87d98 --fp tx_string=0x85638 --fp tx_string=0x84fb8 --fp tx_string=0x856b8 --tail fuzz_free --inherit padded --cursor parse_items=0x8633c --cursor parse_string=0x8633c --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm --module OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable`. *)
(* The numerals, all read from image B': 0x53ac4 / 0x53964 / 0x53d60 are the pcs the malloc / free / realloc interceptors record (the return address of the second GetCurrentPc call of ___interceptor_malloc 0x539fc / ___interceptor_free 0x5382c / ___interceptor_realloc 0x53c24, the branch taken when malloc_context_size > 2). The second entry of each trace is a call site's return address: a jal to __interceptor_trampoline_malloc 0x53824 / _free 0x53820 / _realloc 0x53828 or to the wrappers, or a jal to fuzz_free, which ends in a tail jump to the free trampoline after restoring ra and s0 (0x86228), so the interceptor sees its caller's return site. The later entries are the return addresses the fast unwinder reads from the frame-pointer chain of the frame-pointer functions (pi_fp): check_no_overread 0x81818, check_reject_clean_starved 0x819c0 / 0x819ec and check_round_trip 0x819d4 in LLVMFuzzerTestOneInput, round_trip_text 0x829cc / 0x829ec in check_round_trip, LLVMFuzzerTestOneInput 0x815c8 in target_run (its one caller, jal 0x815c4), parse_value 0x8633c in pj_parse and 0x87d98 in parse_items, tx_string 0x85638 in tx_value and, through tx_value's tail jump to tx_string, 0x84fb8 in round_trip_text and 0x856b8 in tx_value; the chain stops at a function that does not keep its frame pointer (target_run holds the input size in s0, 0x81524 mv s0, a3). The fifth conjunct continues the site traces of each frame-pointer-less callee of a frame-pointer function with that function's contexts: check_as_written and pj_free in LLVMFuzzerTestOneInput; pj_free and padded in check_no_overread; pj_write in check_reject_clean_starved; pj_free and pj_write in check_round_trip; pj_free, pj_write and tx_put in round_trip_text; fuzz_malloc, parse_items and parse_string in parse_value; tx_put in tx_string - the callee's own return site is not in the trace. padded (0x830a8) calls malloc (0x830d0) before it writes s0, so the run itself stores [0x53ac4; 0x830d4; 0x81818; 0x815c8]. 0x8633c (the return site of pj_parse's jal parse_value) is the closure's code word for the cursor functions parse_items and parse_string (PRH_Base.v prh_univ_closure clause 4). libunwind's DwarfFDECache::add calls the wrappers too; it is excluded as the runtime's error path, as pg-core/reloc/README.md:157-171 excludes it. The lemma part is the file's own, unchanged. *)
(* OVER-APPROXIMATION (the kit owner's note, asked for at 2026-10-29 21:07Z): the fifth conjunct above, for the frame-pointer-less callees of fp callers, demands more traces than the run stores. It costs 78 of the 4096 depot slots (YG01.v DEPOT_MAX; universe_ok: length u_fix + u_wmax <= DEPOT_MAX, and univ_of sets u_wmax = 4096 - length Tfib_fixed): Tfib_fixed holds 170 traces in total, 92 before the conjunct, so the room for wild traces is 3926 and not 4004. The 78 are slack: every such callee except padded (check_as_written, pj_free, pj_write, tx_put, fuzz_malloc, parse_items and parse_string) writes s0 before its allocator call, so at that call s0 is not the fp caller's frame, the unwinder does not read the caller's chain, and the run never stores those 78 traces. padded calls malloc before it writes s0, and its traces were in the 92 already. The tight alternative is a per-function image fact as one more premise of the conjunct, `pi_keeps_s0_at_alloc G = true ->`, which would drop the 78; it is rejected because it binds the universe to each callee's instruction order. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_check_as_written : list (list Z) :=
[[0x815c8]].
Definition TRACES_check_as_written : list (list Z) :=
[[0x53ac4; 0x81fc0];
[0x53ac4; 0x81fc0; 0x815c8];
[0x53964; 0x81fec];
[0x53964; 0x81fec; 0x815c8];
[0x53964; 0x82018];
[0x53964; 0x82018; 0x815c8]].
Definition CTX_check_no_overread : list (list Z) :=
[[0x81818]].
Definition TRACES_check_no_overread : list (list Z) :=
[[0x53964; 0x81cf4];
[0x53964; 0x81cf4; 0x81818];
[0x53964; 0x81cf4; 0x81818; 0x815c8];
[0x53964; 0x81cfc];
[0x53964; 0x81cfc; 0x81818];
[0x53964; 0x81cfc; 0x81818; 0x815c8];
[0x53964; 0x81d04];
[0x53964; 0x81d04; 0x81818];
[0x53964; 0x81d04; 0x81818; 0x815c8]].
Definition CTX_check_reject_clean_starved : list (list Z) :=
[[0x819c0];
[0x819ec]].
Definition TRACES_check_reject_clean_starved : list (list Z) :=
[[0x53964; 0x822e8];
[0x53964; 0x822e8; 0x819c0];
[0x53964; 0x822e8; 0x819c0; 0x815c8];
[0x53964; 0x822e8; 0x819ec];
[0x53964; 0x822e8; 0x819ec; 0x815c8];
[0x53964; 0x823c0];
[0x53964; 0x823c0; 0x819c0];
[0x53964; 0x823c0; 0x819c0; 0x815c8];
[0x53964; 0x823c0; 0x819ec];
[0x53964; 0x823c0; 0x819ec; 0x815c8];
[0x53964; 0x824e4];
[0x53964; 0x824e4; 0x819c0];
[0x53964; 0x824e4; 0x819c0; 0x815c8];
[0x53964; 0x824e4; 0x819ec];
[0x53964; 0x824e4; 0x819ec; 0x815c8]].
Definition CTX_check_round_trip : list (list Z) :=
[[0x819d4]].
Definition TRACES_check_round_trip : list (list Z) :=
[[0x53964; 0x82b30];
[0x53964; 0x82b30; 0x819d4];
[0x53964; 0x82b30; 0x819d4; 0x815c8];
[0x53964; 0x83028];
[0x53964; 0x83028; 0x819d4];
[0x53964; 0x83028; 0x819d4; 0x815c8]].
Definition CTX_fuzz_malloc : list (list Z) :=
[[0x8633c];
[0x87d98]].
Definition TRACES_fuzz_malloc : list (list Z) :=
[[0x53ac4; 0x85d50];
[0x53ac4; 0x85d50; 0x8633c];
[0x53ac4; 0x85d50; 0x87d98]].
Definition CTX_fuzz_realloc : list (list Z) :=
[[]].
Definition TRACES_fuzz_realloc : list (list Z) :=
[[0x53d60; 0x86048]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x53ac4; 0x81280];
[0x53ac4; 0x812d4];
[0x53964; 0x812f8];
[0x53964; 0x81428]].
Definition CTX_padded : list (list Z) :=
[[0x81818]].
Definition TRACES_padded : list (list Z) :=
[[0x53ac4; 0x830d4];
[0x53ac4; 0x830d4; 0x81818];
[0x53ac4; 0x830d4; 0x81818; 0x815c8]].
Definition CTX_parse_items : list (list Z) :=
[[0x8633c];
[0x87d98]].
Definition TRACES_parse_items : list (list Z) :=
[[0x53964; 0x87f34];
[0x53964; 0x87f34; 0x8633c];
[0x53964; 0x87f34; 0x87d98]].
Definition CTX_parse_string : list (list Z) :=
[[0x8633c];
[0x87d98]].
Definition TRACES_parse_string : list (list Z) :=
[[0x53964; 0x885e4];
[0x53964; 0x885e4; 0x8633c];
[0x53964; 0x885e4; 0x87d98]].
Definition CTX_pj_free : list (list Z) :=
[[0x815c8];
[0x81818];
[0x819d4];
[0x829cc];
[0x829ec]].
Definition TRACES_pj_free : list (list Z) :=
[[0x53964; 0x86b54];
[0x53964; 0x86b54; 0x815c8];
[0x53964; 0x86b54; 0x81818];
[0x53964; 0x86b54; 0x81818; 0x815c8];
[0x53964; 0x86b54; 0x819d4];
[0x53964; 0x86b54; 0x819d4; 0x815c8];
[0x53964; 0x86b54; 0x829cc];
[0x53964; 0x86b54; 0x829cc; 0x819d4];
[0x53964; 0x86b54; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86b54; 0x829ec];
[0x53964; 0x86b54; 0x829ec; 0x819d4];
[0x53964; 0x86b54; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86b88];
[0x53964; 0x86b88; 0x815c8];
[0x53964; 0x86b88; 0x81818];
[0x53964; 0x86b88; 0x81818; 0x815c8];
[0x53964; 0x86b88; 0x819d4];
[0x53964; 0x86b88; 0x819d4; 0x815c8];
[0x53964; 0x86b88; 0x829cc];
[0x53964; 0x86b88; 0x829cc; 0x819d4];
[0x53964; 0x86b88; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86b88; 0x829ec];
[0x53964; 0x86b88; 0x829ec; 0x819d4];
[0x53964; 0x86b88; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86ba0];
[0x53964; 0x86ba0; 0x815c8];
[0x53964; 0x86ba0; 0x81818];
[0x53964; 0x86ba0; 0x81818; 0x815c8];
[0x53964; 0x86ba0; 0x819d4];
[0x53964; 0x86ba0; 0x819d4; 0x815c8];
[0x53964; 0x86ba0; 0x829cc];
[0x53964; 0x86ba0; 0x829cc; 0x819d4];
[0x53964; 0x86ba0; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86ba0; 0x829ec];
[0x53964; 0x86ba0; 0x829ec; 0x819d4];
[0x53964; 0x86ba0; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86bbc];
[0x53964; 0x86bbc; 0x815c8];
[0x53964; 0x86bbc; 0x81818];
[0x53964; 0x86bbc; 0x81818; 0x815c8];
[0x53964; 0x86bbc; 0x819d4];
[0x53964; 0x86bbc; 0x819d4; 0x815c8];
[0x53964; 0x86bbc; 0x829cc];
[0x53964; 0x86bbc; 0x829cc; 0x819d4];
[0x53964; 0x86bbc; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86bbc; 0x829ec];
[0x53964; 0x86bbc; 0x829ec; 0x819d4];
[0x53964; 0x86bbc; 0x829ec; 0x819d4; 0x815c8]].
Definition CTX_pj_write : list (list Z) :=
[[0x819c0];
[0x819d4];
[0x819ec];
[0x829cc];
[0x829ec]].
Definition TRACES_pj_write : list (list Z) :=
[[0x53964; 0x87330];
[0x53964; 0x87330; 0x819c0];
[0x53964; 0x87330; 0x819c0; 0x815c8];
[0x53964; 0x87330; 0x819ec];
[0x53964; 0x87330; 0x819ec; 0x815c8];
[0x53964; 0x87330; 0x819d4];
[0x53964; 0x87330; 0x819d4; 0x815c8];
[0x53964; 0x87330; 0x829cc];
[0x53964; 0x87330; 0x829cc; 0x819d4];
[0x53964; 0x87330; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x87330; 0x829ec];
[0x53964; 0x87330; 0x829ec; 0x819d4];
[0x53964; 0x87330; 0x829ec; 0x819d4; 0x815c8]].
Definition CTX_round_trip_text : list (list Z) :=
[[0x829cc];
[0x829ec]].
Definition TRACES_round_trip_text : list (list Z) :=
[[0x53964; 0x84fe4];
[0x53964; 0x84fe4; 0x829cc];
[0x53964; 0x84fe4; 0x829cc; 0x819d4];
[0x53964; 0x84fe4; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x84fe4; 0x829ec];
[0x53964; 0x84fe4; 0x829ec; 0x819d4];
[0x53964; 0x84fe4; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x85020];
[0x53964; 0x85020; 0x829cc];
[0x53964; 0x85020; 0x829cc; 0x819d4];
[0x53964; 0x85020; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x85020; 0x829ec];
[0x53964; 0x85020; 0x829ec; 0x819d4];
[0x53964; 0x85020; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x85028];
[0x53964; 0x85028; 0x829cc];
[0x53964; 0x85028; 0x829cc; 0x819d4];
[0x53964; 0x85028; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x85028; 0x829ec];
[0x53964; 0x85028; 0x829ec; 0x819d4];
[0x53964; 0x85028; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x8516c];
[0x53964; 0x8516c; 0x829cc];
[0x53964; 0x8516c; 0x829cc; 0x819d4];
[0x53964; 0x8516c; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x8516c; 0x829ec];
[0x53964; 0x8516c; 0x829ec; 0x819d4];
[0x53964; 0x8516c; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x85174];
[0x53964; 0x85174; 0x829cc];
[0x53964; 0x85174; 0x829cc; 0x819d4];
[0x53964; 0x85174; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x85174; 0x829ec];
[0x53964; 0x85174; 0x829ec; 0x819d4];
[0x53964; 0x85174; 0x829ec; 0x819d4; 0x815c8]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x53ac4; 0x81560];
[0x53964; 0x815f4]].
Definition CTX_tx_put : list (list Z) :=
[[0x829cc];
[0x829ec];
[0x84fb8];
[0x85638];
[0x856b8]].
Definition TRACES_tx_put : list (list Z) :=
[[0x53d60; 0x8529c];
[0x53d60; 0x8529c; 0x829cc];
[0x53d60; 0x8529c; 0x829cc; 0x819d4];
[0x53d60; 0x8529c; 0x829cc; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x829ec];
[0x53d60; 0x8529c; 0x829ec; 0x819d4];
[0x53d60; 0x8529c; 0x829ec; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x85638];
[0x53d60; 0x8529c; 0x84fb8];
[0x53d60; 0x8529c; 0x84fb8; 0x829cc];
[0x53d60; 0x8529c; 0x84fb8; 0x829cc; 0x819d4];
[0x53d60; 0x8529c; 0x84fb8; 0x829cc; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x84fb8; 0x829ec];
[0x53d60; 0x8529c; 0x84fb8; 0x829ec; 0x819d4];
[0x53d60; 0x8529c; 0x84fb8; 0x829ec; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x856b8]].
Definition Tfib_fixed : list (list Z) :=
[[0x53964];
[0x53964; 0x812f8];
[0x53964; 0x81428];
[0x53964; 0x815f4];
[0x53964; 0x81cf4];
[0x53964; 0x81cf4; 0x81818];
[0x53964; 0x81cf4; 0x81818; 0x815c8];
[0x53964; 0x81cfc];
[0x53964; 0x81cfc; 0x81818];
[0x53964; 0x81cfc; 0x81818; 0x815c8];
[0x53964; 0x81d04];
[0x53964; 0x81d04; 0x81818];
[0x53964; 0x81d04; 0x81818; 0x815c8];
[0x53964; 0x81fec];
[0x53964; 0x81fec; 0x815c8];
[0x53964; 0x82018];
[0x53964; 0x82018; 0x815c8];
[0x53964; 0x822e8];
[0x53964; 0x822e8; 0x819c0];
[0x53964; 0x822e8; 0x819c0; 0x815c8];
[0x53964; 0x822e8; 0x819ec];
[0x53964; 0x822e8; 0x819ec; 0x815c8];
[0x53964; 0x823c0];
[0x53964; 0x823c0; 0x819c0];
[0x53964; 0x823c0; 0x819c0; 0x815c8];
[0x53964; 0x823c0; 0x819ec];
[0x53964; 0x823c0; 0x819ec; 0x815c8];
[0x53964; 0x824e4];
[0x53964; 0x824e4; 0x819c0];
[0x53964; 0x824e4; 0x819c0; 0x815c8];
[0x53964; 0x824e4; 0x819ec];
[0x53964; 0x824e4; 0x819ec; 0x815c8];
[0x53964; 0x82b30];
[0x53964; 0x82b30; 0x819d4];
[0x53964; 0x82b30; 0x819d4; 0x815c8];
[0x53964; 0x83028];
[0x53964; 0x83028; 0x819d4];
[0x53964; 0x83028; 0x819d4; 0x815c8];
[0x53964; 0x84fe4];
[0x53964; 0x84fe4; 0x829cc];
[0x53964; 0x84fe4; 0x829cc; 0x819d4];
[0x53964; 0x84fe4; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x84fe4; 0x829ec];
[0x53964; 0x84fe4; 0x829ec; 0x819d4];
[0x53964; 0x84fe4; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x85020];
[0x53964; 0x85020; 0x829cc];
[0x53964; 0x85020; 0x829cc; 0x819d4];
[0x53964; 0x85020; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x85020; 0x829ec];
[0x53964; 0x85020; 0x829ec; 0x819d4];
[0x53964; 0x85020; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x85028];
[0x53964; 0x85028; 0x829cc];
[0x53964; 0x85028; 0x829cc; 0x819d4];
[0x53964; 0x85028; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x85028; 0x829ec];
[0x53964; 0x85028; 0x829ec; 0x819d4];
[0x53964; 0x85028; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x8516c];
[0x53964; 0x8516c; 0x829cc];
[0x53964; 0x8516c; 0x829cc; 0x819d4];
[0x53964; 0x8516c; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x8516c; 0x829ec];
[0x53964; 0x8516c; 0x829ec; 0x819d4];
[0x53964; 0x8516c; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x85174];
[0x53964; 0x85174; 0x829cc];
[0x53964; 0x85174; 0x829cc; 0x819d4];
[0x53964; 0x85174; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x85174; 0x829ec];
[0x53964; 0x85174; 0x829ec; 0x819d4];
[0x53964; 0x85174; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86b54];
[0x53964; 0x86b54; 0x815c8];
[0x53964; 0x86b54; 0x81818];
[0x53964; 0x86b54; 0x81818; 0x815c8];
[0x53964; 0x86b54; 0x819d4];
[0x53964; 0x86b54; 0x819d4; 0x815c8];
[0x53964; 0x86b54; 0x829cc];
[0x53964; 0x86b54; 0x829cc; 0x819d4];
[0x53964; 0x86b54; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86b54; 0x829ec];
[0x53964; 0x86b54; 0x829ec; 0x819d4];
[0x53964; 0x86b54; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86b88];
[0x53964; 0x86b88; 0x815c8];
[0x53964; 0x86b88; 0x81818];
[0x53964; 0x86b88; 0x81818; 0x815c8];
[0x53964; 0x86b88; 0x819d4];
[0x53964; 0x86b88; 0x819d4; 0x815c8];
[0x53964; 0x86b88; 0x829cc];
[0x53964; 0x86b88; 0x829cc; 0x819d4];
[0x53964; 0x86b88; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86b88; 0x829ec];
[0x53964; 0x86b88; 0x829ec; 0x819d4];
[0x53964; 0x86b88; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86ba0];
[0x53964; 0x86ba0; 0x815c8];
[0x53964; 0x86ba0; 0x81818];
[0x53964; 0x86ba0; 0x81818; 0x815c8];
[0x53964; 0x86ba0; 0x819d4];
[0x53964; 0x86ba0; 0x819d4; 0x815c8];
[0x53964; 0x86ba0; 0x829cc];
[0x53964; 0x86ba0; 0x829cc; 0x819d4];
[0x53964; 0x86ba0; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86ba0; 0x829ec];
[0x53964; 0x86ba0; 0x829ec; 0x819d4];
[0x53964; 0x86ba0; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x86bbc];
[0x53964; 0x86bbc; 0x815c8];
[0x53964; 0x86bbc; 0x81818];
[0x53964; 0x86bbc; 0x81818; 0x815c8];
[0x53964; 0x86bbc; 0x819d4];
[0x53964; 0x86bbc; 0x819d4; 0x815c8];
[0x53964; 0x86bbc; 0x829cc];
[0x53964; 0x86bbc; 0x829cc; 0x819d4];
[0x53964; 0x86bbc; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x86bbc; 0x829ec];
[0x53964; 0x86bbc; 0x829ec; 0x819d4];
[0x53964; 0x86bbc; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x87330];
[0x53964; 0x87330; 0x819c0];
[0x53964; 0x87330; 0x819c0; 0x815c8];
[0x53964; 0x87330; 0x819d4];
[0x53964; 0x87330; 0x819d4; 0x815c8];
[0x53964; 0x87330; 0x819ec];
[0x53964; 0x87330; 0x819ec; 0x815c8];
[0x53964; 0x87330; 0x829cc];
[0x53964; 0x87330; 0x829cc; 0x819d4];
[0x53964; 0x87330; 0x829cc; 0x819d4; 0x815c8];
[0x53964; 0x87330; 0x829ec];
[0x53964; 0x87330; 0x829ec; 0x819d4];
[0x53964; 0x87330; 0x829ec; 0x819d4; 0x815c8];
[0x53964; 0x87f34];
[0x53964; 0x87f34; 0x8633c];
[0x53964; 0x87f34; 0x87d98];
[0x53964; 0x885e4];
[0x53964; 0x885e4; 0x8633c];
[0x53964; 0x885e4; 0x87d98];
[0x53ac4];
[0x53ac4; 0x81280];
[0x53ac4; 0x812d4];
[0x53ac4; 0x81560];
[0x53ac4; 0x81fc0];
[0x53ac4; 0x81fc0; 0x815c8];
[0x53ac4; 0x830d4];
[0x53ac4; 0x830d4; 0x81818];
[0x53ac4; 0x830d4; 0x81818; 0x815c8];
[0x53ac4; 0x85d50];
[0x53ac4; 0x85d50; 0x8633c];
[0x53ac4; 0x85d50; 0x87d98];
[0x53d60];
[0x53d60; 0x8529c];
[0x53d60; 0x8529c; 0x829cc];
[0x53d60; 0x8529c; 0x829cc; 0x819d4];
[0x53d60; 0x8529c; 0x829cc; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x829ec];
[0x53d60; 0x8529c; 0x829ec; 0x819d4];
[0x53d60; 0x8529c; 0x829ec; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x84fb8];
[0x53d60; 0x8529c; 0x84fb8; 0x829cc];
[0x53d60; 0x8529c; 0x84fb8; 0x829cc; 0x819d4];
[0x53d60; 0x8529c; 0x84fb8; 0x829cc; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x84fb8; 0x829ec];
[0x53d60; 0x8529c; 0x84fb8; 0x829ec; 0x819d4];
[0x53d60; 0x8529c; 0x84fb8; 0x829ec; 0x819d4; 0x815c8];
[0x53d60; 0x8529c; 0x85638];
[0x53d60; 0x8529c; 0x856b8];
[0x53d60; 0x86048]].
Definition Tfib_wild : list (list Z) :=
[[0x53964; 0x87f34];
[0x53964; 0x885e4];
[0x53d60; 0x8529c]].
Definition Tfib_universe : Univ := univ_of Tfib_fixed Tfib_wild.
Fixpoint listZ_eqb (a b : list Z) : bool :=
match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && listZ_eqb a' b' | _, _ => false end.
Fixpoint memZL (t : list Z) (l : list (list Z)) : bool :=
match l with [] => false | u :: l' => listZ_eqb t u || memZL t l' end.
Lemma listZ_eqb_eq : forall a b, listZ_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [exact H1 | apply IH, H2].
Qed.
Lemma memZL_In : forall t l, memZL t l = true -> In t l.
Proof.
induction l as [|u l IH]; cbn; intros H; [discriminate|].
apply Bool.orb_prop in H as [H|H]; [left; symmetry; apply listZ_eqb_eq, H | right; apply IH, H].
Qed.
Fixpoint allb {X} (f : X -> bool) (l : list X) : bool := match l with [] => true | x :: l' => f x && allb f l' end.
Lemma allb_In : forall {X} (f : X -> bool) l x, allb f l = true -> In x l -> f x = true.
Proof. induction l; cbn; intros x H Hin; [destruct Hin|]. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; auto. Qed.
Lemma TRACES_check_as_written_U : forall t, In t TRACES_check_as_written -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_as_written t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_no_overread_U : forall t, In t TRACES_check_no_overread -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_no_overread t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_reject_clean_starved_U : forall t, In t TRACES_check_reject_clean_starved -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_reject_clean_starved t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_round_trip_U : forall t, In t TRACES_check_round_trip -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_round_trip t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_malloc_U : forall t, In t TRACES_fuzz_malloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_malloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_realloc_U : forall t, In t TRACES_fuzz_realloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_realloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_padded_U : forall t, In t TRACES_padded -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_padded t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_parse_items_U : forall t, In t TRACES_parse_items -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_parse_items t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_parse_string_U : forall t, In t TRACES_parse_string -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_parse_string t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_pj_free_U : forall t, In t TRACES_pj_free -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_pj_free t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_pj_write_U : forall t, In t TRACES_pj_write -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_pj_write t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_round_trip_text_U : forall t, In t TRACES_round_trip_text -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_round_trip_text t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_tx_put_U : forall t, In t TRACES_tx_put -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_tx_put t ltac:(vm_compute; reflexivity) H). Qed.
Fixpoint nodupZL (l : list (list Z)) : bool :=
match l with [] => true | t :: l' => negb (memZL t l') && nodupZL l' end.
Lemma memZL_false : forall t l, memZL t l = false -> ~ In t l.
Proof.
induction l as [|u l IH]; cbn; intros H Hin; [exact Hin|].
apply Bool.orb_false_elim in H as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)].
assert (E : forall a, listZ_eqb a a = true) by (induction a; cbn; [reflexivity|]; rewrite Z.eqb_refl; assumption).
rewrite E in H1. discriminate.
Qed.
Lemma nodupZL_NoDup : forall l, nodupZL l = true -> NoDup l.
Proof.
induction l as [|t l IH]; cbn; intros H; [constructor|].
apply andb_prop in H as [H1 H2]. constructor; [apply memZL_false; destruct (memZL t l); [discriminate|reflexivity] | apply IH, H2].
Qed.
Lemma Tfib_universe_ok : universe_ok Tfib_universe.
Proof.
apply univ_of_ok.
- unfold DEPOT_MAX. apply Z.leb_le. vm_compute. reflexivity.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_fixed t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
