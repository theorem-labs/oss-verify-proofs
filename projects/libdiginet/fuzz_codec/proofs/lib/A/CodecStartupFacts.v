(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the start-up facts of libreac/fuzz_identity's ASan build (image A) that
   lib/A/Prog/IdentEntryLink.v (Section L) takes as the Hypotheses GM (:250), IV (:251), ZS_STEM (:340), ZS_NAME (:341),
   HUMM (:680) and HUMF (:683), each proved here with that Hypothesis's text as its conclusion. The checks and their
   lemmas are ported from fuzz_grant's closer (d110b9a519a, proofs/libreac/fuzz_grant/lib/A/Prog/
   GrantCloseChk.v:38-145 and GrantClose.v:200-287); the universe check is cgif's ACee.v:80 pattern (c8557374ad2e) in
   the start-up AD2l.v's In_of_existsb form. One change in substance: the glob check is RELAXED (see glob_chk_relaxed). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/A/IdentStartupFacts.v
   (origin/ossv/recipes 4b6f0df50aa7) for libdiginet/fuzz_codec's ASan build (image A, fuzz_codec.asan sha256
   7d470194ffdb...): module paths changed; the copied tables are fuzz_codec.asan's; the facts are GM and IV over the 40
   registered globals CODEC_GLOBS (lib/A/Prog/CodecGlobs.v) and any segment list; identity's ZS_STEM / ZS_NAME
   (two of its tables) become one decision lemma codec_in_zs_of_b for any range, and its HUMM / HUMF (allocator
   traces) are dropped with their premises HUNIV / HRA0M / HRA0F, because fuzz_codec's harness calls no allocator.
   Added: a closed satisfiability lemma, codec_startup_sat, at the start state's shadow as the copied tables state it. *)
(* The record: premises, not the core. As fuzz_identity's file does, the facts are stated in a Section over
   `Variable CodecB : asyms` with one premise per record field the proofs read, against verbatim copies of the start-up
   tables below (lib/A/CodecStartupClose.v discharges both premises at the start-up record TfibB, lib/A/AD2l.v):
     HZS    : as_zero_shadow CodecB = TFIB_ZERO_SHADOW_A                           (GM, IV, codec_in_zs_of_b)
     HCONST : forall ly, exists pre, as_const CodecB ly = pre ++ TFIB_CONST_SHADOW_A (GM, IV)
   HCONST asks only that the copied shadow cells are the tail of the record's const list, because the proofs read no
   other const cell: AF0m.v:1204 has Tfib_const ly := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow. No AR law
   is a premise: the zero-shadow ranges and the const cells are fields of AR's first conjunct ARm (am_zshadow,
   am_const: Reusable/YG0n.v), so LAWS (AR_laws) is not needed.
   A record that is an instance of AF0m.v's TfibSyms meets both premises: HZS from ts_zsh (AF0m.v:1239) and the
   copy's equality to Tfib_zero_shadow; HCONST from ts_const (AF0m.v:1235) with
   pre := Tfib_const_sym ++ Tfib_const_abs and app_assoc.
   Sources of the copies (each body below is the source's text, line for line):
     TFIB_ZERO_SHADOW_A  = Tfib_zero_shadow,  lib/A/AF0m.v:1206
     TFIB_CONST_SHADOW_A = Tfib_const_shadow, lib/A/AF0m.v:716-1203 (488 one-byte cells)
       (AF0m.v sha256 fd60b6ac24a5e72f2231d580c534209268a3f2b9805aceddbc7c3a890e910ad0, generated from fuzz_codec.asan).
   Measured against the image (a pyelftools read of fuzz_codec.asan's asan_globals section): for each of the 40
   descriptors, every granule of [beg, beg + size_with_redzone) has, in these two tables, the shadow byte the runtime's
   registration writes (0 for a full granule, size mod 8 for a partial last one, 0xf9 for the guard bytes); no cell
   repeats an address, and no cell with a nonzero byte lies in a zero-shadow range. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecRo CodecGlobs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the start-up tables, verbatim (sources in the header) ------------------------------------------------- *)
Definition TFIB_ZERO_SHADOW_A : list (Z * Z) :=
[ (0x10000, 0x20f48 - 0x10000); (0x20f60, 0x20f68 - 0x20f60); (0x20f80, 0x20f88 - 0x20f80); (0x20fa0, 0x20fa8 - 0x20fa0); (0x20fc0, 0x20fc8 - 0x20fc0); (0x21100, 0x21108 - 0x21100); (0x21340, 0x21368 - 0x21340); (0x21380, 0x21388 - 0x21380); (0x213a0, 0x21508 - 0x213a0); (0x21560, 0x9d678 - 0x21560); (0x9d6a0, 0x9d6b0 - 0x9d6a0); (0x9d6c0, 0x9d6d0 - 0x9d6c0); (0x9d6e0, 0x9d8b0 - 0x9d6e0); (0x9d920, 0x9d950 - 0x9d920); (0x9d980, 0xa23c0 - 0x9d980); (0xa2dc0, 0x5fb000 - 0xa2dc0) ].
Definition TFIB_CONST_SHADOW_A : list acell :=
[ z1 (ANum 0x7fffc1e9) 0x4  ;
z1 (ANum 0x7fffc1ea) 0xf9  ;
z1 (ANum 0x7fffc1eb) 0xf9  ;
z1 (ANum 0x7fffc1ed) 0x1  ;
z1 (ANum 0x7fffc1ee) 0xf9  ;
z1 (ANum 0x7fffc1ef) 0xf9  ;
z1 (ANum 0x7fffc1f1) 0x1  ;
z1 (ANum 0x7fffc1f2) 0xf9  ;
z1 (ANum 0x7fffc1f3) 0xf9  ;
z1 (ANum 0x7fffc1f5) 0xf9  ;
z1 (ANum 0x7fffc1f6) 0xf9  ;
z1 (ANum 0x7fffc1f7) 0xf9  ;
z1 (ANum 0x7fffc1f9) 0x2  ;
z1 (ANum 0x7fffc1fa) 0xf9  ;
z1 (ANum 0x7fffc1fb) 0xf9  ;
z1 (ANum 0x7fffc1fc) 0x1  ;
z1 (ANum 0x7fffc1fd) 0xf9  ;
z1 (ANum 0x7fffc1fe) 0xf9  ;
z1 (ANum 0x7fffc1ff) 0xf9  ;
z1 (ANum 0x7fffc200) 0x7  ;
z1 (ANum 0x7fffc201) 0xf9  ;
z1 (ANum 0x7fffc202) 0xf9  ;
z1 (ANum 0x7fffc203) 0xf9  ;
z1 (ANum 0x7fffc204) 0x3  ;
z1 (ANum 0x7fffc205) 0xf9  ;
z1 (ANum 0x7fffc206) 0xf9  ;
z1 (ANum 0x7fffc207) 0xf9  ;
z1 (ANum 0x7fffc208) 0x6  ;
z1 (ANum 0x7fffc209) 0xf9  ;
z1 (ANum 0x7fffc20a) 0xf9  ;
z1 (ANum 0x7fffc20b) 0xf9  ;
z1 (ANum 0x7fffc20c) 0x6  ;
z1 (ANum 0x7fffc20d) 0xf9  ;
z1 (ANum 0x7fffc20e) 0xf9  ;
z1 (ANum 0x7fffc20f) 0xf9  ;
z1 (ANum 0x7fffc210) 0x5  ;
z1 (ANum 0x7fffc211) 0xf9  ;
z1 (ANum 0x7fffc212) 0xf9  ;
z1 (ANum 0x7fffc213) 0xf9  ;
z1 (ANum 0x7fffc214) 0x6  ;
z1 (ANum 0x7fffc215) 0xf9  ;
z1 (ANum 0x7fffc216) 0xf9  ;
z1 (ANum 0x7fffc217) 0xf9  ;
z1 (ANum 0x7fffc218) 0x7  ;
z1 (ANum 0x7fffc219) 0xf9  ;
z1 (ANum 0x7fffc21a) 0xf9  ;
z1 (ANum 0x7fffc21b) 0xf9  ;
z1 (ANum 0x7fffc21c) 0x4  ;
z1 (ANum 0x7fffc21d) 0xf9  ;
z1 (ANum 0x7fffc21e) 0xf9  ;
z1 (ANum 0x7fffc21f) 0xf9  ;
z1 (ANum 0x7fffc221) 0xf9  ;
z1 (ANum 0x7fffc222) 0xf9  ;
z1 (ANum 0x7fffc223) 0xf9  ;
z1 (ANum 0x7fffc224) 0x7  ;
z1 (ANum 0x7fffc225) 0xf9  ;
z1 (ANum 0x7fffc226) 0xf9  ;
z1 (ANum 0x7fffc227) 0xf9  ;
z1 (ANum 0x7fffc228) 0x7  ;
z1 (ANum 0x7fffc229) 0xf9  ;
z1 (ANum 0x7fffc22a) 0xf9  ;
z1 (ANum 0x7fffc22b) 0xf9  ;
z1 (ANum 0x7fffc22c) 0x6  ;
z1 (ANum 0x7fffc22d) 0xf9  ;
z1 (ANum 0x7fffc22e) 0xf9  ;
z1 (ANum 0x7fffc22f) 0xf9  ;
z1 (ANum 0x7fffc230) 0x5  ;
z1 (ANum 0x7fffc231) 0xf9  ;
z1 (ANum 0x7fffc232) 0xf9  ;
z1 (ANum 0x7fffc233) 0xf9  ;
z1 (ANum 0x7fffc234) 0x6  ;
z1 (ANum 0x7fffc235) 0xf9  ;
z1 (ANum 0x7fffc236) 0xf9  ;
z1 (ANum 0x7fffc237) 0xf9  ;
z1 (ANum 0x7fffc238) 0x6  ;
z1 (ANum 0x7fffc239) 0xf9  ;
z1 (ANum 0x7fffc23a) 0xf9  ;
z1 (ANum 0x7fffc23b) 0xf9  ;
z1 (ANum 0x7fffc23c) 0x5  ;
z1 (ANum 0x7fffc23d) 0xf9  ;
z1 (ANum 0x7fffc23e) 0xf9  ;
z1 (ANum 0x7fffc23f) 0xf9  ;
z1 (ANum 0x7fffc240) 0x6  ;
z1 (ANum 0x7fffc241) 0xf9  ;
z1 (ANum 0x7fffc242) 0xf9  ;
z1 (ANum 0x7fffc243) 0xf9  ;
z1 (ANum 0x7fffc244) 0x5  ;
z1 (ANum 0x7fffc245) 0xf9  ;
z1 (ANum 0x7fffc246) 0xf9  ;
z1 (ANum 0x7fffc247) 0xf9  ;
z1 (ANum 0x7fffc248) 0x5  ;
z1 (ANum 0x7fffc249) 0xf9  ;
z1 (ANum 0x7fffc24a) 0xf9  ;
z1 (ANum 0x7fffc24b) 0xf9  ;
z1 (ANum 0x7fffc24c) 0x4  ;
z1 (ANum 0x7fffc24d) 0xf9  ;
z1 (ANum 0x7fffc24e) 0xf9  ;
z1 (ANum 0x7fffc24f) 0xf9  ;
z1 (ANum 0x7fffc250) 0x5  ;
z1 (ANum 0x7fffc251) 0xf9  ;
z1 (ANum 0x7fffc252) 0xf9  ;
z1 (ANum 0x7fffc253) 0xf9  ;
z1 (ANum 0x7fffc254) 0x6  ;
z1 (ANum 0x7fffc255) 0xf9  ;
z1 (ANum 0x7fffc256) 0xf9  ;
z1 (ANum 0x7fffc257) 0xf9  ;
z1 (ANum 0x7fffc258) 0x3  ;
z1 (ANum 0x7fffc259) 0xf9  ;
z1 (ANum 0x7fffc25a) 0xf9  ;
z1 (ANum 0x7fffc25b) 0xf9  ;
z1 (ANum 0x7fffc25c) 0x6  ;
z1 (ANum 0x7fffc25d) 0xf9  ;
z1 (ANum 0x7fffc25e) 0xf9  ;
z1 (ANum 0x7fffc25f) 0xf9  ;
z1 (ANum 0x7fffc260) 0x6  ;
z1 (ANum 0x7fffc261) 0xf9  ;
z1 (ANum 0x7fffc262) 0xf9  ;
z1 (ANum 0x7fffc263) 0xf9  ;
z1 (ANum 0x7fffc264) 0x2  ;
z1 (ANum 0x7fffc265) 0xf9  ;
z1 (ANum 0x7fffc266) 0xf9  ;
z1 (ANum 0x7fffc267) 0xf9  ;
z1 (ANum 0x7fffc26d) 0x1  ;
z1 (ANum 0x7fffc26e) 0xf9  ;
z1 (ANum 0x7fffc26f) 0xf9  ;
z1 (ANum 0x7fffc271) 0x1  ;
z1 (ANum 0x7fffc272) 0xf9  ;
z1 (ANum 0x7fffc273) 0xf9  ;
z1 (ANum 0x7fffc2a1) 0x4  ;
z1 (ANum 0x7fffc2a2) 0xf9  ;
z1 (ANum 0x7fffc2a3) 0xf9  ;
z1 (ANum 0x7fffc2a4) 0xf9  ;
z1 (ANum 0x7fffc2a5) 0xf9  ;
z1 (ANum 0x7fffc2a6) 0xf9  ;
z1 (ANum 0x7fffc2a7) 0xf9  ;
z1 (ANum 0x7fffc2a8) 0xf9  ;
z1 (ANum 0x7fffc2a9) 0xf9  ;
z1 (ANum 0x7fffc2aa) 0xf9  ;
z1 (ANum 0x7fffc2ab) 0xf9  ;
z1 (ANum 0x8000bacf) 0xf9  ;
z1 (ANum 0x8000bad0) 0xf9  ;
z1 (ANum 0x8000bad1) 0xf9  ;
z1 (ANum 0x8000bad2) 0xf9  ;
z1 (ANum 0x8000bad3) 0xf9  ;
z1 (ANum 0x8000bad6) 0xf9  ;
z1 (ANum 0x8000bad7) 0xf9  ;
z1 (ANum 0x8000bada) 0xf9  ;
z1 (ANum 0x8000badb) 0xf9  ;
z1 (ANum 0x8000bb16) 0xf9  ;
z1 (ANum 0x8000bb17) 0xf9  ;
z1 (ANum 0x8000bb18) 0xf9  ;
z1 (ANum 0x8000bb19) 0xf9  ;
z1 (ANum 0x8000bb1a) 0xf9  ;
z1 (ANum 0x8000bb1b) 0xf9  ;
z1 (ANum 0x8000bb1c) 0xf9  ;
z1 (ANum 0x8000bb1d) 0xf9  ;
z1 (ANum 0x8000bb1e) 0xf9  ;
z1 (ANum 0x8000bb1f) 0xf9  ;
z1 (ANum 0x8000bb20) 0xf9  ;
z1 (ANum 0x8000bb21) 0xf9  ;
z1 (ANum 0x8000bb22) 0xf9  ;
z1 (ANum 0x8000bb23) 0xf9  ;
z1 (ANum 0x8000bb2a) 0xf9  ;
z1 (ANum 0x8000bb2b) 0xf9  ;
z1 (ANum 0x8000bb2c) 0xf9  ;
z1 (ANum 0x8000bb2d) 0xf9  ;
z1 (ANum 0x8000bb2e) 0xf9  ;
z1 (ANum 0x8000bb2f) 0xf9  ;
z1 (ANum 0x8000c478) 0xf9  ;
z1 (ANum 0x8000c479) 0xf9  ;
z1 (ANum 0x8000c47a) 0xf9  ;
z1 (ANum 0x8000c47b) 0xf9  ;
z1 (ANum 0x8000c47c) 0xf9  ;
z1 (ANum 0x8000c47d) 0xf9  ;
z1 (ANum 0x8000c47e) 0xf9  ;
z1 (ANum 0x8000c47f) 0xf9  ;
z1 (ANum 0x8000c480) 0xf9  ;
z1 (ANum 0x8000c481) 0xf9  ;
z1 (ANum 0x8000c482) 0xf9  ;
z1 (ANum 0x8000c483) 0xf9  ;
z1 (ANum 0x8000c484) 0xf9  ;
z1 (ANum 0x8000c485) 0xf9  ;
z1 (ANum 0x8000c486) 0xf9  ;
z1 (ANum 0x8000c487) 0xf9  ;
z1 (ANum 0x8000c488) 0xf9  ;
z1 (ANum 0x8000c489) 0xf9  ;
z1 (ANum 0x8000c48a) 0xf9  ;
z1 (ANum 0x8000c48b) 0xf9  ;
z1 (ANum 0x8000c48c) 0xf9  ;
z1 (ANum 0x8000c48d) 0xf9  ;
z1 (ANum 0x8000c48e) 0xf9  ;
z1 (ANum 0x8000c48f) 0xf9  ;
z1 (ANum 0x8000c490) 0xf9  ;
z1 (ANum 0x8000c491) 0xf9  ;
z1 (ANum 0x8000c492) 0xf9  ;
z1 (ANum 0x8000c493) 0xf9  ;
z1 (ANum 0x8000c494) 0xf9  ;
z1 (ANum 0x8000c495) 0xf9  ;
z1 (ANum 0x8000c496) 0xf9  ;
z1 (ANum 0x8000c497) 0xf9  ;
z1 (ANum 0x8000c498) 0xf9  ;
z1 (ANum 0x8000c499) 0xf9  ;
z1 (ANum 0x8000c49a) 0xf9  ;
z1 (ANum 0x8000c49b) 0xf9  ;
z1 (ANum 0x8000c49c) 0xf9  ;
z1 (ANum 0x8000c49d) 0xf9  ;
z1 (ANum 0x8000c49e) 0xf9  ;
z1 (ANum 0x8000c49f) 0xf9  ;
z1 (ANum 0x8000c4a0) 0xf9  ;
z1 (ANum 0x8000c4a1) 0xf9  ;
z1 (ANum 0x8000c4a2) 0xf9  ;
z1 (ANum 0x8000c4a3) 0xf9  ;
z1 (ANum 0x8000c4a4) 0xf9  ;
z1 (ANum 0x8000c4a5) 0xf9  ;
z1 (ANum 0x8000c4a6) 0xf9  ;
z1 (ANum 0x8000c4a7) 0xf9  ;
z1 (ANum 0x8000c4a8) 0xf9  ;
z1 (ANum 0x8000c4a9) 0xf9  ;
z1 (ANum 0x8000c4aa) 0xf9  ;
z1 (ANum 0x8000c4ab) 0xf9  ;
z1 (ANum 0x8000c4ac) 0xf9  ;
z1 (ANum 0x8000c4ad) 0xf9  ;
z1 (ANum 0x8000c4ae) 0xf9  ;
z1 (ANum 0x8000c4af) 0xf9  ;
z1 (ANum 0x8000c4b0) 0xf9  ;
z1 (ANum 0x8000c4b1) 0xf9  ;
z1 (ANum 0x8000c4b2) 0xf9  ;
z1 (ANum 0x8000c4b3) 0xf9  ;
z1 (ANum 0x8000c4b4) 0xf9  ;
z1 (ANum 0x8000c4b5) 0xf9  ;
z1 (ANum 0x8000c4b6) 0xf9  ;
z1 (ANum 0x8000c4b7) 0xf9  ;
z1 (ANum 0x8000c4b8) 0xf9  ;
z1 (ANum 0x8000c4b9) 0xf9  ;
z1 (ANum 0x8000c4ba) 0xf9  ;
z1 (ANum 0x8000c4bb) 0xf9  ;
z1 (ANum 0x8000c4bc) 0xf9  ;
z1 (ANum 0x8000c4bd) 0xf9  ;
z1 (ANum 0x8000c4be) 0xf9  ;
z1 (ANum 0x8000c4bf) 0xf9  ;
z1 (ANum 0x8000c4c0) 0xf9  ;
z1 (ANum 0x8000c4c1) 0xf9  ;
z1 (ANum 0x8000c4c2) 0xf9  ;
z1 (ANum 0x8000c4c3) 0xf9  ;
z1 (ANum 0x8000c4c4) 0xf9  ;
z1 (ANum 0x8000c4c5) 0xf9  ;
z1 (ANum 0x8000c4c6) 0xf9  ;
z1 (ANum 0x8000c4c7) 0xf9  ;
z1 (ANum 0x8000c4c8) 0xf9  ;
z1 (ANum 0x8000c4c9) 0xf9  ;
z1 (ANum 0x8000c4ca) 0xf9  ;
z1 (ANum 0x8000c4cb) 0xf9  ;
z1 (ANum 0x8000c4cc) 0xf9  ;
z1 (ANum 0x8000c4cd) 0xf9  ;
z1 (ANum 0x8000c4ce) 0xf9  ;
z1 (ANum 0x8000c4cf) 0xf9  ;
z1 (ANum 0x8000c4d0) 0xf9  ;
z1 (ANum 0x8000c4d1) 0xf9  ;
z1 (ANum 0x8000c4d2) 0xf9  ;
z1 (ANum 0x8000c4d3) 0xf9  ;
z1 (ANum 0x8000c4d4) 0xf9  ;
z1 (ANum 0x8000c4d5) 0xf9  ;
z1 (ANum 0x8000c4d6) 0xf9  ;
z1 (ANum 0x8000c4d7) 0xf9  ;
z1 (ANum 0x8000c4d8) 0xf9  ;
z1 (ANum 0x8000c4d9) 0xf9  ;
z1 (ANum 0x8000c4da) 0xf9  ;
z1 (ANum 0x8000c4db) 0xf9  ;
z1 (ANum 0x8000c4dc) 0xf9  ;
z1 (ANum 0x8000c4dd) 0xf9  ;
z1 (ANum 0x8000c4de) 0xf9  ;
z1 (ANum 0x8000c4df) 0xf9  ;
z1 (ANum 0x8000c4e0) 0xf9  ;
z1 (ANum 0x8000c4e1) 0xf9  ;
z1 (ANum 0x8000c4e2) 0xf9  ;
z1 (ANum 0x8000c4e3) 0xf9  ;
z1 (ANum 0x8000c4e4) 0xf9  ;
z1 (ANum 0x8000c4e5) 0xf9  ;
z1 (ANum 0x8000c4e6) 0xf9  ;
z1 (ANum 0x8000c4e7) 0xf9  ;
z1 (ANum 0x8000c4e8) 0xf9  ;
z1 (ANum 0x8000c4e9) 0xf9  ;
z1 (ANum 0x8000c4ea) 0xf9  ;
z1 (ANum 0x8000c4eb) 0xf9  ;
z1 (ANum 0x8000c4ec) 0xf9  ;
z1 (ANum 0x8000c4ed) 0xf9  ;
z1 (ANum 0x8000c4ee) 0xf9  ;
z1 (ANum 0x8000c4ef) 0xf9  ;
z1 (ANum 0x8000c4f0) 0xf9  ;
z1 (ANum 0x8000c4f1) 0xf9  ;
z1 (ANum 0x8000c4f2) 0xf9  ;
z1 (ANum 0x8000c4f3) 0xf9  ;
z1 (ANum 0x8000c4f4) 0xf9  ;
z1 (ANum 0x8000c4f5) 0xf9  ;
z1 (ANum 0x8000c4f6) 0xf9  ;
z1 (ANum 0x8000c4f7) 0xf9  ;
z1 (ANum 0x8000c4f8) 0xf9  ;
z1 (ANum 0x8000c4f9) 0xf9  ;
z1 (ANum 0x8000c4fa) 0xf9  ;
z1 (ANum 0x8000c4fb) 0xf9  ;
z1 (ANum 0x8000c4fc) 0xf9  ;
z1 (ANum 0x8000c4fd) 0xf9  ;
z1 (ANum 0x8000c4fe) 0xf9  ;
z1 (ANum 0x8000c4ff) 0xf9  ;
z1 (ANum 0x8000c500) 0xf9  ;
z1 (ANum 0x8000c501) 0xf9  ;
z1 (ANum 0x8000c502) 0xf9  ;
z1 (ANum 0x8000c503) 0xf9  ;
z1 (ANum 0x8000c504) 0xf9  ;
z1 (ANum 0x8000c505) 0xf9  ;
z1 (ANum 0x8000c506) 0xf9  ;
z1 (ANum 0x8000c507) 0xf9  ;
z1 (ANum 0x8000c508) 0xf9  ;
z1 (ANum 0x8000c509) 0xf9  ;
z1 (ANum 0x8000c50a) 0xf9  ;
z1 (ANum 0x8000c50b) 0xf9  ;
z1 (ANum 0x8000c50c) 0xf9  ;
z1 (ANum 0x8000c50d) 0xf9  ;
z1 (ANum 0x8000c50e) 0xf9  ;
z1 (ANum 0x8000c50f) 0xf9  ;
z1 (ANum 0x8000c510) 0xf9  ;
z1 (ANum 0x8000c511) 0xf9  ;
z1 (ANum 0x8000c512) 0xf9  ;
z1 (ANum 0x8000c513) 0xf9  ;
z1 (ANum 0x8000c514) 0xf9  ;
z1 (ANum 0x8000c515) 0xf9  ;
z1 (ANum 0x8000c516) 0xf9  ;
z1 (ANum 0x8000c517) 0xf9  ;
z1 (ANum 0x8000c518) 0xf9  ;
z1 (ANum 0x8000c519) 0xf9  ;
z1 (ANum 0x8000c51a) 0xf9  ;
z1 (ANum 0x8000c51b) 0xf9  ;
z1 (ANum 0x8000c51c) 0xf9  ;
z1 (ANum 0x8000c51d) 0xf9  ;
z1 (ANum 0x8000c51e) 0xf9  ;
z1 (ANum 0x8000c51f) 0xf9  ;
z1 (ANum 0x8000c520) 0xf9  ;
z1 (ANum 0x8000c521) 0xf9  ;
z1 (ANum 0x8000c522) 0xf9  ;
z1 (ANum 0x8000c523) 0xf9  ;
z1 (ANum 0x8000c524) 0xf9  ;
z1 (ANum 0x8000c525) 0xf9  ;
z1 (ANum 0x8000c526) 0xf9  ;
z1 (ANum 0x8000c527) 0xf9  ;
z1 (ANum 0x8000c528) 0xf9  ;
z1 (ANum 0x8000c529) 0xf9  ;
z1 (ANum 0x8000c52a) 0xf9  ;
z1 (ANum 0x8000c52b) 0xf9  ;
z1 (ANum 0x8000c52c) 0xf9  ;
z1 (ANum 0x8000c52d) 0xf9  ;
z1 (ANum 0x8000c52e) 0xf9  ;
z1 (ANum 0x8000c52f) 0xf9  ;
z1 (ANum 0x8000c530) 0xf9  ;
z1 (ANum 0x8000c531) 0xf9  ;
z1 (ANum 0x8000c532) 0xf9  ;
z1 (ANum 0x8000c533) 0xf9  ;
z1 (ANum 0x8000c534) 0xf9  ;
z1 (ANum 0x8000c535) 0xf9  ;
z1 (ANum 0x8000c536) 0xf9  ;
z1 (ANum 0x8000c537) 0xf9  ;
z1 (ANum 0x8000c538) 0xf9  ;
z1 (ANum 0x8000c539) 0xf9  ;
z1 (ANum 0x8000c53a) 0xf9  ;
z1 (ANum 0x8000c53b) 0xf9  ;
z1 (ANum 0x8000c53c) 0xf9  ;
z1 (ANum 0x8000c53d) 0xf9  ;
z1 (ANum 0x8000c53e) 0xf9  ;
z1 (ANum 0x8000c53f) 0xf9  ;
z1 (ANum 0x8000c540) 0xf9  ;
z1 (ANum 0x8000c541) 0xf9  ;
z1 (ANum 0x8000c542) 0xf9  ;
z1 (ANum 0x8000c543) 0xf9  ;
z1 (ANum 0x8000c544) 0xf9  ;
z1 (ANum 0x8000c545) 0xf9  ;
z1 (ANum 0x8000c546) 0xf9  ;
z1 (ANum 0x8000c547) 0xf9  ;
z1 (ANum 0x8000c548) 0xf9  ;
z1 (ANum 0x8000c549) 0xf9  ;
z1 (ANum 0x8000c54a) 0xf9  ;
z1 (ANum 0x8000c54b) 0xf9  ;
z1 (ANum 0x8000c54c) 0xf9  ;
z1 (ANum 0x8000c54d) 0xf9  ;
z1 (ANum 0x8000c54e) 0xf9  ;
z1 (ANum 0x8000c54f) 0xf9  ;
z1 (ANum 0x8000c550) 0xf9  ;
z1 (ANum 0x8000c551) 0xf9  ;
z1 (ANum 0x8000c552) 0xf9  ;
z1 (ANum 0x8000c553) 0xf9  ;
z1 (ANum 0x8000c554) 0xf9  ;
z1 (ANum 0x8000c555) 0xf9  ;
z1 (ANum 0x8000c556) 0xf9  ;
z1 (ANum 0x8000c557) 0xf9  ;
z1 (ANum 0x8000c558) 0xf9  ;
z1 (ANum 0x8000c559) 0xf9  ;
z1 (ANum 0x8000c55a) 0xf9  ;
z1 (ANum 0x8000c55b) 0xf9  ;
z1 (ANum 0x8000c55c) 0xf9  ;
z1 (ANum 0x8000c55d) 0xf9  ;
z1 (ANum 0x8000c55e) 0xf9  ;
z1 (ANum 0x8000c55f) 0xf9  ;
z1 (ANum 0x8000c560) 0xf9  ;
z1 (ANum 0x8000c561) 0xf9  ;
z1 (ANum 0x8000c562) 0xf9  ;
z1 (ANum 0x8000c563) 0xf9  ;
z1 (ANum 0x8000c564) 0xf9  ;
z1 (ANum 0x8000c565) 0xf9  ;
z1 (ANum 0x8000c566) 0xf9  ;
z1 (ANum 0x8000c567) 0xf9  ;
z1 (ANum 0x8000c568) 0xf9  ;
z1 (ANum 0x8000c569) 0xf9  ;
z1 (ANum 0x8000c56a) 0xf9  ;
z1 (ANum 0x8000c56b) 0xf9  ;
z1 (ANum 0x8000c56c) 0xf9  ;
z1 (ANum 0x8000c56d) 0xf9  ;
z1 (ANum 0x8000c56e) 0xf9  ;
z1 (ANum 0x8000c56f) 0xf9  ;
z1 (ANum 0x8000c570) 0xf9  ;
z1 (ANum 0x8000c571) 0xf9  ;
z1 (ANum 0x8000c572) 0xf9  ;
z1 (ANum 0x8000c573) 0xf9  ;
z1 (ANum 0x8000c574) 0xf9  ;
z1 (ANum 0x8000c575) 0xf9  ;
z1 (ANum 0x8000c576) 0xf9  ;
z1 (ANum 0x8000c577) 0xf9  ;
z1 (ANum 0x8000c578) 0xf9  ;
z1 (ANum 0x8000c579) 0xf9  ;
z1 (ANum 0x8000c57a) 0xf9  ;
z1 (ANum 0x8000c57b) 0xf9  ;
z1 (ANum 0x8000c57c) 0xf9  ;
z1 (ANum 0x8000c57d) 0xf9  ;
z1 (ANum 0x8000c57e) 0xf9  ;
z1 (ANum 0x8000c57f) 0xf9  ;
z1 (ANum 0x8000c580) 0xf9  ;
z1 (ANum 0x8000c581) 0xf9  ;
z1 (ANum 0x8000c582) 0xf9  ;
z1 (ANum 0x8000c583) 0xf9  ;
z1 (ANum 0x8000c584) 0xf9  ;
z1 (ANum 0x8000c585) 0xf9  ;
z1 (ANum 0x8000c586) 0xf9  ;
z1 (ANum 0x8000c587) 0xf9  ;
z1 (ANum 0x8000c588) 0xf9  ;
z1 (ANum 0x8000c589) 0xf9  ;
z1 (ANum 0x8000c58a) 0xf9  ;
z1 (ANum 0x8000c58b) 0xf9  ;
z1 (ANum 0x8000c58c) 0xf9  ;
z1 (ANum 0x8000c58d) 0xf9  ;
z1 (ANum 0x8000c58e) 0xf9  ;
z1 (ANum 0x8000c58f) 0xf9  ;
z1 (ANum 0x8000c590) 0xf9  ;
z1 (ANum 0x8000c591) 0xf9  ;
z1 (ANum 0x8000c592) 0xf9  ;
z1 (ANum 0x8000c593) 0xf9  ;
z1 (ANum 0x8000c594) 0xf9  ;
z1 (ANum 0x8000c595) 0xf9  ;
z1 (ANum 0x8000c596) 0xf9  ;
z1 (ANum 0x8000c597) 0xf9  ;
z1 (ANum 0x8000c598) 0xf9  ;
z1 (ANum 0x8000c599) 0xf9  ;
z1 (ANum 0x8000c59a) 0xf9  ;
z1 (ANum 0x8000c59b) 0xf9  ;
z1 (ANum 0x8000c59c) 0xf9  ;
z1 (ANum 0x8000c59d) 0xf9  ;
z1 (ANum 0x8000c59e) 0xf9  ;
z1 (ANum 0x8000c59f) 0xf9  ;
z1 (ANum 0x8000c5a0) 0xf9  ;
z1 (ANum 0x8000c5a1) 0xf9  ;
z1 (ANum 0x8000c5a2) 0xf9  ;
z1 (ANum 0x8000c5a3) 0xf9  ;
z1 (ANum 0x8000c5a4) 0xf9  ;
z1 (ANum 0x8000c5a5) 0xf9  ;
z1 (ANum 0x8000c5a6) 0xf9  ;
z1 (ANum 0x8000c5a7) 0xf9  ;
z1 (ANum 0x8000c5a8) 0xf9  ;
z1 (ANum 0x8000c5a9) 0xf9  ;
z1 (ANum 0x8000c5aa) 0xf9  ;
z1 (ANum 0x8000c5ab) 0xf9  ;
z1 (ANum 0x8000c5ac) 0xf9  ;
z1 (ANum 0x8000c5ad) 0xf9  ;
z1 (ANum 0x8000c5ae) 0xf9  ;
z1 (ANum 0x8000c5af) 0xf9  ;
z1 (ANum 0x8000c5b0) 0xf9  ;
z1 (ANum 0x8000c5b1) 0xf9  ;
z1 (ANum 0x8000c5b2) 0xf9  ;
z1 (ANum 0x8000c5b3) 0xf9  ;
z1 (ANum 0x8000c5b4) 0xf9  ;
z1 (ANum 0x8000c5b5) 0xf9  ;
z1 (ANum 0x8000c5b6) 0xf9  ;
z1 (ANum 0x8000c5b7) 0xf9   ].

(* ---- the closed checks ------------------------------------------------------------------------------------- *)
(* The shadow byte at s is one of the certificate's one-byte cells (GrantCloseChk.v:38-41). *)
Definition sf_is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition sf_is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.

(* The end (in granules) of the zero-shadow range that holds granule k, if one does (GrantCloseChk.v:44-48). *)
Fixpoint sf_zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else sf_zfind k r
  end.

(* Every granule of [k, hi) is in a range of zs or has a cell in cells (GrantCloseChk.v:51-60). *)
Fixpoint sf_vscan (zs : list (Z * Z)) (cells : list acell) (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match sf_zfind k zs with
      | Some e => sf_vscan zs cells f e hi
      | None => (existsb (sf_is_shc (SHADOW_OFF + k)) cells && sf_vscan zs cells f (k + 1) hi)%bool
      end
  end.

(* The RELAXED glob check. fuzz_grant's glob_chk (GrantCloseChk.v:64-67) asks every global (q, sz) for a zero-shadow
   range over its full granules [q, q + sz / 8 * 8), also when it has none: a global of fewer than 8 bytes then
   needs a range that holds q, which a start-up table whose zero-shadow ranges stop at each global has not. Here that
   clause is asked only when sz / 8 > 0. Every global is still checked byte for byte: a global whose size is not a
   multiple of 8 has a partial last granule whose shadow byte must be the cell `sz mod 8` (glob_chk_relaxed_sound). *)
Definition glob_chk_relaxed (zs : list (Z * Z)) (cells : list acell) (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) || existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) zs) &&
   ((snd g mod 8 =? 0) || existsb (sf_is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) cells))%bool.

(* ---- what the checks say ------------------------------------------------------------------------------------- *)
Lemma sf_le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma sf_is_shc_eq : forall s c, sf_is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma sf_is_shv_eq : forall s v c, sf_is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma sf_zfind_some : forall k zs e, sf_zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [sf_zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [lia | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

(* [a, a + n) lies in one range of l (GrantCloseChk.v:139, over the list rather than the record). *)
Lemma sf_in_zs_of_b : forall (l : list (Z * Z)) a n,
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r))%bool l = true ->
  exists q m, In (q, m) l /\ q <= a /\ a + n <= q + m.
Proof.
intros l a n H. apply existsb_exists in H as ([q m] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, m. split; [exact Hin|]. lia.
Qed.

(* Over any reader rd that holds zero at the shadow of each (8-aligned) range of zs and each one-byte cell of cells. *)
Section sound.
Variable rd : YG0f.reader.
Variable zs : list (Z * Z).
Variable cells : list acell.
Hypothesis ZAL : forall q m, In (q, m) zs -> q mod 8 = 0.
Hypothesis ZRD : Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) zs.
Hypothesis CRD : forall s v, In (z1 (ANum s) v) cells -> rd s = Some (YG0f.le_byte v 1 0).

(* A granule of a zero-shadow range has shadow byte 0 (GrantClose.v:214). *)
Lemma sf_zs_rd : forall q m j, In (q, m) zs -> q / 8 <= j < (q + m) / 8 -> rd (SHADOW_OFF + j) = Some 0.
Proof.
intros q m j Hin Hj.
pose proof (proj1 (Forall_forall _ _) ZRD (q, m) Hin) as Hz. cbn [fst snd] in Hz. unfold zero_shadow in Hz.
pose proof (ZAL q m Hin) as Hq. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
assert (E : (q + m) / 8 = m / 8 + q / 8).
{ replace (q + m) with (m + q / 8 * 8) by lia. apply Z.div_add. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

(* The relaxed check is sound: it gives block_shadow, the fact globs_marked asks of each global. *)
Lemma glob_chk_relaxed_sound : forall q sz, glob_chk_relaxed zs cells (q, sz) = true ->
  block_shadow rd SHADOW_OFF q sz.
Proof.
intros q sz Hb. unfold glob_chk_relaxed in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
unfold shadow_of_addr.
destruct (i <? sz / 8) eqn:Hlt.
- (* a full granule: sz / 8 > 0, so the check found a zero-shadow range over all of them *)
  apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  pose proof (ZAL r0 m0 Hr) as Hr8. pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr.
  pose proof (Z.div_mod (r0 + m0) 8 ltac:(lia)) as Drm. pose proof (Z.mod_pos_bound (r0 + m0) 8 ltac:(lia)) as Brm.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  apply (sf_zs_rd r0 m0); [exact Hr | lia].
- (* the partial last granule: i = sz / 8 and sz mod 8 <> 0, so the check found its cell `sz mod 8` *)
  apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply sf_is_shv_eq in Hcb. subst c. subst i.
  rewrite (CRD _ _ Hc). rewrite sf_le_byte1 by lia. reflexivity.
Qed.

(* Every granule of [k, hi) that the scan accepts has a mapped shadow byte (GrantCloseChk.v:124, GrantClose.v:228). *)
Lemma sf_vscan_sound : forall fuel k hi, sf_vscan zs cells fuel k hi = true ->
  forall j, k <= j < hi -> rd (SHADOW_OFF + j) <> None.
Proof.
induction fuel as [|f IH]; intros k hi H j Hj; cbn [sf_vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (sf_zfind k zs) as [e|] eqn:Ez.
- destruct (sf_zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + rewrite (sf_zs_rd q m j Hin ltac:(lia)). discriminate.
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne].
  + apply existsb_exists in Hc as (c & Hin & Hb). destruct (sf_is_shc_eq _ _ Hb) as [v ->].
    rewrite (CRD _ _ Hin). discriminate.
  + apply (IH _ _ H). lia.
Qed.

(* The two facts globs_marked and img_shadow_vis ask of a reader, from the checks on its tables. *)
Lemma sf_globs_rd : forall G, forallb (glob_chk_relaxed zs cells) G = true ->
  forall q sz, In (q, sz) G -> block_shadow rd SHADOW_OFF q sz.
Proof.
intros G HG q sz Hin. exact (glob_chk_relaxed_sound q sz (proj1 (forallb_forall _ _) HG (q, sz) Hin)).
Qed.

Lemma sf_img_rd : forall lo hi, sf_vscan zs cells (Pos.to_nat 4096) (lo / 8) (hi / 8) = true ->
  8 * (hi / 8) = hi -> forall a, lo <= a < hi -> rd (shadow_addr a) <> None.
Proof.
intros lo hi Hs E8 a Ha. unfold shadow_addr.
assert (Hj : lo / 8 <= a / 8 < hi / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
exact (sf_vscan_sound _ _ _ Hs (a / 8) Hj).
Qed.
End sound.

(* ---- the checks, by computation on the copied tables (closed terms) -------------------------------------- *)
Lemma sf_zs_al : forall q m, In (q, m) TFIB_ZERO_SHADOW_A -> q mod 8 = 0.
Proof.
intros q m Hin.
assert (H : forallb (fun r => fst r mod 8 =? 0) TFIB_ZERO_SHADOW_A = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H (q, m) Hin) as Hb. cbn [fst] in Hb. apply Z.eqb_eq in Hb. exact Hb.
Qed.

(* All 40 registered globals of CODEC_GLOBS pass the relaxed check (none dropped). *)
Lemma codec_globs_chk : forallb (glob_chk_relaxed TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A) CODEC_GLOBS = true.
Proof. vm_compute. reflexivity. Qed.

(* Every granule of the image's read range [IMG_LO, IMG_TOP) is in a zero-shadow range or has a one-byte cell
   (504 scan steps). *)
Lemma codec_vscan : sf_vscan TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A (Pos.to_nat 4096) (IMG_LO / 8) (IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_img_top8 : 8 * (IMG_TOP / 8) = IMG_TOP.
Proof. vm_compute. reflexivity. Qed.

(* ---- the facts, over any segment list and any record that carries the copied tables -------------------------- *)
Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable CodecB : asyms.
Hypothesis HZS : as_zero_shadow CodecB = TFIB_ZERO_SHADOW_A.
Hypothesis HCONST : forall ly, exists pre, as_const CodecB ly = pre ++ TFIB_CONST_SHADOW_A.

(* In every AR state, the shadow of each range of the copied zero-shadow table reads zero (ARm's am_zshadow) ... *)
Lemma sf_ar_zrd : forall ly S (W : world segs) mem md, AR segs CodecB ly S W mem md ->
  Forall (fun r => zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r)) TFIB_ZERO_SHADOW_A.
Proof.
intros ly S W mem md HAR. pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as Hz.
unfold zshadow_ok, zero_shadow_ranges in Hz. rewrite HZS in Hz. exact (Forall_inv_tail Hz).
Qed.

(* ... and each copied one-byte shadow cell holds its byte (ARm's am_const; GrantClose.v:201). *)
Lemma sf_ar_crd : forall ly S (W : world segs) mem md, AR segs CodecB ly S W mem md ->
  forall s v, In (z1 (ANum s) v) TFIB_CONST_SHADOW_A -> aview segs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md HAR s v Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
destruct (HCONST ly) as [pre Hpre].
assert (Hin' : In (z1 (ANum s) v) (as_const CodecB ly)) by (rewrite Hpre; apply in_or_app; right; exact Hin).
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* GM: the runtime has marked each of the 40 registered globals, in every AR state. *)
Lemma codec_GM : globs_marked segs CodecB CODEC_GLOBS.
Proof.
intros ly S W mem md q sz Hin HAR.
exact (sf_globs_rd (aview segs (w_H W) mem) TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A sf_zs_al
  (sf_ar_zrd ly S W mem md HAR) (sf_ar_crd ly S W mem md HAR) CODEC_GLOBS codec_globs_chk q sz Hin).
Qed.

(* IV: every shadow byte of the image's read range is mapped, in every AR state. *)
Lemma codec_IV : img_shadow_vis segs CodecB.
Proof.
intros ly S W mem md a HAR Ha. unfold CodecRo.IMG_HI in Ha.
exact (sf_img_rd (aview segs (w_H W) mem) TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A sf_zs_al
  (sf_ar_zrd ly S W mem md HAR) (sf_ar_crd ly S W mem md HAR) IMG_LO IMG_TOP codec_vscan codec_img_top8 a Ha).
Qed.

(* in_zs of any range a zero-shadow range of the table holds, by computation (identity's ZS_STEM / ZS_NAME form). *)
Lemma codec_in_zs_of_b : forall a n,
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r))%bool TFIB_ZERO_SHADOW_A = true -> in_zs CodecB a n.
Proof.
intros a n H. unfold in_zs. rewrite HZS. exact (sf_in_zs_of_b TFIB_ZERO_SHADOW_A a n H).
Qed.
End L.

(* ---- satisfiability at the start state ------------------------------------------------------------------------- *)
(* The shadow of the start state as the copied tables state it: 0 at each granule of a zero-shadow range, the cell's
   byte at each one-byte cell, unmapped elsewhere. *)
Fixpoint sf_cell_at (s : Z) (cells : list acell) : option Z :=
  match cells with
  | [] => None
  | ACell (ANum s') (S O) (AV (ANum v)) :: r => if Z.eqb s' s then Some (YG0f.le_byte v 1 0) else sf_cell_at s r
  | _ :: r => sf_cell_at s r
  end.
Definition codec_start_shadow : YG0f.reader := fun s =>
  if existsb (fun r => (fst r / 8 <=? s - SHADOW_OFF) && (s - SHADOW_OFF <? (fst r + snd r) / 8))%bool
       TFIB_ZERO_SHADOW_A
  then Some 0 else sf_cell_at s TFIB_CONST_SHADOW_A.

Lemma codec_start_shadow_zs : forall s,
  existsb (fun r => (fst r / 8 <=? s - SHADOW_OFF) && (s - SHADOW_OFF <? (fst r + snd r) / 8))%bool
    TFIB_ZERO_SHADOW_A = true -> codec_start_shadow s = Some 0.
Proof. intros s H. unfold codec_start_shadow. rewrite H. reflexivity. Qed.

Lemma codec_start_zrd :
  Forall (fun r => zero_shadow codec_start_shadow SHADOW_OFF (fst r) (snd r)) TFIB_ZERO_SHADOW_A.
Proof.
apply Forall_forall. intros [q m] Hin. cbn [fst snd]. unfold zero_shadow, shadow_of_addr. intros i Hi.
pose proof (sf_zs_al q m Hin) as Hq. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
assert (E : (q + m) / 8 = m / 8 + q / 8).
{ replace (q + m) with (m + q / 8 * 8) by lia. apply Z.div_add. lia. }
apply codec_start_shadow_zs. apply existsb_exists. exists (q, m). split; [exact Hin|]. cbn [fst snd].
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* Every copied cell holds its byte at the start shadow: no zero-shadow range covers a cell with a nonzero byte and no
   two cells at one address disagree (checked by computation over the 488 cells). *)
Definition sf_cell_ok (c : acell) : bool :=
  match c with
  | ACell (ANum s) (S O) (AV (ANum v)) =>
      match codec_start_shadow s with Some x => Z.eqb x (YG0f.le_byte v 1 0) | None => false end
  | _ => false
  end.
Lemma codec_start_cells_chk : forallb sf_cell_ok TFIB_CONST_SHADOW_A = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_start_crd : forall s v, In (z1 (ANum s) v) TFIB_CONST_SHADOW_A ->
  codec_start_shadow s = Some (YG0f.le_byte v 1 0).
Proof.
intros s v Hin. pose proof (proj1 (forallb_forall _ _) codec_start_cells_chk _ Hin) as H.
unfold sf_cell_ok, z1, c1 in H. revert H. destruct (codec_start_shadow s) as [x|]; intros H; [|discriminate H].
apply Z.eqb_eq in H. subst x. reflexivity.
Qed.

(* Closed: the start state's shadow, as the copied tables state it, meets both premises of the checks (the zero-shadow
   ranges read zero and every cell holds its byte), and at it each of the 40 registered globals is marked and every
   shadow byte of the image's read range is mapped. So the facts codec_GM and codec_IV conclude are not vacuous: the
   tables a record carries under HZS / HCONST are consistent and give them. *)
Lemma codec_startup_sat : exists rd : YG0f.reader,
  Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) TFIB_ZERO_SHADOW_A /\
  (forall s v, In (z1 (ANum s) v) TFIB_CONST_SHADOW_A -> rd s = Some (YG0f.le_byte v 1 0)) /\
  (forall q sz, In (q, sz) CODEC_GLOBS -> block_shadow rd SHADOW_OFF q sz) /\
  (forall a, IMG_LO <= a < CodecRo.IMG_HI -> rd (shadow_addr a) <> None).
Proof.
exists codec_start_shadow. split; [exact codec_start_zrd|]. split; [exact codec_start_crd|]. split.
- exact (sf_globs_rd codec_start_shadow TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A sf_zs_al codec_start_zrd
    codec_start_crd CODEC_GLOBS codec_globs_chk).
- unfold CodecRo.IMG_HI. exact (sf_img_rd codec_start_shadow TFIB_ZERO_SHADOW_A TFIB_CONST_SHADOW_A sf_zs_al
    codec_start_zrd codec_start_crd IMG_LO IMG_TOP codec_vscan codec_img_top8).
Qed.
