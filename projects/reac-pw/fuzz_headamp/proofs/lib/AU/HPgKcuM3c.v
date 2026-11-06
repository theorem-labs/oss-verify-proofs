(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf8.v, with its module paths and module names changed; 86 of its 105 lines of code are new or changed and 64 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgKcA.v; 27 of its 112 lines of code are new or changed and 20 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the piece "the key and the channel" of the walk of LLVMFuzzerTestOneInput
   (lib/AU/HPgSegM.v hqu_piece_M3c_key_stmt: KEY 0x83260 -> VAL 0x83490 / RF 0x836a0 / LATCH 0x836b4), at
   segs = Img0U.rsegs. Proves no function (kind: segment lemma).

   This file only joins the four parts. The split is lib/AU/HPgKcuCut.v, which also proves hku_key_holds: the
   four part statements give the piece, by induction on the two loop indices of read_channel. The parts:
     part 1  KEY 0x83260 .. BL 0x832e8   lib/AU/HPgKcuP1.v   hku_P1 (the eight saves, the strncmp call at
                                                             0x8329c, x->keys++, the constants)
     part 2  BL 0x832e8 .. DG 0x83364    lib/AU/HPgKcuLoop.v hku_P2 (one turn of the blanks loop, the sign)
     part 3  DG 0x83364 .. DOT 0x833c8   lib/AU/HPgKcuLoop.v hku_P3 (one turn of the digits loop)
     part 4  DOT 0x833c8 .. VAL / RF     lib/AU/HPgKcuP4.v   hku_P4 (the '.' test, the save of big, the strcmp
                                                             chain at 0x83418 / 0x8342c / 0x83440, the range)
   The shared lemmas are lib/AU/HPgKcuLib.v; the two call adapters are lib/AU/HPgKcuNcmp.v (strncmp, 0x41c24) and
   lib/AU/HPgKcuScmp.v (strcmp, 0x41c20). The ten UBSan trap sites of the piece (0x83264, 0x832b8, 0x832d8,
   0x8330c, 0x8334c, 0x833a0, 0x833b4, 0x833e4, 0x833f0, 0x83400) are each shown not taken inside its part.

   Section hypotheses, each with the exact type of the part that takes it:
   - errno_low : api_env rsegs B (lib/Reusable/YCbq.v api_env: errno lies in the image), as lib/A/HPgCalls.v's.
   - STRNCMP: the strncmp wrapper's contract at image B's trampoline 0x41c24, at every float state (lib/AU/HPgKcuP1.v
     and lib/AU/HPgKcuNcmp.v; reac-pw/fuzz_pin lib/A/PPgWrap.v astrncmp_realizes, with awrap_str,
     awrap_post and libreac/fuzz_identity lib/A/Rt/WrapRo.v aro_unowned unfolded and beta-reduced).
   - STRCMP: the strcmp wrapper's contract at image B's 0x41c20, at every float state (lib/AU/HPgKcuP4.v and
     lib/AU/HPgKcuScmp.v; libreac/fuzz_identity lib/Reusable/AStrcmpDef.v astrcmp_realizes at origin/ossv/recipes
     2d2ff01bb6f, with str_meet and strcmp_res unfolded and beta-reduced).
   segs_low (the image lies below the shadow map) is not a hypothesis here: lib/AU/HPgSteps.v img_segs_low proves
   it for rsegs. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgKcuCut HPgKcuLib HPgKcuNcmp HPgKcuScmp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgKcuLoop HPgKcuP1 HPgKcuP4.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
(* lib/AU/HPgKcuP1.v's STRNCMP, word for word *)
Hypothesis STRNCMP : forall fx' : YK11.FPState,
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
ecall_pre rsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok rsegs W regs mem x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview rsegs (w_H W) mem) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview rsegs (w_H W) mem a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H W) mem) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok rsegs W regs mem y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview rsegs (w_H W) mem) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview rsegs (w_H W) mem a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))) ->
SRr rsegs W (@cfg_at fx' rsegs B_STRNCMP regs mem md)
(fun (W' : world rsegs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
 AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* lib/AU/HPgKcuP4.v's STRCMP, word for word *)
Hypothesis STRCMP : forall fx' : YK11.FPState,
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre rsegs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
  (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  (0 <= k /\
   (forall i, 0 <= i < k -> exists b, aview rsegs (w_H W) mem (x + i) = Some b /\
                                      aview rsegs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
   aview rsegs (w_H W) mem (x + k) = Some c1 /\ aview rsegs (w_H W) mem (y + k) = Some c2 /\
   (c1 <> c2 \/ c1 = 0)) ->
  src_ok rsegs W regs mem x (k + 1) -> src_ok rsegs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) x (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (k + 1) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) y (k + 1) ->
  SRr rsegs W (@cfg_at fx' rsegs B_STRCMP regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
       AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* the piece "the key and the channel" of M03, image B *)
Theorem hqu_piece_M3c_key : hqu_piece_M3c_key_stmt rsegs B MT.
Proof.
apply (hku_key_holds rsegs B MT).
- apply hku_P1; assumption.
- exact (hku_P2 B MT errno_low).
- exact (hku_P3 B MT errno_low).
- apply hku_P4; assumption.
Qed.

End d.
End b.

Check @hqu_piece_M3c_key.
Print Assumptions hqu_piece_M3c_key.
