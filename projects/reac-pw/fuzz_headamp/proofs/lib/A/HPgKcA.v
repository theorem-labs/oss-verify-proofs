(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf8.v, with its module paths and module names changed; 86 of its 105 lines of code are new or changed and 64 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the piece "the key and the channel" of the walk of LLVMFuzzerTestOneInput,
   lib/A/HPgSegM.v hq_piece_M3c_key_stmt (KEY 0x83168 -> VAL 0x83364 / RF 0x83460 / LATCH 0x83474), from its four
   parts: lib/A/HPgKcP1.v hk_P1 (KEY -> LATCH / BL), lib/A/HPgKcLoop.v hk_P2 and hk_P3 (one turn of read_channel's
   blanks loop and of its digits loop), lib/A/HPgKcP4.v hk_P4 (DOT -> RF / VAL), chained by lib/A/HPgKcCut.v
   hk_key_holds. Proves no function (kind: segment lemma).

   Section hypotheses (runtime facts, each at every float state where it names one):
   - errno_low: errno lies in the image (lib/Reusable/YCbq.v api_env), as lib/A/HPgCalls.v takes it;
   - STRNCMP: the strncmp wrapper's contract at 0x41ba4, lib/A/HPgCallsStr.v's Section hypothesis STRNCMP at
     segs = rsegs for every float state (reac-pw/fuzz_pin lib/A/PPgWrap.v astrncmp_realizes, unfolded);
   - STRCMP: the strcmp wrapper's contract at 0x41ba0, libreac/fuzz_identity lib/Reusable/AStrcmpDef.v
     astrcmp_realizes rsegs B 0x41ba0 for every float state, str_meet and strcmp_res unfolded (lib/A/HPgKcStr.v).
   The two texts below are the parts' own, word for word (hk_P1's and hk_P4's Section hypotheses). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgKcCut HPgKcLib HPgKcStr HPgKcP1 HPgKcLoop HPgKcP4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
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
SRr rsegs W (@cfg_at fx' rsegs A_STRNCMP regs mem md)
(fun (W' : world rsegs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
 AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Hypothesis STRCMP : forall fx' : YK11.FPState,
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre rsegs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
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
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview rsegs (w_H W) mem) x (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview rsegs (w_H W) mem) y (k + 1) ->
  SRr rsegs W (@cfg_at fx' rsegs A_STRCMP regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
       AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* M3c: the key and the channel of M03, KEY 0x83168 -> VAL / RF / LATCH *)
Theorem hk_key_A : @hq_piece_M3c_key_stmt fx rc SK rsegs B MT.
Proof.
exact (@hk_key_holds fx rc SK rsegs B MT
  (@hk_P1 fx rc SK B MT errno_low STRNCMP)
  (@hk_P2 fx rc SK B MT errno_low)
  (@hk_P3 fx rc SK B MT errno_low)
  (@hk_P4 fx rc SK B MT errno_low STRCMP)).
Qed.

End d.
End b.

Print Assumptions hk_key_A.
