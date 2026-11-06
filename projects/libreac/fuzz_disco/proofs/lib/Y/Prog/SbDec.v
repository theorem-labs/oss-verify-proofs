(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 227 of its 280 lines of code are new or changed and 3287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/SbDec.v, with its module paths, module names and numbers changed; 20 of its 109 lines of code are new or changed and 191 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Definition SB_DEC_STK : Z := 160 + ESTACK.
Definition tsb_dec_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (A v md p cap n over : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
       ~ (A + 16 <= a < A + 28) ->
       ~ (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
       ~ (A + 16 <= b + i < A + 28) ->
       ~ (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= b + i < p + n + sb_dec_c.sb_dec_acc v md cap n) ->
       aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
    (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall cid pos a, In (cid, pos) (frames Sc) ->
       (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
       ~ (A + 16 <= a < A + 28) ->
       ~ (0 < sb_dec_c.sb_dec_room cap n /\ p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
       apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
    (forall a, spZ regs - SB_DEC_STK <= a < spZ regs -> apresent (w_H W2) mem2 a) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) A 8 p /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (A + 8) 8 cap /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (A + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (A + 24) 4
      (if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else over) /\
    (0 < sb_dec_c.sb_dec_room cap n ->
       garr8 SEGS (mrestrict (w_H W2) mem2) (p + n)
         (firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md))).
Definition tsb_dec_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (A v md p cap n over : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 A -> getr regs 11 = w64 v -> getr regs 12 = w64 md ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z (regupd regs 8 (Z_to_bv 64 0))) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  Z.of_nat (length (frames Sc)) <= 9 ->
  0 <= v < 2 ^ 31 -> (md = 1 \/ md = 2) ->
  0 < A -> A mod 8 = 0 -> A + 28 <= 2 ^ 63 -> amem_range A 28 -> off_img A 28 ->
  (spZ regs <= A \/ A + 28 <= spZ regs - SB_DEC_STK) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 1 < 2 ^ 64 - 3 -> 0 <= over < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 over ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) A 28 ->
  (forall a, A <= a < A + 28 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  (0 < sb_dec_c.sb_dec_room cap n ->
     0 < p /\ p + n + sb_dec_c.sb_dec_acc v md cap n <= 2 ^ 63 /\
     amem_range (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\ off_img (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= A \/ A + 28 <= p + n) /\
     (spZ regs <= p + n \/ p + n + sb_dec_c.sb_dec_acc v md cap n <= spZ regs - SB_DEC_STK) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     shadow_hull_vis (aview SEGS (w_H W) memc) (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (forall a, p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_dec) regs memc mdc)
    (tsb_dec_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs A v md p cap n over).

End h.
End f.
End d.
