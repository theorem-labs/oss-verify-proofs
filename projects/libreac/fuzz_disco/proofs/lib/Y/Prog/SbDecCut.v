(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 452 of its 506 lines of code are new or changed and 3286 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/SbCh.v; 158 of its 194 lines of code are new or changed and 470 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition SBD_PA : Z := 0x74.
Definition SBD_PL : Z := 0x184.
Definition SBD_PE : Z := 0x1c0.
Definition sbd_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26].
Definition sbd_sh : list Z := [241; 241; 241; 241; 4; 243; 243; 243].
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Record sbd_in : Type := SbdIn {
  si_fq : YK11.FPState; si_STK : Z; si_sp0 : Z; si_FP : list (Z * Z); si_ly : alayout; si_S : astate;
  si_W0 : world SEGS; si_mem0 : word -> option byte; si_md0 : Model; si_own : list (Z * Z);
  si_lyc : alayout; si_Sc : astate; si_W : world SEGS; si_memc : word -> option byte; si_mdc : Model; si_k : Z;
  si_regs : bvmap 5 word;
  si_A : Z; si_v : Z; si_md : Z; si_p : Z; si_cap : Z; si_n : Z; si_over : Z }.
Definition sbd_SP (X : sbd_in) : Z := spZ (si_regs X).
Definition sbd_S1 (X : sbd_in) : Z := 32 * ((sbd_SP X - 128) / 32).
Definition sbd_F (X : sbd_in) (pos : Z) : Z := frame_addr (si_lyc X) 0 pos.
Definition sbd_FL (X : sbd_in) (pos : Z) : Z := flag_addr (si_lyc X) 0 pos.
Definition sbd_SH (X : sbd_in) (pos : Z) : Z := shadow_addr (sbd_F X pos).
Definition sbd_D (X : sbd_in) : list Z := sb_dec_c.sb_dec_D (si_v X) (si_md X).
Definition sbd_L (X : sbd_in) : Z := Z.of_nat (length (sbd_D X)).
Definition sbd_room (X : sbd_in) : Z := sb_dec_c.sb_dec_room (si_cap X) (si_n X).
Definition sbd_acc (X : sbd_in) : Z := sb_dec_c.sb_dec_acc (si_v X) (si_md X) (si_cap X) (si_n X).
Definition sbd_ne (X : sbd_in) (e : Z) : Z := si_n X + Z.min e (sbd_room X).
Definition sbd_ov (X : sbd_in) (e : Z) : Z := if sbd_room X <? e then 1 else si_over X.
Definition sbd_Er (X : sbd_in) (a : Z) : Prop :=
  (si_A X + 16 <= a < si_A X + 28) \/
  (0 < sbd_room X /\ si_p X + si_n X <= a < si_p X + si_n X + sbd_acc X).
Definition sbd_shadow_at (W1 : world SEGS) (m : word -> option byte) (q : Z) (l : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W1) m (q + j) = Some (nth (Z.to_nat j) l 0).
Definition sbd_frame (X : sbd_in) (m : word -> option byte) : Prop :=
  forall j r, nth_error sbd_saved_regs j = Some r ->
    val_mem SEGS m (sbd_SP X - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (si_regs X) (Z_to_bv 5 r))).
Definition sbd_cfg (X : sbd_in) (off : Z) (regs1 : bvmap 5 word) (memc1 : word -> option byte) (mdc1 : Model)
  : config :=
  cfg_at (fx := si_fq X) SEGS (BASE + AF_both3_sb_dec + off) regs1 memc1 mdc1.
Definition sbd_rec (X : sbd_in) (W1 : world SEGS) (memc1 : word -> option byte) (e : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H W1) memc1) (si_A X) 8 (si_p X) /\
  val_mem SEGS (mrestrict (w_H W1) memc1) (si_A X + 8) 8 (si_cap X) /\
  val_mem SEGS (mrestrict (w_H W1) memc1) (si_A X + 16) 8 (sbd_ne X e) /\
  val_mem SEGS (mrestrict (w_H W1) memc1) (si_A X + 24) 4 (sbd_ov X e) /\
  (0 < sbd_room X ->
     garr8 SEGS (mrestrict (w_H W1) memc1) (si_p X + si_n X)
       (firstn (Z.to_nat (Z.min e (sbd_room X))) (sbd_D X))).
Section h.
Variable B : asyms.
Definition sbd_recP (X : sbd_in) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS) (memc1 : word -> option byte)
  (own1 : list (Z * Z)) : Prop :=
  range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (si_A X) 28 /\
  shadow_hull_vis (aview SEGS (w_H W1) memc1) (si_A X) 28 /\
  (forall a, si_A X <= a < si_A X + 28 ->
     awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B lyc1 Sc1) lyc1 own1 a /\
     apresent (w_H W1) memc1 a).
Definition sbd_outP (X : sbd_in) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS) (memc1 : word -> option byte)
  (own1 : list (Z * Z)) : Prop :=
  range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (si_p X + si_n X) (sbd_acc X) /\
  shadow_hull_vis (aview SEGS (w_H W1) memc1) (si_p X + si_n X) (sbd_acc X) /\
  (forall a, si_p X + si_n X <= a < si_p X + si_n X + sbd_acc X ->
     awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B lyc1 Sc1) lyc1 own1 a /\
     apresent (w_H W1) memc1 a).
Definition sbd_cx (X : sbd_in) : Prop :=
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X) (si_own X)
    (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_mdc X) (si_k X) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (si_W X)) (si_memc X)) /\
  YK0s.ret_ok (getr (si_regs X) 1) /\ 4096 <= raZ (si_regs X) /\
  getr (si_regs X) 3 = w64 (as_gp B) /\ getr (si_regs X) 4 = w64 (as_tp B) /\
  getr (si_regs X) 10 = w64 (si_A X) /\ getr (si_regs X) 11 = w64 (si_v X) /\
  getr (si_regs X) 12 = w64 (si_md X) /\
  sbd_SP X mod 16 = 0 /\ si_sp0 X - si_STK X <= sbd_SP X - SB_DEC_STK /\ sbd_SP X <= si_sp0 X /\
  Z.of_nat (length (frames (si_Sc X))) <= 9 /\
  0 <= si_v X < 2 ^ 31 /\ (si_md X = 1 \/ si_md X = 2) /\
  0 < si_A X /\ si_A X mod 8 = 0 /\ si_A X + 28 <= 2 ^ 63 /\ amem_range (si_A X) 28 /\ off_img (si_A X) 28 /\
  (sbd_SP X <= si_A X \/ si_A X + 28 <= sbd_SP X - SB_DEC_STK) /\
  0 <= si_p X < 2 ^ 64 /\ 0 <= si_cap X < 2 ^ 64 /\ 0 <= si_n X /\ si_n X + 1 < 2 ^ 64 - 3 /\
  0 <= si_over X < 2 ^ 32 /\
  sbd_rec X (si_W X) (si_memc X) 0 /\
  sbd_recP X (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_own X) /\
  (0 < sbd_room X ->
     0 < si_p X /\ si_p X + si_n X + sbd_acc X <= 2 ^ 63 /\
     amem_range (si_p X + si_n X) (sbd_acc X) /\ off_img (si_p X + si_n X) (sbd_acc X) /\
     (si_p X + si_n X + sbd_acc X <= si_A X \/ si_A X + 28 <= si_p X + si_n X) /\
     (sbd_SP X <= si_p X + si_n X \/ si_p X + si_n X + sbd_acc X <= sbd_SP X - SB_DEC_STK) /\
     sbd_outP X (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_own X)).
Definition sbd_post (X : sbd_in) : world SEGS -> config -> Prop :=
  tsb_dec_post B (si_fq X) (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    (si_own X) (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_k X) (si_regs X)
    (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) (si_over X).
Definition sbd_kept (X : sbd_in) (W1 : world SEGS) (memc1 : word -> option byte) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sbd_SP X - SB_DEC_STK <= a < sbd_SP X) -> ~ sbd_Er X a ->
     aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (si_W X)) (si_memc X) a) /\
  (forall b m j, In (b, m) (ablocks B (si_lyc X) (si_Sc X)) -> 0 <= j < req_size m -> ~ sbd_Er X (b + j) ->
     aview SEGS (w_H W1) memc1 (b + j) = aview SEGS (w_H (si_W X)) (si_memc X) (b + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (si_W X)) (si_memc X) a) /\
  (forall cid pos a, In (cid, pos) (frames (si_Sc X)) ->
     (in_zr a (frame_rng (si_lyc X) (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr (si_lyc X) cid pos), fs_frame_bytes cid / 8)) ->
     ~ sbd_Er X a -> aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (si_W X)) (si_memc X) a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sbd_SP X - SB_DEC_STK <= a < sbd_SP X) ->
     apresent (w_H (si_W X)) (si_memc X) a -> apresent (w_H W1) memc1 a) /\
  (forall a, sbd_SP X - SB_DEC_STK <= a < sbd_SP X -> apresent (w_H W1) memc1 a).
Definition sbd_mid0 (X : sbd_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W1 memc1 mdc1 (si_k X) /\
  frames Sc1 = (0, pos) :: frames (si_Sc X) /\
  ablocks B lyc1 Sc1 = ablocks B (si_lyc X) (si_Sc X) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) memc1) /\
  sbd_kept X W1 memc1 /\
  sbd_frame X (mrestrict (w_H W1) memc1) /\
  val_mem SEGS (mrestrict (w_H W1) memc1) (sbd_F X pos + 56) 8 (sbd_FL X pos) /\
  sbd_recP X lyc1 Sc1 W1 memc1 ((0, pos) :: si_own X) /\
  (0 < sbd_room X -> sbd_outP X lyc1 Sc1 W1 memc1 ((0, pos) :: si_own X)).
Definition sbd_rbase (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
  getr regs1 2 = w64 (sbd_S1 X) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (sbd_SP X) /\ getr regs1 9 = w64 (sbd_S1 X) /\ getr regs1 18 = w64 (sbd_F X pos) /\
  getr regs1 19 = w64 (si_A X) /\ getr regs1 22 = w64 SHADOW_OFF /\ getr regs1 23 = w64 (sbd_F X pos) /\
  getr regs1 24 = w64 (sbd_SH X pos) /\ getr regs1 25 = w64 (sbd_F X pos + 32) /\
  getr regs1 26 = w64 (- (sbd_F X pos + 32) - 1) /\ getr regs1 27 = getr (si_regs X) 27.
Definition sbd_stA (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid0 X pos lyc1 Sc1 W1 memc1 mdc1 /\ sbd_rec X W1 memc1 0 /\
  getr regs1 2 = w64 (sbd_S1 X) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (sbd_SP X) /\ getr regs1 9 = w64 (sbd_S1 X) /\ getr regs1 10 = w64 (sbd_F X pos) /\
  getr regs1 19 = w64 (si_A X) /\ getr regs1 20 = w64 (si_md X) /\ getr regs1 21 = w64 (si_v X) /\
  getr regs1 22 = w64 SHADOW_OFF /\ getr regs1 27 = getr (si_regs X) 27.
Definition sbd_stL (X : sbd_in) (pos j e : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid0 X pos lyc1 Sc1 W1 memc1 mdc1 /\ sbd_shadow_at W1 memc1 (sbd_SH X pos) sbd_sh /\
  sbd_rbase X pos regs1 /\ getr regs1 20 = w64 j /\ getr regs1 21 = w64 (-1) /\
  0 <= j /\ 0 <= e /\ j + e + 1 = sbd_L X /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (sbd_F X pos + 32) (rev (sbd_D X)) /\
  sbd_rec X W1 memc1 e.
Definition sbd_stE (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid0 X pos lyc1 Sc1 W1 memc1 mdc1 /\ sbd_shadow_at W1 memc1 (sbd_SH X pos) sbd_sh /\
  sbd_rbase X pos regs1 /\ sbd_rec X W1 memc1 (sbd_L X).
Definition sbd_atA (X : sbd_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_PA regs1 memc1 mdc1 /\ sbd_stA X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition sbd_atL (X : sbd_in) (j e : Z) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_PL regs1 memc1 mdc1 /\ sbd_stL X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition sbd_atE (X : sbd_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_PE regs1 memc1 mdc1 /\ sbd_stE X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition sbd_seg1_stmt : Prop :=
  forall X : sbd_in, sbd_cx X ->
  SRr SEGS (si_W X) (cfg_at (fx := si_fq X) SEGS (BASE + AF_both3_sb_dec) (si_regs X) (si_memc X) (si_mdc X))
    (sbd_atA X).
Definition sbd_seg2_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, sbd_cx X -> sbd_stA X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (sbd_cfg X SBD_PA regs1 memc1 mdc1) (sbd_atL X (sbd_L X - 1) 0).
Definition sbd_segL_stmt : Prop :=
  forall X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1, sbd_cx X -> sbd_stL X pos j e regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (sbd_cfg X SBD_PL regs1 memc1 mdc1)
    (fun W2 c2 => (0 < j /\ sbd_atL X (j - 1) (e + 1) W2 c2) \/ (j = 0 /\ sbd_atE X W2 c2)).
Definition sbd_segE_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, sbd_cx X -> sbd_stE X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (sbd_cfg X SBD_PE regs1 memc1 mdc1) (sbd_post X).
End h.
End f.
End d.
