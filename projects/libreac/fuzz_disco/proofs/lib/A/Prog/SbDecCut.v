(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 155 of its 181 lines of code are new or changed and 43 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SBD_P2 : Z := 0x68.
Definition SBD_P3 : Z := 0x110.
Definition SBD_P4 : Z := 0x150.
Definition SBD_P5 : Z := 0x254.
Definition sbd_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].
Definition sbd_sh_hdr : list Z := [241; 241; 241; 241; 4; 243; 243; 243].
Definition sbd_frame_magic : Z := 0x41b58ab3.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Record sbd_in : Type := SbdIn {
  si_fq : YK11.FPState; si_STK : Z; si_sp0 : Z; si_FP : list (Z * Z); si_ly : alayout; si_S : astate;
  si_W0 : world SEGS; si_mem0 : word -> option byte; si_md0 : Model; si_own : list (Z * Z);
  si_lyc : alayout; si_Sc : astate; si_W : world SEGS; si_memc : word -> option byte; si_mdc : Model; si_k : Z;
  si_regs : bvmap 5 word; si_ch : list (Z * Z * Z);
  si_A : Z; si_v : Z; si_md : Z; si_p : Z; si_cap : Z; si_n : Z; si_over : Z }.
Definition sbd_SP (X : sbd_in) : Z := spZ (si_regs X).
Definition sbd_SP1 (X : sbd_in) : Z := 32 * ((sbd_SP X + -96) / 32).
Definition sbd_F (X : sbd_in) (pos : Z) : Z := frame_addr (si_lyc X) 0 pos.
Definition sbd_FL (X : sbd_in) (pos : Z) : Z := flag_addr (si_lyc X) 0 pos.
Definition sbd_SH (X : sbd_in) (pos : Z) : Z := shadow_addr (sbd_F X pos).
Definition sbm_room (X : sbd_in) : Z := sb_dec_c.sb_dec_room (si_cap X) (si_n X).
Definition sbm_acc (X : sbd_in) : Z := sb_dec_c.sb_dec_acc (si_v X) (si_md X) (si_cap X) (si_n X).
Definition sbm_D (X : sbd_in) : list Z := sb_dec_c.sb_dec_D (si_v X) (si_md X).
Definition sbm_lsd (X : sbd_in) : list Z := sb_dec_c.sb_dec_lsd (si_v X) 3.
Definition sbm_over (X : sbd_in) : Z :=
  if sbm_room X <? Z.of_nat (length (sbm_D X)) then 1 else si_over X.
Definition sbd_rec (m : word -> option byte) (A p cap n over : Z) : Prop :=
  val_mem SEGS m A 8 p /\ val_mem SEGS m (A + 8) 8 cap /\ val_mem SEGS m (A + 16) 8 n /\
  val_mem SEGS m (A + 24) 4 over.
Definition sbd_shadow_at (W1 : world SEGS) (m : word -> option byte) (q : Z) (l : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W1) m (q + j) = Some (nth (Z.to_nat j) l 0).
Definition sbd_frame (X : sbd_in) (m : word -> option byte) : Prop :=
  forall j r, nth_error sbd_saved_regs j = Some r ->
    val_mem SEGS m (sbd_SP X - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (si_regs X) (Z_to_bv 5 r))).
Section h.
Variable B : asyms.
Definition sbd_cx (X : sbd_in) : Prop :=
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X) (si_own X)
    (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_mdc X) (si_k X) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (si_W X)) (si_memc X)) /\
  YK0s.ret_ok (getr (si_regs X) 1) /\ 4096 <= raZ (si_regs X) /\
  getr (si_regs X) 3 = w64 (as_gp B) /\ getr (si_regs X) 4 = w64 (as_tp B) /\
  getr (si_regs X) 10 = w64 (si_A X) /\ getr (si_regs X) 11 = w64 (si_v X) /\ getr (si_regs X) 12 = w64 (si_md X) /\
  achain (si_lyc X) (aview SEGS (w_H (si_W X)) (si_memc X)) (spZ (si_regs X)) (s0Z (si_regs X)) (si_ch X) /\
  spZ (si_regs X) mod 16 = 0 /\ si_sp0 X - si_STK X <= spZ (si_regs X) - SB_DEC_STK /\ spZ (si_regs X) <= si_sp0 X /\
  Z.of_nat (length (frames (si_Sc X))) <= 9 /\
  0 <= si_v X < 2 ^ 31 /\ (si_md X = 1 \/ si_md X = 2) /\
  si_A X mod 8 = 0 /\ (in_app (si_A X) 28 \/ (si_sp0 X - si_STK X <= si_A X /\ si_A X + 28 <= si_sp0 X)) /\
  si_A X + 28 <= 2 ^ 63 /\ (si_A X + 28 <= IMG_LO \/ IMG_TOP <= si_A X) /\
  (spZ (si_regs X) <= si_A X \/ si_A X + 28 <= spZ (si_regs X) - SB_DEC_STK) /\
  0 <= si_p X < 2 ^ 64 /\ 0 <= si_cap X < 2 ^ 64 /\ 0 <= si_n X /\ si_n X + 1 < 2 ^ 64 - 3 /\
  0 <= si_over X < 2 ^ 32 /\
  sbd_rec (mrestrict (w_H (si_W X)) (si_memc X)) (si_A X) (si_p X) (si_cap X) (si_n X) (si_over X) /\
  range_addressable (aview SEGS (w_H (si_W X)) (si_memc X)) SHADOW_OFF (si_A X) 28 /\
  (forall a, si_A X <= a < si_A X + 28 -> apresent (w_H (si_W X)) (si_memc X) a) /\
  (forall a, si_A X <= a < si_A X + 28 ->
     awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B (si_lyc X) (si_Sc X))
       (si_lyc X) (si_own X) a) /\
  (0 < sbm_room X ->
     si_p X + si_cap X <= 2 ^ 64 /\ in_app (si_p X + si_n X) (sbm_acc X) /\
     (si_p X + si_n X + sbm_acc X <= IMG_LO \/ IMG_TOP <= si_p X + si_n X) /\
     (si_p X + si_n X + sbm_acc X <= si_A X \/ si_A X + 28 <= si_p X + si_n X) /\
     (spZ (si_regs X) <= si_p X + si_n X \/ si_p X + si_n X + sbm_acc X <= spZ (si_regs X) - SB_DEC_STK) /\
     range_addressable (aview SEGS (w_H (si_W X)) (si_memc X)) SHADOW_OFF (si_p X + si_n X) (sbm_acc X) /\
     (forall a, si_p X + si_n X <= a < si_p X + si_n X + sbm_acc X ->
        awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B (si_lyc X) (si_Sc X))
          (si_lyc X) (si_own X) a /\ apresent (w_H (si_W X)) (si_memc X) a)).
Definition sbd_post (X : sbd_in) : world SEGS -> config -> Prop :=
  tsb_dec_post B (si_fq X) (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    (si_own X) (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_k X) (si_regs X)
    (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) (si_over X).
Definition sbd_kept_at (X : sbd_in) (memc1 : word -> option byte) : Prop :=
  sbd_kept B (si_lyc X) (si_Sc X) (si_W X) (si_memc X) memc1 (sbd_SP X - SB_DEC_STK) (sbd_SP X)
    (sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X)).
Definition sbd_mid (X : sbd_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (memc1 : word -> option byte)
  (mdc1 : Model) (sh : list Z) : Prop :=
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) memc1 mdc1 (si_k X) /\
  frames Sc1 = (0, pos) :: frames (si_Sc X) /\
  ablocks B lyc1 Sc1 = ablocks B (si_lyc X) (si_Sc X) /\
  (forall c p, frame_addr lyc1 c p = frame_addr (si_lyc X) c p) /\
  (forall c p, flag_addr lyc1 c p = flag_addr (si_lyc X) c p) /\
  sbd_kept_at X memc1 /\
  sbd_frame X (mrestrict (w_H (si_W X)) memc1) /\
  val_mem SEGS (mrestrict (w_H (si_W X)) memc1) (sbd_F X pos + 56) 8 (sbd_FL X pos) /\
  sbd_shadow_at (si_W X) memc1 (sbd_SH X pos) sh.
Definition sbd_base (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
  getr regs1 2 = w64 (sbd_SP1 X) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (sbd_SP X) /\ getr regs1 9 = w64 (sbd_SP1 X) /\ getr regs1 18 = w64 (si_A X) /\
  getr regs1 21 = w64 SHADOW_OFF /\ getr regs1 10 = w64 (sbd_F X pos) /\
  (forall r, 24 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr (si_regs X) (Z_to_bv 5 r)).
Definition sbd_st2 (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid X pos lyc1 Sc1 memc1 mdc1 (repeat 0 8) /\ sbd_base X pos regs1 /\
  getr regs1 19 = w64 (si_md X) /\ getr regs1 20 = w64 (si_v X) /\
  sbd_rec (mrestrict (w_H (si_W X)) memc1) (si_A X) (si_p X) (si_cap X) (si_n X) (si_over X).
Definition sbd_st3 (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr /\ sbd_base X pos regs1 /\
  getr regs1 19 = w64 (si_md X) /\ getr regs1 20 = w64 (si_v X) /\
  getr regs1 16 = w64 (sbd_F X pos) /\ getr regs1 17 = w64 (sbd_SH X pos) /\
  getr regs1 14 = w64 (sbd_F X pos + 32) /\ getr regs1 15 = w64 0 /\ getr regs1 11 = w64 0 /\
  getr regs1 5 = w64 1717986919 /\ getr regs1 12 = w64 10 /\ getr regs1 13 = w64 (-20) /\ getr regs1 6 = w64 2 /\
  sbd_rec (mrestrict (w_H (si_W X)) memc1) (si_A X) (si_p X) (si_cap X) (si_n X) (si_over X).
Definition sbd_st4 (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr /\ sbd_base X pos regs1 /\
  getr regs1 19 = w64 (si_md X) /\
  getr regs1 16 = w64 (sbd_F X pos) /\ getr regs1 17 = w64 (sbd_SH X pos) /\
  getr regs1 14 = w64 (sbd_F X pos + 32) /\
  getr regs1 11 = w64 (Z.of_nat (length (sbm_lsd X))) /\ getr regs1 15 = w64 (Z.of_nat (length (sbm_lsd X))) /\
  garr8 SEGS (mrestrict (w_H (si_W X)) memc1) (sbd_F X pos + 32) (sbm_lsd X) /\
  sbd_rec (mrestrict (w_H (si_W X)) memc1) (si_A X) (si_p X) (si_cap X) (si_n X) (si_over X).
Definition sbd_st5 (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  sbd_mid X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr /\ sbd_base X pos regs1 /\
  getr regs1 16 = w64 (sbd_F X pos) /\ getr regs1 17 = w64 (sbd_SH X pos) /\
  sbd_rec (mrestrict (w_H (si_W X)) memc1) (si_A X) (si_p X) (si_cap X) (si_n X + sbm_acc X) (sbm_over X) /\
  (0 < sbm_room X ->
     garr8 SEGS (mrestrict (w_H (si_W X)) memc1) (si_p X + si_n X) (firstn (Z.to_nat (sbm_acc X)) (sbm_D X))).
Definition sbd_cfg (X : sbd_in) (off : Z) (regs1 : bvmap 5 word) (memc1 : word -> option byte) (mdc1 : Model)
  : config :=
  cfg_at (fx := si_fq X) SEGS (BASE + AF_sb_dec + off) regs1 memc1 mdc1.
Definition sbd_at2 (X : sbd_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => W1 = si_W X /\ exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_P2 regs1 memc1 mdc1 /\ sbd_st2 X pos regs1 lyc1 Sc1 memc1 mdc1.
Definition sbd_at3 (X : sbd_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => W1 = si_W X /\ exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_P3 regs1 memc1 mdc1 /\ sbd_st3 X pos regs1 lyc1 Sc1 memc1 mdc1.
Definition sbd_at4 (X : sbd_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => W1 = si_W X /\ exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_P4 regs1 memc1 mdc1 /\ sbd_st4 X pos regs1 lyc1 Sc1 memc1 mdc1.
Definition sbd_at5 (X : sbd_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => W1 = si_W X /\ exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = sbd_cfg X SBD_P5 regs1 memc1 mdc1 /\ sbd_st5 X pos regs1 lyc1 Sc1 memc1 mdc1.
Definition sbd_seg1_stmt : Prop :=
  forall X : sbd_in, sbd_cx X ->
  SRr SEGS (si_W X) (cfg_at (fx := si_fq X) SEGS (BASE + AF_sb_dec) (si_regs X) (si_memc X) (si_mdc X))
    (sbd_at2 X).
Definition sbd_seg2_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 memc1 mdc1, sbd_cx X -> sbd_st2 X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  SRr SEGS (si_W X) (sbd_cfg X SBD_P2 regs1 memc1 mdc1) (sbd_at3 X).
Definition sbd_seg3_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 memc1 mdc1, sbd_cx X -> sbd_st3 X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  SRr SEGS (si_W X) (sbd_cfg X SBD_P3 regs1 memc1 mdc1) (sbd_at4 X).
Definition sbd_seg4_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 memc1 mdc1, sbd_cx X -> sbd_st4 X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  SRr SEGS (si_W X) (sbd_cfg X SBD_P4 regs1 memc1 mdc1) (sbd_at5 X).
Definition sbd_seg5_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 memc1 mdc1, sbd_cx X -> sbd_st5 X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  SRr SEGS (si_W X) (sbd_cfg X SBD_P5 regs1 memc1 mdc1) (sbd_post X).
End h.
End f.
End d.
