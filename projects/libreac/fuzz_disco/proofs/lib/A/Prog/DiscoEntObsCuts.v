(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 245 of its 278 lines of code are new or changed and 1245 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition sr_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | _ => SOff (AT_X + r) 0
  end.
Definition obs_sr : list sv := map sr_x (seq 0 32).
Definition obs_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma d_E_atoms : forall cx E, d_E cx E ->
  ew E AT_A = Z_to_bv 64 (d_A cx) /\ ew E AT_F = Z_to_bv 64 (d_FB cx) /\
  ew E AT_SH = Z_to_bv 64 (shadow_addr (d_FB cx)) /\ ew E 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros cx E (_ & H32 & _ & HA & HF & HS). repeat split; assumption. Qed.

Lemma regs_ok_obs : forall cx E regs, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs)) obs_sr regs.
Proof.
intros cx E regs HE HL HA.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth obs_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.


#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
Definition oc (cx : dcx) (h i n now op nb fr len : Z) (Sg T : list byte) (regs : bvmap 5 word)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ (op mod 4 = 0 \/ op mod 4 = 1) /\ 0 <= op < 256 /\
  d_rL B cx regs /\ d_sp0 cx i now W3 mem3 /\ d_frm cx nb fr len W3 mem3 /\
  length Sg = 24%nat /\ garr8 SEGS (rd W3 mem3) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) /\
  sighting_facts Sg (firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) len 0 /\
  val_mem SEGS (rd W3 mem3) (d_A cx + 248) 8 (d_cur cx nb) /\ val_mem SEGS (rd W3 mem3) (d_A cx + 336) 8 len /\
  val_mem SEGS (rd W3 mem3) (d_A cx + 368) 8 nb /\ val_mem SEGS (rd W3 mem3) (d_A cx + 280) 8 fr /\
  len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7) /\
  length T = 400%nat /\ garr8 SEGS (rd W3 mem3) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) /\ table_ok T /\
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W3 mem3.
Definition ob_c0 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx OBS_OFF kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\ dR_obs cx regs).
Definition ob_c1 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_find_entry kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\ dR_obs cx regs /\
    getr regs 1 = w64 (BASE + (OBS_OFF + 16)) /\ getr regs 10 = w64 (d_obj cx OT) /\
    getr regs 11 = w64 (d_obj cx OS) /\ getr regs 27 = w64 (d_obj cx OT)).
Definition u64 (z : Z) : Z := z mod 2 ^ 64.
Definition oldv (a v : Z) : Z := if a <? 0 then 0 else v.
Definition ob_sp22 (cx : dcx) (T : list byte) (ai : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 88) 8 (u64 (16 * ai)) /\ val_mem SEGS (rd W m) (d_A cx + 80) 8 (u64 (64 * ai)) /\
  val_mem SEGS (rd W m) (d_A cx + 392) 8 (u64 (oldv ai (role_of_e T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 136) 8 (u64 (oldv ai (hd_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 128) 8 (u64 (oldv ai (din_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 120) 8 (u64 (oldv ai (dout_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 112) 8 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 104) 8 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 224) 8 (u64 (oldv ai (s32_at T (48 * ai + 20)))) /\
  val_mem SEGS (rd W m) (d_A cx + 96) 8 (u64 (oldv ai (owned_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 72) 8 (u64 (oldv ai (u_at T (48 * ai + 32) 8))).
Definition obT (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  length T = 400%nat /\ table_ok T /\ find_res T (s_mac Sg) ai /\ (ow = 0 \/ ow = 1) /\ ob_sp22 cx T ai W m /\
  val_mem SEGS (rd W m) (d_A cx + 408) 8 ow /\ reac_disco_table_observe_c.observe_model T Sg ow now T' ret.
Definition ob_c2 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx (OBS_OFF + 16) kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T ai w,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\
    getr regs 26 = w64 (d_obj cx OOUR) /\ getr regs 27 = w64 (d_obj cx OT) /\
    getr regs 10 = w64 ai /\ find_res T (s_mac Sg) ai /\ val_mem SEGS (rd W3 mem3) (d_A cx + 408) 8 w).
Definition ob_c3 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_reac_disco_table_observe kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T ai ow,
    oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    find_res T (s_mac Sg) ai /\ (ow = 0 \/ ow = 1) /\ ob_sp22 cx T ai W3 mem3 /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 408) 8 ow /\
    getr regs 1 = w64 (BASE + 0x1804) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS) /\
    getr regs 12 = w64 ow /\ getr regs 13 = w64 now /\ getr regs 19 = w64 (n_of T) /\ getr regs 24 = w64 (ov_of T) /\
    getr regs 23 = w64 (s32_at T 392) /\ getr regs 22 = w64 ai /\ getr regs 27 = w64 (d_obj cx OT)).
Definition ob_rT (T : list byte) (ai : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = w64 (n_of T) /\ getr regs 22 = w64 ai.
Definition ob_c4 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x1804 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\
    getr regs 10 = w64 ret /\ getr regs 24 = w64 (ov_of T) /\ getr regs 23 = w64 (s32_at T 392) /\
    getr regs 27 = w64 (d_obj cx OT)).
Definition ob_c5 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_check_table kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\
    getr regs 1 = w64 (BASE + 0x181c) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 21 = w64 ret /\
    getr regs 24 = w64 (ov_of T) /\ getr regs 23 = w64 (s32_at T 392) /\ getr regs 27 = w64 (d_obj cx OT)).
Definition ob_c6 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x181c kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\ getr regs 21 = w64 ret /\
    getr regs 24 = w64 (ov_of T) /\ getr regs 23 = w64 (s32_at T 392) /\ getr regs 27 = w64 (d_obj cx OT)).
Definition ob_rX (nb fr len ret : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 21 = w64 ret /\ getr regs 23 = w64 nb /\ getr regs 24 = w64 len /\ getr regs 27 = w64 fr.
Definition ob_c7 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_find_entry kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
    0 <= ai /\ role_of_e T ai = 1 /\
    getr regs 1 = w64 (BASE + 0x1874) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS)).
Definition ob_c8 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x1874 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret idx,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
    0 <= ai /\ role_of_e T ai = 1 /\ getr regs 10 = w64 idx /\ find_res T' (s_mac Sg) idx).
Definition ob_c9 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x18b8 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
    0 <= ai /\ getr regs 13 = w64 (d_obj cx OT)).
Definition ob_c10 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x1b78 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    obT cx now Sg T T' ai ow ret W3 mem3 /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
    ai < 0 /\ getr regs 13 = w64 (d_obj cx OT) /\ getr regs 14 = w64 (d_cur cx nb)).
Definition ob_seg89 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c8 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c9 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg23 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c2 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c3 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg45 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c4 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c5 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg67 : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c6 cx h i n now op nb fr len Sg kmax accmax W c ->
  SRr SEGS W c (fun W' c' => ob_c7 cx h i n now op nb fr len Sg kmax accmax W' c' \/
    ob_c9 cx h i n now op nb fr len Sg kmax accmax W' c' \/ ob_c10 cx h i n now op nb fr len Sg kmax accmax W' c').
Definition ob_seg9r : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  ob_c9 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).
Definition ob_seg10r : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  ob_c10 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).
Definition ob_sp24 (cx : dcx) (T Sg : list byte) (ai ow ret : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 392) 8 (u64 (oldv ai (role_of_e T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 136) 8 (u64 (oldv ai (hd_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 128) 8 (u64 (oldv ai (din_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 120) 8 (u64 (oldv ai (dout_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 112) 8 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 104) 8 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 224) 8 (u64 (oldv ai (s32_at T (48 * ai + 20)))) /\
  val_mem SEGS (rd W m) (d_A cx + 96) 8 (u64 (oldv ai (owned_of T ai))) /\
  val_mem SEGS (rd W m) (d_A cx + 72) 8 (u64 (oldv ai (u_at T (48 * ai + 32) 8))) /\
  val_mem SEGS (rd W m) (d_A cx + 88) 8 (if ow =? 0 then owned_of T ai else 1) /\
  val_mem SEGS (rd W m) (d_A cx + 408) 8 ret /\
  val_mem SEGS (rd W m) (d_A cx + 64) 8
    (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg else reac_disco_table_observe_c.ch_of T ai)) /\
  val_mem SEGS (rd W m) (d_A cx + 56) 8 (bv_swrap 32 (s_ch Sg)).
Definition ob_r24 (cx : dcx) (T Sg : list byte) (ai ow : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 10 = w64 0 /\
  getr regs 19 = w64 (if s_role Sg =? 0 then role_of_e T ai
                      else if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg) /\
  getr regs 21 = w64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) /\
  getr regs 22 = w64 (d_obj cx OT + 48 * ai) /\
  getr regs 23 = w64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) /\
  getr regs 24 = w64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg) /\
  getr regs 26 = w64 (if s_hd Sg =? 0 then hd_of T ai else 1) /\
  getr regs 27 = w64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg).
Definition ob_c11 (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x1990 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ai ow ret,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\
    length T = 400%nat /\ table_ok T /\ find_res T (s_mac Sg) ai /\ 0 <= ai < n_of T /\ (ow = 0 \/ ow = 1) /\
    reac_disco_table_observe_c.observe_model T Sg ow now T' ret /\
    ob_sp24 cx T Sg ai ow ret W3 mem3 /\ ob_r24 cx T Sg ai ow regs).
Definition ob_seg9a : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) (W : world SEGS) (c : config),
  ob_c9 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c11 cx h i n now op nb fr len Sg kmax accmax).
Definition ob_seg9b : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  ob_c11 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).

Definition OBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma ob_A_range : forall cx ly3 S3 W3 mem3 md3 k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  alloc_ceiling + LLVMF_STK <= d_S cx <= 2 ^ 47 /\ d_S cx mod 16 = 0 /\
  d_S cx - 592 <= d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M.
unfold MFRAME in *. split; [lia|]. split; [exact Hal|]. split; [|rewrite Z.mul_comm; apply Z_mod_mult].
assert ((d_S cx - 576) mod 32 = 0 \/ (d_S cx - 576) mod 32 = 16).
{ assert (E16 : (d_S cx - 576) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  pose proof (Z.div_mod (d_S cx - 576) 16 ltac:(lia)). lia. }
lia.
Qed.

Lemma frame_of_ro_pt : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Lemma val_mem_pt : forall (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hpt H kk Hk. pose proof (H kk Hk) as H1. unfold mbyte in H1 |- *. rewrite Hpt. exact H1. Qed.
Lemma garr8_pt : forall (m m' : word -> option byte) a l, (forall x, m' x = m x) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof. intros m m' a l Hpt H j Hj. destruct (H j Hj) as [H1 H2]. split; [exact (val_mem_pt m m' _ _ _ Hpt H1) | exact H2]. Qed.
Lemma w64_add_w : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.


End h.
End f.
End d.
Ltac ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
