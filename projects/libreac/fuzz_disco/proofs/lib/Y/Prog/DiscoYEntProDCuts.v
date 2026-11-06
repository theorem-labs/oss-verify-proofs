(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 437 of its 472 lines of code are new or changed and 1243 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProE.v, with its module paths and module names changed; 53 of its 92 lines of code are new or changed and 433 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0e YP02 YP0k YP06 YP03 YP04 YP01 YP00 YP0i YA0o YCbm YA0q YE00 YC5d YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntSeatStmt DiscoYEntProCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition POFF_D1 : Z := 0x720.
Definition POFF_D2 : Z := 0x734.
Definition PD_NOW : Z := 1000000000.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition pd_our (cx : dcx) (W : world SEGS) (m : word -> option byte) : Prop :=
  garr8 SEGS (rd W m) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx))).
Definition pd_objT (cx : dcx) (W : world SEGS) (m : word -> option byte) : Prop :=
  exists T : list byte, length T = 400%nat /\
    garr8 SEGS (rd W m) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) /\ disco_table_c.table_ok T.
Definition pd_objG (cx : dcx) (W : world SEGS) (m : word -> option byte) : Prop :=
  exists G : list byte, length G = 264%nat /\
    garr8 SEGS (rd W m) (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G) /\ disco_classify_c.gate_ok G.
Definition pd_objL (cx : dcx) (W : world SEGS) (m : word -> option byte) : Prop :=
  exists Lk : list byte, length Lk = 12%nat /\
    garr8 SEGS (rd W m) (d_obj cx OLOCK) (map (fun b : byte => bv_unsigned b) Lk) /\ disco_classify_c.lock_ok Lk.
Definition pd_objH (cx : dcx) (h : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  exists H : list byte, length H = 480%nat /\
    garr8 SEGS (rd W m) h (map (fun b : byte => bv_unsigned b) H) /\ hunt_c.hunt_ok H /\
    firstn 6 (skipn 412 H) = our_of (c_pl cx).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Definition pd_at (cx : dcx) (h pc : Z) (R : bvmap 5 word -> Prop)
  (M : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx pc EV_PRO (ACC_PRO MT) (fun regs ly3 S3 W3 mem3 md3 =>
    p_canok cx /\
    p_rC3 cx B regs /\ R regs /\ p_frame cx dsh_loop ps_C3 W3 mem3 /\ d_blocks B cx h [] ly3 S3 /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 184) 8 h /\ M W3 mem3).
Definition pd_K1 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h POFF_D1 (fun regs => True)
    (fun W m => pd_our cx W m /\ pd_objT cx W m /\ pd_objG cx W m /\ pd_objL cx W m).
Definition pd_K2 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h POFF_D2 (fun regs => True)
    (fun W m => pd_our cx W m /\ pd_objT cx W m /\ pd_objG cx W m /\ pd_objL cx W m /\ pd_objH cx h W m).
Definition pd_seg1 : Prop :=
  forall (cx : dcx) (h : Z) (W : world SEGS) (c : config),
  pro_C4 B MT XM_LIB RLO RHI tfib_K cx h W c -> SRr SEGS W c (pd_K1 cx h).
Definition pd_seg2 : Prop :=
  forall (cx : dcx) (h : Z) (W : world SEGS) (c : config),
  pd_K1 cx h W c -> SRr SEGS W c (pd_K2 cx h).
Definition pd_seg3 : Prop :=
  forall (cx : dcx) (h : Z) (W : world SEGS) (c : config),
  pd_K2 cx h W c -> SRr SEGS W c (pro_C5 B MT XM_LIB RLO RHI tfib_K cx h).
Theorem pd_of_segs : pd_seg1 -> pd_seg2 -> pd_seg3 -> pro_segD B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros S1 S2 S3. unfold pro_segD. intros cx h W c H1.
  eapply SRr_bind; [exact (S1 cx h W c H1)|].
  cbv beta. intros W1 c1 _ H2.
  eapply SRr_bind; [exact (S2 cx h W1 c1 H2)|].
  cbv beta. intros W2 c2 _ H3.
  exact (S3 cx h W2 c2 H3).
Qed.
End h.
End f.
End d.
