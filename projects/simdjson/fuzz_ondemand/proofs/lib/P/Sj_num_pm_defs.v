(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition PM_ENTRY : Z := 0x3b630.
Definition PM_GTOP : Z := 0xab000.
Definition PM_POW10 : Z := 0x19fb0.

Record pmenv : Type := mkPmEnv {
  p_ra : word; p_sp : word; p_gp : word; p_tp : word;
  p_s0 : word; p_s1 : word; p_s2 : word; p_s3 : word; p_s4 : word; p_s5 : word;
  p_s6 : word; p_s7 : word; p_s8 : word; p_s9 : word; p_s10 : word; p_s11 : word;
  p_F : bvmap 5 word; p_fc : bv 32;
  p_X : Z; p_A : Z; p_IP : Z; p_IL : Z; p_FPT : Z; p_FL : Z; p_lo : Z; p_txt : list byte; p_m0 : mem }.

Notation p_SP E := (bv_unsigned (p_sp E)).
Notation p_TL E := (Z.of_nat (length (p_txt E))).

Record pm_ok (E : pmenv) : Prop := mkPmOk {
  po_room : (p_lo E + PM_STACK <= p_SP E)%Z;
  po_gtop : (PM_GTOP <= p_lo E)%Z;
  po_xhi : (p_SP E <= p_X E - 40)%Z;
  po_tlo : (p_A E + p_TL E <= p_lo E)%Z;
  po_tmax : (p_TL E < NUM_TXT_MAX)%Z;
  po_spans : pm_spans_ok (p_A E) (p_txt E) (p_IP E) (p_IL E) (p_FPT E) (p_FL E) }.

Definition pm_W (E : pmenv) : list (Z * Z) := [(p_SP E - PM_STACK, p_SP E); (p_X E, p_X E + 498); (p_X E + 504, p_X E + 512)]%Z.
Notation pm_post E := (pm_post_g psegs (p_ra E) (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                          (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E)
                          (p_X E) (p_IP E) (p_IL E) (p_FPT E) (p_FL E) (p_lo E) (p_m0 E)).

Definition pm_saved (E : pmenv) : list cell :=
  [C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E); C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E); C8 (p_s0 E)].
Definition pm_spans (E : pmenv) : list cell :=
  [C8 (Z_to_bv 64 (p_IP E)); C8 (Z_to_bv 64 (p_IL E)); C8 (Z_to_bv 64 (p_FPT E)); C8 (Z_to_bv 64 (p_FL E))].

Definition PMINV (E : pmenv) (mm : mem) (len dg : Z) : Prop :=
  (exists j, rw_cells psegs mm (p_SP E + -96) (CB 8 j :: pm_saved E)) /\
  (exists bs, u8arr psegs mm (p_X E) bs /\ length bs = 496%nat) /\
  rw_cells psegs mm (p_X E + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
  rw_cells psegs mm (p_X E + 504) [C8 (Z_to_bv 64 dg)] /\
  rw_cells psegs mm (p_X E + -40) (pm_spans E) /\
  bytes_at psegs mm (p_A E) (p_txt E) /\
  (exists tb, bytes_at psegs mm PM_POW10 tb /\ length tb = 160%nat) /\
  mem_inv psegs mm /\ munch (pm_W E) (p_m0 E) mm /\ wmono psegs (p_m0 E) mm /\ stk psegs mm (p_lo E) (p_SP E + -96).

Ltac pm_open H :=
  let j := fresh "j" in let bs := fresh "bs" in let tb := fresh "tb" in
  destruct H as ((j & FR) & (bs & XA & ?XL) & XN & ?LEN & DG & SPANS & TXT & (tb & TBL & ?TBLL) & MI & MU & WM & ST);
  unfold pm_saved in FR; unfold pm_spans in SPANS; unfold pm_W, PM_STACK in MU; unfold PM_POW10 in TBL;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac pm_close :=
  lazymatch goal with
  | |- PMINV _ _ _ _ =>
      split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [eexists; split; eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac pm_forget := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H end.

Notation PM E pc xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm :=
  (MS (mkR (p_ra E) (Z_to_bv 64 (p_SP E + -96)) (p_gp E) (p_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (p_s11 E) xt3 xt4 xt5 xt6) (p_F E) (Z_to_bv 64 pc) (p_fc E) None mm (seg_rom psegs)).

Notation PMX E pc xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm :=
  (PM E pc xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (p_X E)) xa1 xa2 (Z_to_bv 64 (p_X E + 504)) xa4 xa5 xa6 xa7
      xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).

Ltac pm_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let XHI := fresh "XHI" in let TLO := fresh "TLO" in
  let TMAX := fresh "TMAX" in let SPN := fresh "SPN" in
  destruct OK as [ROOM GTOP XHI TLO TMAX SPN];
  unfold PM_STACK, PM_GTOP, NUM_TXT_MAX, pm_spans_ok in *;
  destruct SPN as (SPN1 & SPN2 & SPN3 & SPN4);
  lazymatch goal with E : pmenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Section PMDEFS.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).

  Lemma pm_exit : forall xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg ->
    evt psegs (pm_post E) (PM E 0x3c2f0 xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV. pm_open INV. pm_env OK.
    do 11 zstep. zstep. zstep.
    release_frame FR ST (p_SP E).
    destruct (u64arr_of_u8arr psegs mm X bs XA XL) as (ws & WL & WA).
    apply evt_done. unfold pm_post_g. do 15 eexists. exists mm, ws, len, dg.
    split; [cbv delta [mkR]; reflexivity|].
    unfold PM_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] |].
    split; [exact DG|]. split; [exact SPANS| exact ST].
  Qed.
End PMDEFS.
