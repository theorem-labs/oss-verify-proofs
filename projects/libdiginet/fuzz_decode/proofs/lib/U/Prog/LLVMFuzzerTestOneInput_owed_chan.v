(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the family switch of the inlined spec_event_of (spec.h:395-396, :397, :412,
   :428) in LLVMFuzzerTestOneInput on the UBSan image, 0x12f5c-0x12f6c:
     0x12f5c-0x12f60  a0 = o.m.status, a1 = status & 0xf0;
     0x12f64          o.e.kind = SPEC_EV_OTHER (13), the event of spec.h:395;
     0x12f68          family == 0x90 -> 0x12ff4 (the note);
     0x12f6c          family != 0xb0 -> 0x1302c (the system exclusive, or OTHER); else 0x12f70 (the control
                      change).
   No UBSan check site is in this range. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout
  LLVMFuzzerTestOneInput_owed_lib.
Import ListNotations.
Open Scope Z_scope.

Lemma chan_evt :
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    seg_env Sp lo body bb -> msg_ok (Z.of_nat (length bb)) M ->
    (Z.land (sm_status M) 240 = 144 -> at_ev1 Q gp tp x23 F fc m0 Sp lo body bb M 0x12ff4) ->
    (Z.land (sm_status M) 240 = 176 -> at_ev1 Q gp tp x23 F fc m0 Sp lo body bb M 0x12f70) ->
    (Z.land (sm_status M) 240 <> 144 -> Z.land (sm_status M) 240 <> 176 ->
     at_ev1 Q gp tp x23 F fc m0 Sp lo body bb M 0x1302c) ->
    at_ev0 Q gp tp x23 F fc m0 Sp lo body bb M.
Proof.
  intros gp tp x23 F fc m0 Sp lo body bb M Q ENV MOK Knote Kcc Kelse.
  destruct ENV as (Hlo & HloSp & HSp16 & HSp47 & Hbody & Hbb).
  destruct MOK as (Hcode & Hsta & Hd1 & Hd2 & Hso & Hnx & Hmsg).
  pose proof (land_b (sm_status M) 240 ltac:(lia) ltac:(lia)) as Hfam.
  unfold at_ev0. intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m p1 p2 j56
    MU WM MI ST BA HM HEv HLm HP1 HN HS HP2 H150 H10.
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  step. rewrite (zxb_b8 (sm_status M)) by lia.
  step. usub.
  do 2 step.
  rewrite (beq_lit (Z.land (sm_status M) 240) 144) by lia.
  destruct (Z.eqb_spec (Z.land (sm_status M) 240) 144) as [E144|E144]; cbv iota.
  - unfold at_ev1 in Knote. apply (Knote E144) with (p1 := p1) (p2 := p2) (j56 := j56);
      try solve [ assumption | unfold spec_msg_cells; exact HM | exact HEv ].
  - step.
    rewrite (beq_lit (Z.land (sm_status M) 240) 176) by lia.
    destruct (Z.eqb_spec (Z.land (sm_status M) 240) 176) as [E176|E176]; cbn [negb]; cbv iota.
    + unfold at_ev1 in Kcc. apply (Kcc E176) with (p1 := p1) (p2 := p2) (j56 := j56);
        try solve [ assumption | unfold spec_msg_cells; exact HM | exact HEv ].
    + unfold at_ev1 in Kelse. apply (Kelse E144 E176) with (p1 := p1) (p2 := p2) (j56 := j56);
        try solve [ assumption | unfold spec_msg_cells; exact HM | exact HEv ].
Qed.
