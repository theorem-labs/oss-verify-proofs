(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the case SPEC_FN_LEDS (0x20) of the system exclusive part of the inlined
   spec_event_of (spec.h:465-473) in LLVMFuzzerTestOneInput on the UBSan image, 0x13230-0x13258 (the entry 2 of the
   jump table at 0x103a4; a0 = pl, a1 = s, a3 = pn):
     0x13230-0x13234  pn != 2 -> 0x131cc (the event stays OTHER with the device);
     0x13238-0x1323c  e.kind = SPEC_EV_STRIP_LEDS (9);
     0x13240-0x13248  e.strip = e.addr = pl[0];
     0x1324c          UBSan: pl + 1 does not wrap (beq pl, -1 -> 0x13460);
     0x13250-0x13258  e.mask = pl[1] (lbu of s[4]), then 0x131cc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout
  LLVMFuzzerTestOneInput_owed_lib LLVMFuzzerTestOneInput_owed_sysex_lib.
Import ListNotations.
Open Scope Z_scope.

Lemma sx_leds_evt :
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    sx_env Sp lo body bb M -> byte_at (map bz bb) (sm_sysex_at M + 2) = 32 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (Owed M (spec_event_of (map bz bb) M) 0 (sm_next M) (sm_status_out M)) ->
    at_sx Q gp tp x23 F fc m0 Sp lo body bb M 0x13230.
Proof.
  intros gp tp x23 F fc m0 Sp lo body bb M Q SXE Hfn K.
  sx_env_facts SXE.
  rewrite (seo_leds _ M E240 Hn3 Hmk Hfn) in K.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) in K by lia.
  unfold at_sx. intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 m p1 p2 j56
    -> -> -> -> SXM.
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HP1 & HN & HS & HP2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x13230-0x13234: pn != 2 -> 0x131cc *)
  do 2 step.
  rewrite (beq_lit (sm_sysex_len M - 3) 2) by lia.
  destruct (Z.eqb_spec (sm_sysex_len M - 3) 2) as [P2|P2]; cbn [negb]; cbv iota.
  2: { try rewrite (proj2 (Z.eqb_neq _ _) P2) in K. cbn [negb] in K. sx_fin K. }
  try rewrite (proj2 (Z.eqb_eq _ _) P2) in K. cbn [negb] in K.
  (* 0x13238-0x13248: kind, strip, addr *)
  do 2 step.
  rd_step (sm_sysex_at M + 3).
  step. rewrite le1_zxb. mem_after_store.
  step. rewrite le1_zxb. mem_after_store.
  (* 0x1324c: UBSan pl + 1 does not wrap *)
  step. take false.
  (* 0x13250-0x13258: the mask *)
  rd_step (sm_sysex_at M + 4).
  rewrite (zxb_b8 _ (bat_range bb (sm_sysex_at M + 4))).
  do 2 step.
  sx_fin K.
Qed.
