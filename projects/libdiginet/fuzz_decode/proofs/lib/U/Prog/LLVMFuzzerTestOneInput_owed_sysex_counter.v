(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the case SPEC_FN_COUNTER (0x30) of the system exclusive part of the inlined
   spec_event_of (spec.h:483-492) in LLVMFuzzerTestOneInput on the UBSan image, 0x132f0-0x13340 (the entry 3 of the
   jump table at 0x103a4; a0 = pl, a1 = s, a3 = pn):
     0x132f0-0x132f4  pn != 2 + SPEC_DIGITS (10) -> 0x131cc (the event stays OTHER with the device);
     0x132f8-0x13304  e.kind = SPEC_EV_COUNTER (11), e.addr = pl[0];
     0x13308          UBSan: pl + 1 does not wrap (beq pl, -1 -> 0x13460);
     0x1330c-0x13310  e.dots = pl[1] (lbu of s[4]);
     0x13314-0x1333c  the digit loop, unrolled here: for k = 0 .. 7, seg[k] = s[12 - k] (a2 = 12 - k, a3 =
                      sp + 0x6d + k), each turn with the UBSan check of pl + 10 (0x13320: bltu -10, pl);
     0x13340          to 0x131cc. *)
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

(* spec.h:491: seg[k] = pl[2 + 8 - 1 - k] = s[12 - k] *)
Lemma counter_seg : forall b s,
  map (fun k => byte_at b (s + 3 + 2 + 8 - 1 - k)) (zseq 8) =
  [byte_at b (s + 12); byte_at b (s + 11); byte_at b (s + 10); byte_at b (s + 9); byte_at b (s + 8);
   byte_at b (s + 7); byte_at b (s + 6); byte_at b (s + 5)].
Proof.
  intros b s. unfold zseq. cbn [seq map Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat f_equal; lia.
Qed.

(* one turn of the digit loop 0x1331c-0x13338, reading s[c] *)
Ltac cnt_turn M c :=
  step; step; take false;
  step; rd_step (sm_sysex_at M + c);
  step; step; rewrite le1_zxb; mem_after_store;
  do 3 step.

Lemma sx_counter_evt :
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    sx_env Sp lo body bb M -> byte_at (map bz bb) (sm_sysex_at M + 2) = 48 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (Owed M (spec_event_of (map bz bb) M) 0 (sm_next M) (sm_status_out M)) ->
    at_sx Q gp tp x23 F fc m0 Sp lo body bb M 0x132f0.
Proof.
  intros gp tp x23 F fc m0 Sp lo body bb M Q SXE Hfn K.
  sx_env_facts SXE.
  rewrite (seo_counter _ M E240 Hn3 Hmk Hfn) in K.
  rewrite counter_seg in K.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) in K by lia.
  unfold at_sx. intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 m p1 p2 j56
    -> -> -> -> SXM.
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HP1 & HN & HS & HP2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x132f0-0x132f4: pn != 10 -> 0x131cc *)
  do 2 step.
  rewrite (beq_lit (sm_sysex_len M - 3) 10) by lia.
  destruct (Z.eqb_spec (sm_sysex_len M - 3) 10) as [P10|P10]; cbn [negb]; cbv iota.
  2: { try rewrite (proj2 (Z.eqb_neq _ _) P10) in K. cbn [negb] in K. sx_fin K. }
  try rewrite (proj2 (Z.eqb_eq _ _) P10) in K. cbn [negb] in K.
  (* 0x132f8-0x13304: kind, addr *)
  do 2 step.
  rd_step (sm_sysex_at M + 3).
  step. rewrite le1_zxb. mem_after_store.
  (* 0x13308: UBSan pl + 1 does not wrap *)
  step. take false.
  (* 0x1330c-0x13310: dots *)
  rd_step (sm_sysex_at M + 4).
  step. rewrite le1_zxb. mem_after_store.
  (* 0x13314-0x1333c: the digits *)
  do 2 step.
  cnt_turn M 12. take true. cnt_turn M 11. take true. cnt_turn M 10. take true. cnt_turn M 9. take true.
  cnt_turn M 8. take true. cnt_turn M 7. take true. cnt_turn M 6. take true. cnt_turn M 5. take false.
  (* 0x13340 *)
  step.
  sx_fin K.
Qed.
