(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the note family of the inlined spec_event_of (spec.h:397-411) in
   LLVMFuzzerTestOneInput on the UBSan image, 0x12ff4-0x13028 and 0x13184-0x13198:
     0x12ff4-0x13008  id = m.d2 & 0x3f, on = m.d2 >> 6 & 1 (the `slli 57` / `srli 63` pair), id - 0x18;
     0x1300c-0x13010  e.button = m.d1, e.on = on;
     0x13018          id - 0x18 >=u 6 -> 0x13184 (not a zone);
     0x1301c-0x13028  e.kind = SPEC_EV_SECTION_BUTTON (4), e.zone = id;
     0x13184-0x13198  e.kind = (m.d1 == 9 ? SPEC_EV_TOUCH (2) : SPEC_EV_STRIP_BUTTON (3)) by
                      `seqz` / `xori 3`, e.strip = id.
   Both paths reach 0x131cc. No UBSan check site is in this range. *)
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

Lemma note_evt :
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    seg_env Sp lo body bb -> msg_ok (Z.of_nat (length bb)) M ->
    Z.land (sm_status M) 240 = 144 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (owed_tail (map bz bb) (Z.of_nat (length bb)) M) ->
    at_ev1 Q gp tp x23 F fc m0 Sp lo body bb M 0x12ff4.
Proof.
  intros gp tp x23 F fc m0 Sp lo body bb M Q ENV MOK Hfam K.
  destruct ENV as (Hlo & HloSp & HSp16 & HSp47 & Hbody & Hbb).
  destruct MOK as (Hcode & Hsta & Hd1 & Hd2 & Hso & Hnx & Hmsg).
  pose proof (land_b (sm_d2 M) 63 ltac:(lia) ltac:(lia)) as Htid.
  pose proof (shiftr_b (sm_d2 M) 6 ltac:(lia) ltac:(lia)) as Hsr.
  pose proof (land_b (Z.shiftr (sm_d2 M) 6) 1 ltac:(lia) ltac:(lia)) as Honb.
  rewrite (owed_tail_note (map bz bb) (Z.of_nat (length bb)) M Hfam) in K.
  rewrite (seo_note (map bz bb) M Hfam) in K.
  unfold owed_k in K.
  unfold at_ev1. intros y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m p1 p2 j56
    MU WM MI ST BA HM HEv HLm HP1 HN HS HP2 H150 H10.
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x12ff4-0x13008 *)
  do 2 step.
  rewrite (zxb_b8 (sm_d2 M)) by lia.
  step. usub.
  do 2 step. usub.
  rewrite (shl_shr_bit (sm_d2 M) 57 6 ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  (* 0x1300c-0x13010: e.button, e.on *)
  step. rewrite le1_zxb. mem_after_store.
  rewrite (zxb_b8 (sm_d1 M)) by lia.
  step. rewrite le1_lit. mem_after_store.
  (* 0x13014-0x13018: the zone test *)
  do 2 step.
  rewrite (addw_ltu (Z.land (sm_d2 M) 63) (-24) 6 ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (Ezone : (0 <=? Z.land (sm_d2 M) 63 + -24) && (Z.land (sm_d2 M) 63 + -24 <? 6)
                = (24 <=? Z.land (sm_d2 M) 63) && (Z.land (sm_d2 M) 63 <=? 29)).
  { destruct (Z.leb_spec 0 (Z.land (sm_d2 M) 63 + -24));
      destruct (Z.ltb_spec (Z.land (sm_d2 M) 63 + -24) 6);
      destruct (Z.leb_spec 24 (Z.land (sm_d2 M) 63));
      destruct (Z.leb_spec (Z.land (sm_d2 M) 63) 29);
      cbn [andb]; first [reflexivity | exfalso; lia]. }
  rewrite Ezone.
  destruct ((24 <=? Z.land (sm_d2 M) 63) && (Z.land (sm_d2 M) 63 <=? 29)) eqn:Ez;
    cbn [negb]; cbv iota.
  - (* 0x1301c-0x13028: a section button *)
    do 2 step.
    step. rewrite le1_lit. mem_after_store.
    step.
    apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
    apply (owed_join _ _ _ _ _ _ _ p1 p2);
      try solve [ assumption | unfold spec_msg_cells; exact HM ].
    all: try (rewrite ev_cells_unfold; exact HEv).
  - (* 0x13184-0x13198: a strip button or the touch *)
    do 2 step.
    rewrite (sltiu1_addw (sm_d1 M) (-9) ltac:(lia) ltac:(lia)).
    destruct (Z.eqb_spec (sm_d1 M + -9) 0) as [E9|E9]; cbv iota.
    + replace (sm_d1 M =? 9) with true in K by (symmetry; apply Z.eqb_eq; lia).
      step. usub.
      step.
      step. rewrite le1_lit. mem_after_store.
      step.
      apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
      apply (owed_join _ _ _ _ _ _ _ p1 p2);
        try solve [ assumption | unfold spec_msg_cells; exact HM ].
      all: try (rewrite ev_cells_unfold; exact HEv).
    + replace (sm_d1 M =? 9) with false in K by (symmetry; apply Z.eqb_neq; lia).
      step. usub.
      step.
      step. rewrite le1_lit. mem_after_store.
      step.
      apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
      apply (owed_join _ _ _ _ _ _ _ p1 p2);
        try solve [ assumption | unfold spec_msg_cells; exact HM ].
      all: try (rewrite ev_cells_unfold; exact HEv).
Qed.
