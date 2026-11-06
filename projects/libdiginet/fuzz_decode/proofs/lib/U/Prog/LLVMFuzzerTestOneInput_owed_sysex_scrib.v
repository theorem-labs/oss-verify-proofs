(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the case SPEC_FN_SCRIBBLE (0x40) of the system exclusive part of the inlined
   spec_event_of (spec.h:474-482) in LLVMFuzzerTestOneInput on the UBSan image, 0x13344-0x13380 (the entry 4 of the
   jump table at 0x103a4; a0 = pl, a1 = s, a2 = sysex_len, a3 = pn):
     0x13344-0x13348  pn < 3 -> 0x131cc (the event stays OTHER with the device);
     0x1334c-0x13354  len = sysex_len - 5 = pn - 2, len > SPEC_CHARS_MAX (8) -> 0x131cc;
     0x13358-0x13368  e.kind = SPEC_EV_SCRIBBLE (10), e.len = len, e.addr = pl[0];
     0x1336c-0x13370  UBSan: pl + 2 does not wrap (bltu -3, pl -> 0x13460);
     0x13374-0x1337c  memcpy (e.text, pl + 2, len) (sp + 0x65, s + 5); the other bytes of e.text stay 0 from the
                      memset of the event;
     0x13380          to 0x131cc.
   The proof takes the 8 lengths 1 .. 8 one by one, so that the cut of the event's cells around the memcpy's
   destination is concrete. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout memcpy_c
  LLVMFuzzerTestOneInput_owed_lib LLVMFuzzerTestOneInput_owed_sysex_lib.
Import ListNotations.
Open Scope Z_scope.

(* the L body bytes from index j, the memcpy's source *)
Definition sx_pick (bb : list byte) (j : Z) (L : nat) : list byte :=
  map (fun k => b8 (byte_at (map bz bb) (j + Z.of_nat k))) (seq 0 L).

Lemma b8_bz : forall x : byte, b8 (bz x) = x.
Proof.
  intros x. unfold b8, bz. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma bytes_at_pick : forall m body bb j L, bytes_at rsegs m body bb -> 0 <= j ->
  j + Z.of_nat L <= Z.of_nat (length bb) -> bytes_at rsegs m (body + j) (sx_pick bb j L).
Proof.
  intros m body bb j L (H0 & H1 & H2) Hj HL. unfold bytes_at, sx_pick. rewrite length_map, length_seq.
  split; [lia|]. split; [lia|]. intros i Hi.
  assert (S : nth_error (seq 0 L) i = Some i).
  { rewrite (nth_error_nth' (seq 0 L) 0%nat) by (rewrite length_seq; lia). rewrite seq_nth by lia. reflexivity. }
  erewrite map_nth_error by exact S.
  replace (body + j + Z.of_nat i) with (body + Z.of_nat (Z.to_nat (j + Z.of_nat i))) by lia.
  rewrite H2 by lia. rewrite (nth_error_nth' bb (b8 0)) by lia. f_equal.
  unfold byte_at.
  replace (nth (Z.to_nat (j + Z.of_nat i)) (map bz bb) 0) with (bz (nth (Z.to_nat (j + Z.of_nat i)) bb (b8 0)))
    by (rewrite <- (map_nth bz bb (b8 0) (Z.to_nat (j + Z.of_nat i))); reflexivity).
  symmetry. apply b8_bz.
Qed.

(* cut the cell list of H after its k-th cell: Ha the first k cells, Hb the rest at A + their size *)
Ltac cells_cut H k Ha Hb :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let c1 := eval cbv [firstn] in (firstn k cs) in
    let c2 := eval cbv [skipn] in (skipn k cs) in
    change (rw_cells segs m A (c1 ++ c2)) in H;
    destruct (proj1 (rw_cells_app segs m A c1 c2) H) as [Ha Hb]; clear H;
    let z := eval vm_compute in (Z.of_nat (cells_size c1)) in
    change (Z.of_nat (cells_size c1)) with z in Hb
  end.

(* the cells of H as one block of their bytes *)
Ltac cells_to_cb H :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let bs := eval cbv [cells_bytes cbytes app] in (cells_bytes cs) in
    let k := eval vm_compute in (cells_size cs) in
    apply (rwc_bytes segs m A cs [CB k bs]) in H; [ | split; [reflexivity | exact I] | reflexivity ]
  end.

(* one length L = sysex_len - 5 of the text, from 0x13358 to 0x131cc *)
Ltac scrib_len MCPY K M Sp body bb L :=
  (* 0x13358-0x13368: kind, e.len, e.addr *)
  do 2 step;
  rd_step (sm_sysex_at M + 3);
  step; rewrite le1_lit; mem_after_store;
  step; rewrite le1_zxb; mem_after_store;
  (* 0x1336c-0x13370: UBSan pl + 2 does not wrap *)
  step; step; take false;
  (* 0x13374-0x1337c: memcpy (sp + 0x65, s + 5, L) *)
  do 3 step;
  lazymatch goal with HE : rw_cells rsegs _ (Sp + 0x50) _ |- _ =>
    let Hh := fresh "Hh" in let Hr := fresh "Hr" in let Ht := fresh "Ht" in let Hu := fresh "Hu" in
    cells_cut HE 15%nat Hh Hr;
    replace (Sp + 0x50 + 21) with (Sp + 0x65) in Hr by lia;
    cells_cut Hr L Ht Hu;
    cells_to_cb Ht;
    call (mcpy_call MCPY (sx_pick bb (sm_sysex_at M + 5) L));
    [ lia | lia | lia | reflexivity
    | replace (body + sm_sysex_at M + 5) with (body + (sm_sysex_at M + 5)) by lia;
      apply bytes_at_pick; [assumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
    | exact Ht | left; lia | assumption | ];
    (* 0x13380 *)
    step;
    lazymatch goal with HM : rw_cells rsegs _ (Sp + 0x65) [CB _ _] |- _ =>
      let J1 := fresh "J1" in let J2 := fresh "J2" in
      pose proof (rw_join _ _ _ _ _ HM Hu ltac:(cbn [cells_size csize Nat.add]; lia)) as J1;
      pose proof (rw_join _ _ _ _ _ Hh J1 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
        as J2;
      clear Hh HM Hu J1;
      eapply sx_close; [ eapply sx_mem_intro | exact K ];
      first [ eassumption | unfold spec_msg_cells; assumption
            | apply (rwc_bytes _ _ _ _ _ J2);
              [ rewrite ev_cells_unfold; cbn [cells_wf cell_wf length]; repeat split | reflexivity ] ]
    end
  end.

Lemma sx_scrib_evt : memcpy_contract ->
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    sx_env Sp lo body bb M -> byte_at (map bz bb) (sm_sysex_at M + 2) = 64 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (Owed M (spec_event_of (map bz bb) M) 0 (sm_next M) (sm_status_out M)) ->
    at_sx Q gp tp x23 F fc m0 Sp lo body bb M 0x13344.
Proof.
  intros MCPY gp tp x23 F fc m0 Sp lo body bb M Q SXE Hfn K.
  sx_env_facts SXE.
  rewrite (seo_scribble _ M E240 Hn3 Hmk Hfn) in K.
  replace (sm_sysex_at M + 3 + 2) with (sm_sysex_at M + 5) in K by lia.
  unfold at_sx. intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 m p1 p2 j56
    -> -> -> -> SXM.
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HP1 & HN & HS & HP2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x13344-0x13348: pn < 3 -> 0x131cc *)
  do 2 step.
  rewrite (bltu_lit (sm_sysex_len M - 3) 3) by lia.
  destruct (Z.ltb_spec (sm_sysex_len M - 3) 3) as [L3|L3]; cbv iota.
  { try rewrite (proj2 (Z.ltb_lt _ _) L3) in K. cbn [orb] in K. sx_fin K. }
  try rewrite (proj2 (Z.ltb_ge _ _) L3) in K. cbn [orb] in K.
  (* 0x1334c-0x13354: len = sysex_len - 5 > 8 -> 0x131cc *)
  do 3 step.
  rewrite (bltu_lit 8 (sm_sysex_len M + -5)) by lia.
  destruct (Z.ltb_spec 8 (sm_sysex_len M + -5)) as [L8|L8]; cbv iota.
  { replace (8 <? sm_sysex_len M - 3 - 2) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in K.
    sx_fin K. }
  replace (8 <? sm_sysex_len M - 3 - 2) with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in K.
  assert (Hn : sm_sysex_len M = 6 \/ sm_sysex_len M = 7 \/ sm_sysex_len M = 8 \/ sm_sysex_len M = 9 \/
               sm_sysex_len M = 10 \/ sm_sysex_len M = 11 \/ sm_sysex_len M = 12 \/ sm_sysex_len M = 13) by lia.
  destruct Hn as [Hn|[Hn|[Hn|[Hn|[Hn|[Hn|[Hn|Hn]]]]]]]; rewrite Hn in K; rewrite Hn.
  - scrib_len MCPY K M Sp body bb 1%nat.
  - scrib_len MCPY K M Sp body bb 2%nat.
  - scrib_len MCPY K M Sp body bb 3%nat.
  - scrib_len MCPY K M Sp body bb 4%nat.
  - scrib_len MCPY K M Sp body bb 5%nat.
  - scrib_len MCPY K M Sp body bb 6%nat.
  - scrib_len MCPY K M Sp body bb 7%nat.
  - scrib_len MCPY K M Sp body bb 8%nat.
Qed.
