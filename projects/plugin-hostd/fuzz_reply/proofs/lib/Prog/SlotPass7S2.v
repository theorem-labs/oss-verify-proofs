From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadQ RelayRunT RelayRunF HarnessGlue
  relay_event_b_c check_shape_event_c strnlen_c memcpy_c SlotPass7D SlotPass7RV SlotPass7R SlotPass7S SlotPass7T1
  SlotPass7T2 SlotPass7.
Import ListNotations.
Local Open Scope Z_scope.

Definition op7_s2_post (Q S0 M R EL : Z) (e : list byte) (x2 x3 x4 x20 x21 x22 x24 x25 x26 x27 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ms : machine_state) : Prop :=
  exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0,
    ms = MS (mkR (Z_to_bv 64 0x140b8) x2 x3 x4 t0 t1 t2 (Z_to_bv 64 S0) (Z_to_bv 64 Q) (Z_to_bv 64 Q) a1 a2 a3 a4 a5
      a6 a7 (Z_to_bv 64 (S0 + M)) (Z_to_bv 64 (Q + EL)) x20 x21 x22 (Z_to_bv 64 (R - M)) x24 x25 x26 x27 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1316c) fc None m0 (seg_rom rsegs) /\
    munch [(Q, Q + EL + 1)] m m0 /\ wmono rsegs m m0 /\
    rw_cells rsegs m0 Q [CB (Z.to_nat EL) e; C1 (Z_to_bv 8 0)].

Lemma op7_s2_run : memcpy_contract ->
  forall (Q S0 M R EL : Z) (e junk : list byte) (j1 : byte)
    (x2 x3 x4 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x1 x9 x11 x12 : word),
  0 < Q -> 0 <= M <= R -> R < 2 ^ 64 -> 0 <= EL -> 0 <= S0 < 2 ^ 64 ->
  bytes_at rsegs m S0 e -> Z.of_nat (length e) = EL ->
  rw_cells rsegs m Q [CB (Z.to_nat EL) junk; CB 1 [j1]] ->
  (S0 + EL <= Q \/ Q + EL <= S0) ->
  mem_inv rsegs m ->
  evt rsegs (op7_s2_post Q S0 M R EL e x2 x3 x4 x20 x21 x22 x24 x25 x26 x27 F fc m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S0) x9 (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 M)
      (Z_to_bv 64 EL) x20 x21 x22 (Z_to_bv 64 R) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1408c) fc None m
      (seg_rom rsegs)).
Proof.
  intros MC Q S0 M R EL e junk j1 x2 x3 x4 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m x1 x9 x11 x12 HQ HM HR HEL HS0 BE LE DST DJ MI.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize] in DB.
  pose proof BE as (BE0 & BE1 & _).
  destruct (hg_cut rsegs m Q [CB (Z.to_nat EL) junk] [CB 1 [j1]] DST) as (D1 & D2).
  replace (Q + Z.of_nat (cells_size [CB (Z.to_nat EL) junk])) with (Q + EL) in D2 by (cbn [cells_size csize]; lia).
  eapply evt_cut; [apply (op7_cpy Q S0 M R EL); lia|].
  intros ms1 (s2 & s7 & -> & -> & ->).
  assert (UQ : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply hg_unsigned; lia).
  assert (US : bv_unsigned (Z_to_bv 64 S0) = S0) by (apply hg_unsigned; lia).
  assert (UE : bv_unsigned (Z_to_bv 64 EL) = EL) by (apply hg_unsigned; lia).
  eapply evt_cut.
  { eapply (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e junk).
    - rewrite US. exact BE.
    - rewrite UE. lia.
    - rewrite UQ, UE. exact D1.
    - rewrite UQ, US, UE. lia.
    - exact MI. }
  intros ms2 (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & _ & RW & _).
  rewrite UQ, UE in MU, RW.
  rewrite (ret_pc_even 0x140a8) by lia.
  assert (D2' : rw_cells rsegs m' (Q + EL) [CB 1 [j1]]).
  { apply (rw_cells_transport rsegs [(Q, Q + EL)] m m' (Q + EL) [CB 1 [j1]] D2 MU WM).
    cbn [disjoint_from cells_size csize]. split; [lia|exact I]. }
  assert (ST : store_ok rsegs m' (Z_to_bv 64 (Q + EL)) 1 = true).
  { eapply (rw_cells_store_ok_at rsegs m' (Q + EL) [CB 1 [j1]] 0 (CB 1 [j1]) 1);
      [exact D2'|reflexivity|reflexivity|unfold wa; f_equal; lia]. }
  eapply evt_cut; [apply (op7_ev Q EL); exact ST|].
  intros ms3 (s3 & -> & ->).
  apply evt_done. unfold op7_s2_post.
  do 15 eexists. split; [reflexivity|].
  assert (L1 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0]) by reflexivity.
  split.
  { change (Z_to_bv 64 (Q + EL)) with (wa (Q + EL)). apply munch_write.
    - eapply munch_weaken; [|exact MU]. intros x (Hx & _). split; [lia|exact I].
    - lia.
    - rewrite length_le1. lia.
    - cbn [inside]. left. rewrite length_le1. lia. }
  split; [apply wmono_write; exact WM|].
  apply (hg_join rsegs _ Q (Q + EL) [CB (Z.to_nat EL) e] [C1 (Z_to_bv 8 0)]).
  - change (Z_to_bv 64 (Q + EL)) with (wa (Q + EL)).
    apply rw_cells_frame; [exact RW|lia|rewrite length_le1; lia|cbn [cells_size csize]; lia].
  - pose proof (rw_cells_write rsegs m' (Q + EL) [CB 1 [j1]] 0 (CB 1 [j1]) (C1 (Z_to_bv 8 0)) D2' eq_refl eq_refl I)
      as W1.
    cbn [cell_upd Nat.eqb cbytes] in W1. replace (Q + EL + Z.of_nat 0) with (Q + EL) in W1 by lia.
    rewrite L1. exact W1.
  - cbn [cells_size csize]. lia.
Qed.

Lemma op7_src_sep : forall p n K0 EL res (L : layout) (A : astate),
  (forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) ->
  In (p, n) (blocks L A) -> 0 <= K0 -> K0 + EL <= n ->
  p + K0 + EL <= res \/ res + EL <= p + K0.
Proof.
  intros p n K0 EL res L A RS IN H0 H1.
  destruct (RS p n IN) as (_ & D).
  destruct (Z.le_gt_cases EL 0) as [E0|E0]; [lia|].
  destruct (Z.le_gt_cases (p + K0 + EL) res) as [X|X]; [left; exact X|].
  destruct (Z.le_gt_cases (res + EL) (p + K0)) as [Y|Y]; [right; exact Y|].
  exfalso.
  destruct (Z.le_gt_cases res (p + K0)) as [Z1|Z1].
  - apply (D K0); lia.
  - apply (D (res - p)); lia.
Qed.
