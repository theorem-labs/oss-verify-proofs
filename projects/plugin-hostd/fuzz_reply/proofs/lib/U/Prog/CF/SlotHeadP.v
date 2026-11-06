(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass9G.v; 93 of its 141 lines of code are new or changed and 623 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotHead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Ltac geq X := etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; reflexivity.

Lemma swrap_inc : forall T, 0 <= T < 2 ^ 31 - 1 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 T) + 1)) = Z_to_bv 64 (T + 1).
Proof.
  intros T HT. f_equal. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma pair_ok_t : forall rc B L A mem t t' e p,
  pair_ok (rc := rc) B L A mem t e p -> 0 <= t <= t' -> pair_ok (rc := rc) B L A mem t' e p.
Proof.
  intros rc B L A mem t t' e p H Ht. unfold pair_ok in *. cbv zeta in *.
  destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
  unfold WRITE_MAX in *.
  repeat (split; [assumption|]). split; [lia|]. split; [lia|]. split; [nia|]. split; assumption.
Qed.

Lemma relay_at_t : forall rc B L A mem t t' nfd G OUT es hj,
  relay_at (rc := rc) B L A mem t nfd G OUT es hj -> 0 <= t <= t' ->
  relay_at (rc := rc) B L A mem t' nfd G OUT es hj.
Proof.
  intros rc B L A mem t t' nfd G OUT es hj H Ht. unfold relay_at in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [|split; [exact H8|split; [exact H9|exact H10]]].
  eapply Forall2_impl; [|exact H7]. intros e p Hp. exact (pair_ok_t rc B L A mem t t' e p Hp Ht).
Qed.

Section Tail48.

Lemma tl48_run : forall (T N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 <= T < 512 -> 0 <= K <= N -> N < 2 ^ 26 ->
  evt rsegs (fun ms => exists x10' x22' : word,
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (N - K)) x10' x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                  x22' x23 x24 x25 x26 x27 x28 x29 x30 x31) F
              (Z_to_bv 64 (if (T + 1 <? 512) && (K <? N) then 0x14144 else 0x14658)) fc None m ro /\
      ((T + 1 <? 512) && (K <? N) = true -> x22' = Z_to_bv 64 (T + 1)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (N - K)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             (Z_to_bv 64 T) x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x142bc) fc None m ro).
Proof.
  intros T N K x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m ro HT HK HN.
  step. step. if_cases HB.
  - assert (T = 511) as ->.
    { unfold bv_ltu in HB. rewrite !unsigned_lit in HB by lia. apply Z.ltb_lt in HB. lia. }
    apply evt_done. do 2 eexists. split; [reflexivity|]. cbn. intros C. discriminate C.
  - assert (HT' : T <= 510).
    { unfold bv_ltu in HB. rewrite !unsigned_lit in HB by lia. apply Z.ltb_ge in HB. lia. }
    step. step. if_cases HC.
    + assert (HKN : K < N).
      { apply Bool.negb_true_iff in HC. unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia.
        apply Z.eqb_neq in HC. lia. }
      assert (C : (T + 1 <? 512) && (K <? N) = true).
      { apply andb_true_iff. split; apply Z.ltb_lt; lia. }
      rewrite C. apply evt_done. do 2 eexists. split; [reflexivity|]. intros _. apply swrap_inc. lia.
    + assert (HKN : K = N).
      { apply Bool.negb_false_iff in HC. unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia.
        apply Z.eqb_eq in HC. lia. }
      assert (C : (T + 1 <? 512) && (K <? N) = false).
      { apply andb_false_iff. right. apply Z.ltb_ge. lia. }
      step. rewrite C. apply evt_done. do 2 eexists. split; [reflexivity|]. intros D. discriminate D.
Qed.

Lemma MI_tail48 : forall B API LS SH SK ra empty rc fx j E CS RI t k RG c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  (forall es hj no regs, RG es hj no regs -> tail48_regs E t k regs) -> walk_at (ss_pl E) (t + 1) k ->
  MI (rc := rc) B (API rc) E RI t k TAIL_STEP RG c ->
  SR (ms_segs B) c (LI (rc := rc) B (API rc) E RI (t + 1) k).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t k RG c HF HRG HW HM.
  destruct HF as (FF & _ & _). pose proof (proj1 FF) as SEGS.
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  destruct (HRG _ _ _ _ HR) as ((B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R9 & R18 & R22).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 (ss_n E - k)) by exact R9.
  assert (E18 : reg_get regs 18 = Z_to_bv 64 (ss_p E + k)) by exact R18.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 4) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEGS.
  eapply (evt_SR_canon rsegs); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E9, E18, E19, E20, E21, E22, E23, E24, E25, E27.
    apply tl48_run; unfold OPS_MAX, INPUT_MAX in *; lia. }
  intros ms1 (can1 & (x10' & x22' & -> & HX) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  apply SR_ret.
  exists fx', L, A, R1, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj.
  split; [rewrite SEGS; reflexivity|].
  split; [exact FZ|].
  split; [unfold OPS_MAX in *; lia|].
  split; [lia|]. split; [exact HW|]. split; [exact Hn|].
  split.
  { unfold head_regs. split; [geq X1|]. split; [geq X1|]. split; [geq X1|]. split; [geq X1|].
    intros HB. unfold head_body, OPS_MAX in HB. specialize (HX HB).
    split; [geq X1|]. split; [geq X1|]. split; [etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|];
      exact HX|].
    split; [geq X1|]. split; [geq X1|]. split; [geq X1|]. split; [geq X1|]. split; [geq X1|].
    geq X1. }
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact HRO|]. split; [exact HIK|].
  split.
  { destruct HST as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros _. exact S3. }
  assert (Hn2 : 0 <= nfd <= t + 2) by exact Hnfd.
  split; [exact HDK|]. split; [exact HGL|]. split; [lia|]. split; [exact HOUT|].
  split; [exact HREL|].
  split; [exact Hes|]. split; [exact Hcost|]. exact HRI.
Qed.

End Tail48.
