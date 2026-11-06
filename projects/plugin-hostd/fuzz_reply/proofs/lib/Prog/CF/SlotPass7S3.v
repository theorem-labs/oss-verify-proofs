(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, module names and numbers changed; 959 of its 1011 lines of code are new or changed and 1064 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/source_reset.v, with its module names changed; 392 of its 455 lines of code are new or changed and 948 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass7S3.v, with its module paths, module names, addresses and numbers changed; 52 of its 367 lines of code are new or changed and 140 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessGlue relay_event_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_event_c strnlen_c memcpy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass7D SlotPass7RV SlotPass7R HarnessFrame SlotPass7 SlotPass7T1 SlotPass7T2 SlotPass7S.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require SlotEntry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma s3_c1 : forall segs m a b, rw_cells segs m a [C1 b] -> bytes_at segs m a [b].
Proof. intros segs m a b ((_ & H) & _). exact H. Qed.

Lemma s3_outv : forall segs m a v0 v1 v2 v3, rw_cells segs m a [C8 v0; C8 v1; C8 v2; C8 v3] ->
  bytes_at segs m (a + 8) (le8 v1) /\ bytes_at segs m (a + 24) (le8 v3).
Proof.
  intros segs m a v0 v1 v2 v3 ((_ & H) & _). cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  apply bytes_at_app in H as (_ & H). rewrite length_le8 in H.
  apply bytes_at_app in H as (H1 & H). rewrite length_le8 in H.
  apply bytes_at_app in H as (_ & H3). rewrite length_le8 in H3.
  split.
  - replace (a + 8) with (a + Z.of_nat 8) by lia. exact H1.
  - replace (a + 24) with (a + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact H3.
Qed.

Lemma s3_dj : forall SP a n, a + n <= SP - 96 -> disjoint_from [(SP - CHECK_SHAPE_EVENT_K, SP)] a n.
Proof. intros SP a n H. cbn [disjoint_from]. unfold CHECK_SHAPE_EVENT_K. split; [lia|exact I]. Qed.

Lemma op7s3_run : check_shape_event_contract ->
  forall (SP Q lo gone : Z) (nout out : word) (e slack ob : list byte)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 <= SP < 2 ^ 64 -> 0 <= Q < 2 ^ 64 ->
  stk rsegs m lo SP -> lo + 96 <= SP -> SP mod 16 = 0 -> mem_inv rsegs m ->
  bytes_at rsegs m Q (e ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) e ->
  (- (Q + Z.of_nat (length e) + 1)) mod 8 <= Z.of_nat (length slack) ->
  Q + Z.of_nat (length (e ++ Z_to_bv 8 0 :: slack)) <= SP - 96 ->
  0x31018 <= SP - 96 ->
  bytes_at rsegs m 0x30fc8 [Z_to_bv 8 gone] -> (gone = 0 \/ gone = 1) ->
  bytes_at rsegs m 0x31000 (le8 nout) -> bytes_at rsegs m 0x31010 (le8 out) ->
  bytes_at rsegs m (bv_unsigned out) ob -> Z.of_nat (length ob) = bv_unsigned nout ->
  bv_unsigned out + bv_unsigned nout <= SP - 96 ->
  (0 < bv_unsigned nout -> 0 < bv_unsigned out) ->
  ((gone = 1 /\ bv_unsigned nout = 0) \/ (gone = 0 /\ ob = e ++ [Z_to_bv 8 0])) ->
  evt rsegs (fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x140c8) (Z_to_bv 64 SP) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 Q) (Z_to_bv 64 Q)
        a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x15664) fc None m'
        (seg_rom rsegs) /\
      munch [(SP - 96, SP)] m m' /\ wmono rsegs m m')
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x140b8) fc None m (seg_rom rsegs)).
Proof.
  intros CK SP Q lo gone nout out e slack ob x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HSP HQ ST SLO SAL MI BE NZ SL DJE DJG BG HG BN BO BOB LOB DJO
    POS REL.
  assert (USP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
  assert (UQ : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply (op7_chk Q)|].
  intros ms ->.
  eapply evt_cut.
  { apply (CK (Z_to_bv 64 0x140c0) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) (Z_to_bv 64 Q) x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m lo gone nout out e slack ob).
    - rewrite USP. exact ST.
    - rewrite USP. unfold CHECK_SHAPE_EVENT_K. lia.
    - rewrite USP. exact SAL.
    - exact MI.
    - rewrite UQ. exact BE.
    - exact NZ.
    - rewrite UQ. exact SL.
    - rewrite USP, UQ. apply s3_dj. exact DJE.
    - exact BG.
    - exact HG.
    - rewrite USP. apply (s3_dj SP 0x30fc8 1). lia.
    - exact BN.
    - rewrite USP. apply (s3_dj SP 0x31000 8). lia.
    - exact BO.
    - rewrite USP. apply (s3_dj SP 0x31010 8). lia.
    - exact BOB.
    - exact LOB.
    - rewrite USP. apply s3_dj. exact DJO.
    - exact POS.
    - exact REL. }
  intros ms (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & _).
  rewrite USP in MU. change CHECK_SHAPE_EVENT_K with 96 in MU.
  rewrite (ret_pc_even 0x140c0); [|lia|reflexivity].
  eapply evt_cut; [apply (op7_fr Q)|].
  intros ms ->.
  apply evt_done. exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [reflexivity|]. split; [exact MU|exact WM].
Qed.

Ltac s3_reg GR5 PR GR r :=
  rewrite GR5; etransitivity; [exact (PR r ltac:(unfold callee_saved; lia))|]; rewrite GR.

Ltac gin := intros i Hi; simpl in Hi; apply in_G_bss; gunf; lia.

Theorem op7_c3_holds : forall F RI, op7_c3_stmt F RI.
Proof.
  intros F RI B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es
    hj c HF CK HFR HC HP.
  destruct HP as (L2 & A2 & R2 & m2 & md2 & K0 & M & EL & res & e & nout' & cap' & out' & ev' & HP).
  cbv zeta in HP.
  destruct HP as (-> & HR1 & R8 & R18 & R9 & R23 & HK0 & HM0 & HKM & HKS & HEL & LE & NZE & BE & RM2 & INIT2 & RO2 & NZ &
    AL16 & FRESH & INB & RSEP & CLS & CBR & CEI & COUTV & CERR & CLOCK & LF & LT & (qr & LIVE2 & RES)).
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & PL & AX & BW & SPLO & SPHI & IL).
  pose proof HF as (FF & _ & PRE & _).
  assert (HFREE : ms_free B = 0x15664) by (unfold frame_facts in FF; tauto).
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  pose proof FF as FFA. do 30 (destruct FFA as [_ FFA]). specialize (FFA rc fx').
  do 5 (destruct FFA as [_ FFA]). destruct FFA as (SLP & CTX & _ & NDB & _).
  destruct PRE as (((_ & _ & _ & _ & _ & SPAL & _ & _ & _ & TP0 & _) & _) & _).
  destruct HC as (FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd &
    HOUT & HREL & Hes & Hcost & HRI).
  destruct HR as (NO0 & _).
  destruct HGL as (_ & _ & _ & _ & G5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGN & _ & _ & HGONE & _).
  destruct HR1 as ((B2 & B3 & B4 & B20) & F21 & F22 & F24 & F25 & F26 & F27).
  pose proof (aa_laws (API rc)) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SB1 : YM05.alloc_ceiling + 65344 <= slot_sp E) by (unfold slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia).
  assert (SB2 : slot_sp E < 2 ^ 63) by (unfold slot_sp, SLOT_FRAME; lia).
  assert (SB3 : slot_sp E mod 16 = 0) by (unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HKK : YM05.alloc_ceiling <= slot_sp E - OP7_K) by (change OP7_K with 8384; lia).
  pose proof RM2 as (MR2 & WF2 & BD2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  destruct (mr_model _ _ LAWS _ _ _ _ MR2) as (Hh2 & Hl2 & _).
  pose proof FRESH as (FR1 & FR2 & _).
  pose proof (bv_unsigned_in_range 64 out') as ROUT. pose proof (bv_unsigned_in_range 64 nout') as RNOUT.
  pose proof (bv_unsigned_in_range 64 out) as ROUT0.
  unfold bv_modulus in ROUT, RNOUT, ROUT0. cbn in ROUT, RNOUT, ROUT0.
  assert (HO : op7_live cl br dd EL = true -> 0 < bv_unsigned cap ->
      fresh_block (rc := rc) B (bv_unsigned out) (bv_unsigned cap)).
  { intros _ HCP. exact (op7_out_hi rc B L A mem nout cap out HOUT HCP). }
  assert (RM2F : rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L2 A2 m2 md2).
  { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ RM2); [intros a X; exact X|intros q X; right; exact X]. }
  assert (G5' : rw_cells (ms_segs B) m2 0x30fc8 [C1 (Z_to_bv 8 gn)]).
  { eapply (op7_glob_cells B API LS SH SK ra empty rc fx j E CS);
      [exact HF|exact HMR|exact RM2F|exact FRESH|exact HO|exact G5|gside]. }
  pose proof RO2 as RO2r. rewrite SEG in RO2r.
  assert (BG : bytes_at rsegs (normalize rsegs m2) 0x30fc8 [Z_to_bv 8 gn]).
  { apply bytes_at_normalize; [exact RO2r|rewrite <- SEG; exact (s3_c1 _ _ _ _ G5')]. }
  destruct (s3_outv _ _ _ _ _ _ _ COUTV) as (BN0 & BO0).
  rewrite SEG in BN0, BO0.
  assert (BN : bytes_at rsegs (normalize rsegs m2) 0x31000 (le8 nout'))
    by (apply bytes_at_normalize; [exact RO2r|exact BN0]).
  assert (BO : bytes_at rsegs (normalize rsegs m2) 0x31010 (le8 out'))
    by (apply bytes_at_normalize; [exact RO2r|exact BO0]).
  assert (OBX : exists ob, bytes_at rsegs m2 (bv_unsigned out') ob /\ Z.of_nat (length ob) = bv_unsigned nout' /\
      bv_unsigned out' + bv_unsigned nout' <= slot_sp E - 96 /\ (0 < bv_unsigned nout' -> 0 < bv_unsigned out') /\
      ((gn = 1 /\ bv_unsigned nout' = 0) \/ (gn = 0 /\ ob = e ++ [Z_to_bv 8 0]))).
  { destruct HGN as [G0|G1].
    - assert (LV : op7_live cl br dd EL = true).
      { destruct (proj1 HGONE G0) as (-> & -> & ->). unfold op7_live, send_live, send_off.
        replace (EL + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      destruct (LT LV) as (N1 & (C1 & C2) & _ & (FO1 & FO2 & _) & _ & (junk & BJ & LJ) & _).
      exists (e ++ [Z_to_bv 8 0]).
      rewrite app_assoc in BJ. apply bytes_at_app in BJ as (BJ & _). rewrite SEG in BJ.
      split; [exact BJ|]. split; [rewrite length_app; cbn [length]; lia|].
      split; [lia|]. split; [lia|]. right. split; [exact G0|reflexivity].
    - assert (LV : op7_live cl br dd EL = false).
      { unfold op7_live, send_live, send_off.
        destruct (cl <? 0) eqn:C1; [reflexivity|]. destruct (br =? 1) eqn:C2; [reflexivity|].
        destruct (EL + 1 =? 0) eqn:C3; [reflexivity|]. cbn [orb negb andb].
        apply Z.eqb_neq. destruct (proj2 HGONE G1) as [X|[X|X]];
          [apply Z.ltb_ge in C1; lia|apply Z.eqb_neq in C2; lia|lia]. }
      destruct (LF LV) as (-> & -> & ->).
      assert (OB0 : bv_unsigned out <= YM05.alloc_ceiling).
      { destruct HOUT as ((O & junk & [(_ & X & _)|(CP0 & _ & _ & (_ & X & _) & _)]) & _); lia. }
      exists []. split; [apply bytes_at_nil; lia|]. split; [cbn [length]; lia|].
      split; [lia|]. split; [lia|]. left. split; [exact G1|exact NO0]. }
  destruct OBX as (ob & BOB0 & LOB & DJO & POS & REL).
  assert (R8M := Z.mod_pos_bound (- (res + EL + 1)) 8 ltac:(lia)).
  assert (ZSL : Z.of_nat (Z.to_nat ((- (res + EL + 1)) mod 8)) = (- (res + EL + 1)) mod 8) by (apply Z2Nat.id; lia).
  assert (SLX : exists slack, bytes_at rsegs m2 res (e ++ Z_to_bv 8 0 :: slack) /\
      Z.of_nat (length slack) = (- (res + EL + 1)) mod 8).
  { exists (slack_at rsegs m2 (res + EL + 1) (Z.to_nat ((- (res + EL + 1)) mod 8))).
    split; [|rewrite slack_at_len; exact ZSL].
    apply bytes_split3; [rewrite <- SEG; exact BE|]. rewrite LE.
    apply slack_at_bytes; [lia|rewrite ZSL; lia|].
    intros i Hi. rewrite ZSL in Hi.
    apply (SLP L2 A2 m2 md2 res (EL + 1) _ MR2 INB).
    assert (E8 : forall N, 8 * ((N + 7) / 8) = N + (- N) mod 8) by (intros N; Z.div_mod_to_equations; lia).
    rewrite E8. replace (res + (EL + 1)) with (res + EL + 1) by lia. lia. }
  destruct SLX as (slack & BES & LSL).
  assert (ST : stk rsegs m2 (slot_sp E - 96) (slot_sp E)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs m2 a) by (rewrite <- SEG; apply SC2; left; change OP7_K with 8384; lia).
    split; [exact W|].
    destruct (writable_hi_present m2 a ltac:(lia) W) as [bb Eb]. exists bb. unfold mrd, wa. rewrite Eb. reflexivity. }
  rewrite SEG.
  eapply (kseg R2 (Z_to_bv 64 0x140b8) m2 md2); [exact wx_apart_rsegs|exact RO2r|exact Hh2|exact Hl2| | |].
  - assert (E2 : reg_get R2 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
    assert (E9 : reg_get R2 9 = Z_to_bv 64 res) by exact R9.
    unfold Regs6ss.mkR_of. rewrite E2, E9.
    apply (op7s3_run CK (slot_sp E) res (slot_sp E - 96) gn nout' out' e slack ob).
    + lia.
    + lia.
    + apply stk_normalize; [exact ST|lia].
    + lia.
    + exact SB3.
    + apply mem_inv_normalize.
    + apply bytes_at_normalize; [exact RO2r|exact BES].
    + exact NZE.
    + rewrite LE, LSL. lia.
    + rewrite length_app. cbn [length]. lia.
    + lia.
    + exact BG.
    + exact HGN.
    + exact BN.
    + exact BO.
    + apply bytes_at_normalize; [exact RO2r|exact BOB0].
    + exact LOB.
    + exact DJO.
    + exact POS.
    + exact REL.
  - intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc m0 regs1 m1 (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EQ & MU & WM)
      GR MREL ROS.
    injection EQ as ER EP EM. subst R pc m0.
    assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x140c8) by (rewrite GR; reflexivity).
    assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (slot_sp E)) by (rewrite GR; reflexivity).
    assert (G4 : YK11.getr regs1 4 = getr (ss_regs E) 4) by (rewrite GR; exact B4).
    assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 res) by (rewrite GR; reflexivity).
    destruct (rmid_norm B (API rc) OP7_K (slot_sp E) (fun _ => False) (fun _ => False) L2 A2 m2 md2 m' m1
      [(slot_sp E - 96, slot_sp E)] SEG RO2r MREL ROS MU WM MR2 WF2 BD2 HKK SC2) as (RM3 & _ & _).
    { intros a Ha HOt. destruct (hg_not_out _ _ HOt) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      left. change OP7_K with 8384. lia. }
    { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a MR2 Ho).
      apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-. left. lia. }
    { intros q0 n0 i HQ HI HOt. destruct (hg_not_out _ _ HOt) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      destruct (mr_blocks _ _ LAWS _ _ _ _ q0 n0 i MR2 HQ HI) as (_ & H1 & H2 & _). lia. }
    pose proof RM3 as (MR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC3).
    assert (RO1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs _ _ RO2r ROS).
    assert (SP1 : spZ regs1 = slot_sp E) by (unfold spZ; rewrite G2; apply unsigned_lit; lia).
    assert (CP : call_pre B (aa_MR (API rc)) L2 A2 regs1 m1 md2).
    { apply (proj2 (call_pre_k_alloc B (aa_MR (API rc)) L2 A2 regs1 m1 md2)).
      eapply (cpk_of_rmid B (API rc)); [exact RM3|exact INIT2| | | | | | | |].
      - rewrite G1. apply ret_ok_even. vm_compute. reflexivity.
      - rewrite G4. exact TP0.
      - rewrite SP1. exact SB3.
      - rewrite SP1. change OP7_K with 8384. unfold ALLOC_STACK. lia.
      - rewrite SP1. lia.
      - unfold ALLOC_STACK. lia.
      - rewrite SP1. unfold ALLOC_STACK. lia.
      - rewrite SP1. lia. }
    pose proof INB as INB'. unfold blocks in INB'. apply in_map_iff in INB' as ([p k] & Ep & Hp).
    cbn [fst snd] in Ep. injection Ep as Ep Ek. subst k.
    destruct (RES p) as (bnd & OKB & _ & POST).
    pose proof (HFR fx') as FRc. unfold free_contract_rt in FRc. rewrite SEG, HFREE in FRc.
    eapply SR_bind.
    { apply (FRc L2 A2 regs1 m1 md2 p (EL + 1) bnd CP RO1 Hp); [rewrite G10, Ep; reflexivity|exact OKB]. }
    intros c' (L4 & A4 & regs4 & m4 & md4 & -> & CPo & (b1 & b2 & BLa & BLb) & _ & RO4 & _ & SURV & INITi & LEN &
      RES4).
    destruct (rmid_of_free B (API rc) _ _ _ _ _ _ _ _ _ _ _ p (EL + 1) AX CTX MR3 WF2 CPo Hp ltac:(lia) LEN SURV)
      as (RMf & PRf).
    rewrite SP1 in RMf.
    assert (WR3 : forall a, slot_sp E - OP7_K <= a < slot_sp E -> writable_at (ms_segs B) m1 a)
      by (intros a Ha; apply SC3; left; exact Ha).
    pose proof (rmid_widen B (API rc) ALLOC_STACK (slot_sp E) OP7_K (slot_sp E) (fun _ => False)
      (fun q => q = ptr_addr L2 p) _ _ _ _ _ _ _ _ MR3 ltac:(change OP7_K with 8384; unfold ALLOC_STACK; lia)
      ltac:(lia) ltac:(change OP7_K with 8384; lia) ltac:(lia) WR3 (fun a _ X => X) RMf) as RMfw.
    pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF2 RM3 RMfw) as R34.
    pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM2 R34) as R24.
    pose proof RMf as (MR4 & _).
    destruct (mr_model _ _ LAWS _ _ _ _ MR4) as (Hh4 & Hl4 & _).
    destruct (CF.SlotEntry.entry_errno_cells B SEG ETP EOFF m4) as (ev & CEV).
    assert (TR : forall a cs, rw_cells (ms_segs B) m2 a cs ->
        (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals G_reply (a + i)) -> rw_cells (ms_segs B) m4 a cs).
    { intros a cs H D.
      apply (rmid_rw_img B (API rc) AX OP7_K (slot_sp E) _ _ L2 A2 m2 md2 L4 A4 m4 md4 a cs IL HKK MR2 R34 H).
      intros i Hi. split; [exact (PL _ (D i Hi))|intros [[]|[]]]. }
    assert (E42 : reg_get regs4 2 = Z_to_bv 64 (slot_sp E)).
    { etransitivity; [exact (PRf 2 ltac:(unfold callee_saved; lia))|]. exact G2. }
    rewrite G1.
    eapply (kseg_raw regs4 (Z_to_bv 64 0x140c8) m4 md4); [exact Hh4|exact Hl4| | |].
    + unfold Regs6ss.mkR_of. rewrite E42. apply (op7_tl (slot_sp E)).
    + intros ms (s3 & -> & _). do 3 eexists. reflexivity.
    + intros R pc m0 regs5 (s3 & EQ & ES3) GR5. injection EQ as ER EP EM. subst R pc m0 s3.
      apply SR_ret. unfold op7_post.
      exists L4, A4, regs5, m4, md4, (K0 + M), EL, res, nout', cap', out', ev.
      split; [rewrite SEG; reflexivity|].
      split.
      { unfold tail_regs, base_regs, fix_regs. repeat split.
        - rewrite GR5. reflexivity.
        - s3_reg GR5 PRf GR 3. exact B3.
        - s3_reg GR5 PRf GR 4. exact B4.
        - s3_reg GR5 PRf GR 20. exact B20.
        - rewrite GR5. reflexivity.
        - s3_reg GR5 PRf GR 21. exact F21.
        - s3_reg GR5 PRf GR 24. exact F24.
        - s3_reg GR5 PRf GR 25. exact F25.
        - s3_reg GR5 PRf GR 26. exact F26.
        - s3_reg GR5 PRf GR 27. exact F27.
        - rewrite GR5. etransitivity; [exact (PRf 18 ltac:(unfold callee_saved; lia))|]. rewrite GR. exact R18.
        - s3_reg GR5 PRf GR 23. exact R23.
        - s3_reg GR5 PRf GR 22. exact F22. }
      split; [lia|]. split; [exact HKS|]. split; [lia|].
      split.
      { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ R24).
        - intros a [X|[[]|[]]]. exact X.
        - intros q [X|[[]|X]]; [right; exact X|left; cbv beta in X; rewrite X; exact Ep]. }
      split; [exact (INITi INIT2)|].
      split; [rewrite SEG; exact RO4|].
      split; [exact FRESH|].
      split; [exact RSEP|].
      assert (ND : List.NoDup (map fst (blocks L2 A2))).
      { first [exact (NDB L2 A2 m2 md2 MR2) | apply hf_nodup; exact (NDB L2 A2 m2 md2 MR2) |
          apply NoDup_ListNoDup; exact (NDB L2 A2 m2 md2 MR2)]. }
      rewrite BLa, map_app in ND. cbn [map fst] in ND. apply NoDup_remove_2 in ND. rewrite <- map_app, Ep in ND.
      assert (IN24 : forall q mm, In (q, mm) (blocks L4 A4) -> In (q, mm) (blocks L2 A2) /\ q <> res).
      { intros q mm Hq. rewrite BLb in Hq. split.
        - rewrite BLa. apply in_app_or in Hq as [X|X]; apply in_or_app; [left; exact X|right; right; exact X].
        - intros ->. apply ND. exact (in_map fst _ (res, mm) Hq). }
      assert (IN42 : forall q mm, In (q, mm) (blocks L2 A2) -> q <> res -> In (q, mm) (blocks L4 A4)).
      { intros q mm Hq NQ. rewrite BLa in Hq. rewrite BLb.
        apply in_app_or in Hq as [X|[X|X]]; apply in_or_app; [left; exact X| |right; exact X].
        exfalso. injection X as X1 _. apply NQ. rewrite <- X1. exact Ep. }
      split.
      { intros q mm Hq. destruct (IN24 q mm Hq) as (Hq2 & NQ).
        destruct (CLS q mm Hq2) as [X|[(X & _)|X]]; [left; exact X|contradiction|right; exact X]. }
      split; [apply TR; [exact CBR|gin]|].
      split; [apply TR; [exact CEI|gin]|].
      split; [apply TR; [exact COUTV|gin]|].
      split; [rewrite SEG; exact CEV|].
      split; [apply TR; [exact CLOCK|gin]|].
      split; [exact LF|].
      split.
      { intros LV. destruct (LT LV) as (N1 & C1 & IN & FB & NR & (junk & BJ & LJ) & DIF).
        split; [exact N1|]. split; [exact C1|].
        split; [exact (IN42 _ _ IN NR)|]. split; [exact FB|].
        split.
        { exists (e ++ [Z_to_bv 8 0]), junk.
          split; [|split; [rewrite length_app; cbn [length]; lia|exact LJ]].
          rewrite <- app_assoc.
          eapply (rmid_bytes_block B (API rc) BW); [exact R34|exact IN|lia| |exact BJ|lia| |].
          - intros [[]|X]. cbv beta in X. apply NR. rewrite X. exact Ep.
          - rewrite !length_app. cbn [length]. lia.
          - intros i _ [[]|[]]. }
        exact DIF. }
      assert (LIVE4 : op7_live cl br dd EL = true -> forall q, live_at L2 A2 q (bv_unsigned out') (bv_unsigned cap') ->
          live_at L4 A4 q (bv_unsigned out') (bv_unsigned cap')).
      { intros LV q (Hq & Eq). destruct (LT LV) as (_ & _ & _ & _ & NR & _).
        pose proof RMf as (_ & _ & _ & _ & _ & PAf & _).
        assert (NA : ptr_addr L2 q <> ptr_addr L2 p) by (rewrite Eq, Ep; exact NR).
        assert (Hq4 : In (q, bv_unsigned cap') (user_blocks A4))
          by exact (SURV _ _ Hq (fun X => NA (f_equal (ptr_addr L2) X))).
        split; [exact Hq4|]. rewrite <- Eq. exact (PAf _ _ Hq Hq4 NA). }
      exact (POST L4 A4 [] eq_refl RES4 (bv_unsigned out') (fun LV => LIVE4 LV _ (LIVE2 LV))).
Qed.
