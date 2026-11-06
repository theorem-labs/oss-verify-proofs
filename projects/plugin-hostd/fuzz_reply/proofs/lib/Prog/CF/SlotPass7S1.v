(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, module names and numbers changed; 959 of its 1011 lines of code are new or changed and 1064 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/source_reset.v, with its module names changed; 392 of its 455 lines of code are new or changed and 948 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass7S3.v, with its module paths, module names, addresses and numbers changed; 246 of its 299 lines of code are new or changed and 402 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require Import StrFun.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass7D SlotPass7RV SlotPass7 SlotPass7T2 SlotPass7S.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma s1_nz_prefix : forall (l : list byte) i, find_byte 0 l = Some i ->
  forall b, In b (firstn i l) -> bv_unsigned b <> 0.
Proof.
  induction l as [|x l IH]; intros i H b Hb; cbn in H; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [EX|NX].
  - injection H as <-. cbn in Hb. destruct Hb.
  - destruct (find_byte 0 l) as [i'|] eqn:FL; [|discriminate]. injection H as <-.
    cbn in Hb. destruct Hb as [<-|Hb]; [exact NX|exact (IH i' eq_refl b Hb)].
Qed.

Lemma s1_strnlen_facts : forall M (buf : list byte), Z.of_nat (length buf) = M ->
  0 <= strnlen_res M buf <= M /\
  Z.of_nat (length (firstn (Z.to_nat (strnlen_res M buf)) buf)) = strnlen_res M buf /\
  ~ In (Z_to_bv 8 0) (firstn (Z.to_nat (strnlen_res M buf)) buf).
Proof.
  intros M buf HL. unfold strnlen_res. rewrite (firstn_all2 (n := Z.to_nat M) buf) by lia.
  destruct (find_byte 0 buf) as [i|] eqn:FB.
  - destruct (find_byte_Some _ _ _ FB) as (Hl & _ & _). rewrite Nat2Z.id, length_firstn.
    split; [lia|]. split; [lia|]. intros Hin. apply (s1_nz_prefix buf i FB _ Hin). reflexivity.
  - rewrite (firstn_all2 (n := Z.to_nat M) buf) by lia. split; [lia|]. split; [lia|].
    intros Hin. destruct (In_nth_error _ _ Hin) as (j & Hj). apply (find_byte_None _ _ FB j _ Hj). reflexivity.
Qed.

Lemma s1_sub_bytes : forall segs m a (pl : list byte) k n, bytes_at segs m a pl -> 0 <= k -> 0 <= n ->
  k + n <= Z.of_nat (length pl) ->
  bytes_at segs m (a + k) (firstn (Z.to_nat n) (skipn (Z.to_nat k) pl)) /\
  Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat k) pl))) = n.
Proof.
  intros segs m a pl k n H Hk Hn Hkn.
  split; [|rewrite length_firstn, length_skipn; lia].
  rewrite <- (firstn_skipn (Z.to_nat k) pl) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Z.of_nat (Nat.min (Z.to_nat k) (length pl))) with k in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat k) pl)) in H. apply bytes_at_app in H.
  exact (proj1 H).
Qed.

Lemma s1_first1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros [|k] d H; cbn in H |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma op7_run : strnlen_contract -> forall (P N K S : Z) (pl : list byte)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 <= K <= N -> N < 2 ^ 26 -> bytes_at rsegs m P pl -> Z.of_nat (length pl) = N -> 0 < P ->
  P + N <= S - 32 -> 2 ^ 20 <= S - 32 -> S < 2 ^ 64 -> stk rsegs m (S - 32) S -> mem_inv rsegs m ->
  evt rsegs (fun ms => exists (K' M EL : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
                          (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x1408c) (Z_to_bv 64 S) x3 x4 t0 t1 t2 (Z_to_bv 64 (P + K')) x9
        (Z_to_bv 64 (EL + 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 M) (Z_to_bv 64 EL) x20 x21 x22
        (Z_to_bv 64 (N - K')) x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x157a4) fc None m' (seg_rom rsegs) /\
      EL = strnlen_res M (firstn (Z.to_nat M) (skipn (Z.to_nat K') pl)) /\
      K <= K' <= N /\ 0 <= M <= N - K' /\
      K' + M = (if K + 2 <=? N then K + 2 + Z.min (bv_unsigned (nth (Z.to_nat K) pl (Z_to_bv 8 0)) +
        256 * bv_unsigned (nth (Z.to_nat (K + 1)) pl (Z_to_bv 8 0))) (N - (K + 2)) else N) /\
      munch [(S - 32, S)] m m' /\ wmono rsegs m m')
    (MS (mkR x1 (Z_to_bv 64 S) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17
      x18 x19 x20 x21 x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13dc0) fc None m
      (seg_rom rsegs)).
Proof.
  intros SNL P N K S pl x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m HK HN BP LP P0 PS SLO SHI ST MI.
  eapply evt_cut.
  { apply (op7_head P N K x1 (Z_to_bv 64 S) x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24
      x25 x26 x27 x28 x29 x30 x31 F fc m (seg_rom rsegs) (nth (Z.to_nat K) pl (Z_to_bv 8 0))
      (nth (Z.to_nat (K + 1)) pl (Z_to_bv 8 0))); [lia|lia| |].
    - intros HK1. change (Z_to_bv 64 (P + K)) with (wa (P + K)).
      rewrite (bytes_at_read rsegs m P pl K 1 BP) by lia.
      rewrite (s1_first1 pl (Z.to_nat K) (Z_to_bv 8 0)) by lia. reflexivity.
    - intros HK1. replace (P + K + 1) with (P + (K + 1)) by ring.
      change (Z_to_bv 64 (P + (K + 1))) with (wa (P + (K + 1))).
      rewrite (bytes_at_read rsegs m P pl (K + 1) 1 BP) by lia.
      rewrite (s1_first1 pl (Z.to_nat (K + 1)) (Z_to_bv 8 0)) by lia. reflexivity. }
  intros ms (s0 & s2 & s7 & K' & -> & E0 & E7 & HK' & HS2 & HKS). subst s0 s7.
  pose proof (bv_unsigned_in_range 64 s2) as R2. unfold bv_modulus in R2. cbn in R2.
  rewrite <- (Z_to_bv_bv_unsigned s2).
  destruct (s1_sub_bytes rsegs m P pl K' (bv_unsigned s2) BP ltac:(lia) ltac:(lia) ltac:(lia)) as (BB & LB).
  set (M := bv_unsigned s2) in *.
  set (buf := firstn (Z.to_nat M) (skipn (Z.to_nat K') pl)) in *.
  eapply evt_cut.
  { apply (SNL (Z_to_bv 64 0x14080) (Z_to_bv 64 S) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K')) x9 x12 x13 x14
      (Z_to_bv 64 1) x16 x17 (Z_to_bv 64 M) x19 x20 x21 x22 (Z_to_bv 64 (N - K')) x24 x25 x26 x27 x28 x29 x30 x31
      F fc m (P + K') M (S - 32) buf);
      [exact BB| |lia|lia|rewrite unsigned_lit by lia; exact ST|rewrite unsigned_lit by lia; lia
      |rewrite unsigned_lit by lia; lia|exact MI].
    unfold memchr_ok. rewrite (firstn_all2 (n := Z.to_nat M) buf) by lia. destruct (find_byte 0 buf); [left|]; lia. }
  intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & _ & _ & _).
  rewrite unsigned_lit in MU by lia.
  rewrite (ret_pc_even 0x14080); [|lia|reflexivity].
  eapply evt_cut; [apply op7_mal|].
  intros ms (a0 & -> & ->).
  apply evt_done. exists K', M, (strnlen_res M buf), t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HKS|].
  split; [exact MU|exact WM].
Qed.

Ltac s1_reg PRES GR r :=
  etransitivity; [exact (PRES r ltac:(unfold callee_saved; lia))|]; rewrite GR.

Theorem op7_c1_holds : forall F RI, op7_c1_stmt F RI.
Proof.
  intros F RI B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es
    hj HF SN HMA HRE HK HC.
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & GPL & AX & BW & SPLO & SPHI & IMGL).
  pose proof HF as (FF & _ & PRE & _).
  pose proof FF as (_ & _ & HMAL & _).
  pose proof FF as FFA. do 30 (destruct FFA as [_ FFA]). specialize (FFA rc fx').
  do 6 (destruct FFA as [_ FFA]). destruct FFA as (CTX & BLO & NDB & _).
  destruct PRE as (((_ & _ & _ & _ & _ & SPAL & _ & _ & _ & TP0 & _ & _ & _ & INP & _) & LEN & BD & _) &
    _ & _ & _ & _ & _ & NT & _).
  destruct HC as (FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd &
    HOUT & HREL & Hes & Hcost & HRI).
  destruct HR as (_ & _ & (B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22 & _ & R15).
  pose proof (aa_laws (API rc)) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HIK as (_ & _ & _ & IK4).
  pose proof HDK as (DK1 & _ & DK3 & _).
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMX).
  pose proof HOUT as (_ & HCAP).
  pose proof (bv_unsigned_in_range 64 mx) as RMX. pose proof (bv_unsigned_in_range 64 cap) as RCAP.
  unfold bv_modulus in RMX, RCAP. cbn in RMX, RCAP.
  pose proof Hn as HnI. unfold INPUT_MAX in Hn.
  assert (SB1 : YM05.alloc_ceiling + 65344 <= slot_sp E) by (unfold slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia).
  assert (SB2 : slot_sp E < 2 ^ 63) by (unfold slot_sp, SLOT_FRAME; lia).
  assert (SB3 : slot_sp E mod 16 = 0) by (unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HN0 : 0 < ss_n E) by lia.
  destruct INP as [(HN00 & _) | (_ & q & Hq & Eq)]; [lia|].
  destruct (DK1 q (ss_n E) Hq) as (_ & q' & Hq' & Eq').
  { rewrite Eq. exact (NT HN0). }
  assert (INB : In (ss_p E, ss_n E) (blocks L A)).
  { unfold blocks. apply in_map_iff. exists (q', ss_n E). split; [cbv beta; cbn [fst snd]; rewrite Eq', Eq; reflexivity|exact Hq']. }
  destruct (block_facts B (aa_MR (API rc)) LAWS L A mem md (ss_p E) (ss_n E) 0 HMR INB ltac:(lia))
    as (_ & PLO & PHI & _).
  assert (BS0 : bytes_at (ms_segs B) mem (ss_p E) (ss_pl E)).
  { apply bytes_at_of_mbyte; [lia|lia|]. intros i Hi.
    rewrite (DK3 (Z.of_nat i)) by lia. rewrite (BD (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity. }
  assert (SCR : forall a, sk B OP7_K (slot_sp E) a -> writable_at (ms_segs B) mem a).
  { intros a [Ha|Ha]; apply IK4; [left|right; exact Ha].
    change OP7_K with 8384 in Ha. unfold slot_sp, SLOT_FRAME in Ha. unfold SLOT_STACK. lia. }
  assert (ST : stk rsegs mem (slot_sp E - 32) (slot_sp E)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (rewrite <- SEG; apply SCR; left; change OP7_K with 8384; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb Eb]. exists bb. unfold mrd, wa. rewrite Eb. reflexivity. }
  pose proof HRO as RO. rewrite SEG in RO.
  pose proof BS0 as BS0r. rewrite SEG in BS0r.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E15 : reg_get regs 15 = Z_to_bv 64 1) by exact R15.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - K)) by exact R23.
  rewrite SEG.
  eapply (kseg regs (Z_to_bv 64 0x13dc0) mem md); [exact wx_apart_rsegs|exact RO|exact Hh|exact Hl| | |].
  - unfold Regs6ss.mkR_of. rewrite E2, E8, E15, E23.
    apply (op7_run SN (ss_p E) (ss_n E) K (slot_sp E) (ss_pl E));
      [lia|lia|apply bytes_at_normalize; [exact RO|exact BS0r]|lia|lia|lia|lia|lia
      |apply stk_normalize; [exact ST|lia]|apply mem_inv_normalize].
  - intros ms (K0 & M & EL & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc m0 regs1 m1 (K0 & M & EL & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
      EQ & EEL & HK0 & HM & HKS & MU & WM) GR MREL ROS.
    injection EQ as ER EP EM. subst R pc m0.
    destruct (s1_strnlen_facts M (firstn (Z.to_nat M) (skipn (Z.to_nat K0) (ss_pl E)))) as (ELB & ELE & ELZ).
    { rewrite length_firstn, length_skipn. lia. }
    destruct (s1_sub_bytes (ms_segs B) mem (ss_p E) (ss_pl E) K0 M BS0 ltac:(lia) ltac:(lia) ltac:(lia)) as (BB & LB).
    rewrite <- EEL in ELB, ELE, ELZ.
    set (buf := firstn (Z.to_nat M) (skipn (Z.to_nat K0) (ss_pl E))) in *.
    set (ee := firstn (Z.to_nat EL) buf) in *.
    assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x1408c) by (rewrite GR; reflexivity).
    assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (slot_sp E)) by (rewrite GR; reflexivity).
    assert (G4 : YK11.getr regs1 4 = getr (ss_regs E) 4) by (rewrite GR; exact B4).
    assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 (EL + 1)) by (rewrite GR; reflexivity).
    destruct (rmid_norm B (API rc) OP7_K (slot_sp E) (fun _ => False) (fun _ => False) L A mem md m' m1
      [(slot_sp E - 32, slot_sp E)] SEG RO MREL ROS MU WM HMR HWF HBD ltac:(change OP7_K with 8384; lia) SCR)
      as (RM1 & MUR & WMR).
    { intros a Ha HO. destruct (hg_not_out _ _ HO) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      left. change OP7_K with 8384. lia. }
    { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho).
      apply hg_out. intros lo hi [EQ|[]]. injection EQ as <- <-. left. lia. }
    { intros q0 n0 i HQ HI HO. destruct (hg_not_out _ _ HO) as (lo & hi & [EQ|[]] & HX). injection EQ as <- <-.
      destruct (mr_blocks _ _ LAWS _ _ _ _ q0 n0 i HMR HQ HI) as (_ & H1 & H2 & _). lia. }
    pose proof RM1 as (MR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
    assert (RO1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs _ _ RO ROS).
    assert (SP1 : spZ regs1 = slot_sp E) by (unfold spZ; rewrite G2; apply unsigned_lit; lia).
    assert (CP : call_pre B (aa_MR (API rc)) L A regs1 m1 md).
    { apply (proj2 (call_pre_k_alloc B (aa_MR (API rc)) L A regs1 m1 md)).
      eapply (cpk_of_rmid B (API rc)); [exact RM1|exact HINIT| | | | | | | |].
      - rewrite G1. apply ret_ok_even. vm_compute. reflexivity.
      - rewrite G4. exact TP0.
      - rewrite SP1. exact SB3.
      - rewrite SP1. change OP7_K with 8384. unfold ALLOC_STACK. lia.
      - rewrite SP1. lia.
      - unfold ALLOC_STACK. lia.
      - rewrite SP1. unfold ALLOC_STACK. lia.
      - rewrite SP1. lia. }
    assert (NDA : List.NoDup (map fst (blocks L A))).
    { first [exact (NDB L A mem md HMR) | apply NoDup_ListNoDup; exact (NDB L A mem md HMR)]. }
    assert (OI : 0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L A)).
    { intros HC0. destruct HOUT as ((O & junk & [(X & _)|(_ & _ & IN & _)]) & _); [lia|exact IN]. }
    assert (O0 : bv_unsigned cap = 0 -> forall m, ~ In (bv_unsigned out, m) (blocks L A)).
    { intros HC0 m Hm. destruct HOUT as ((O & junk & [(_ & X & _)|(X & _)]) & _); [|lia].
      rewrite X in Hm. pose proof (BLO L A mem md 0 m HMR Hm). lia. }
    destruct (HRE E K (K0 + M) L A EL (op7_live cl br dd EL) (bv_unsigned mx) (bv_unsigned cap)
      G (bv_unsigned out) es hj HRI HK ltac:(lia) HnI ltac:(lia) ltac:(lia) ltac:(lia) NDA OI O0)
      as (bnd & OKB & ROOM & POST).
    destruct (ROOM [SP 0 0] eq_refl) as (RM0 & _).
    pose proof (HMA fx') as MAL. unfold malloc_contract_rt in MAL. rewrite SEG, HMAL in MAL.
    eapply SR_mono; [exact (MAL L A regs1 m1 md (EL + 1) bnd CP RO1 G10 OKB RM0)|].
    intros c' (L1 & A1 & R1 & m2 & md1 & res & -> & CPK & A0' & NZ & AL16 & FRESH & BLK & KEPT & RO2 & GK & UBK &
      INIT & RLEN & RES').
    destruct (rmid_of_cpk B (API rc) ALLOC_STACK (fun _ => False) (fun _ => False) L A regs1 m1 md L1 A1 R1 m2 md1
      AX CTX MR1 CPK RLEN (fun p n H _ _ => UBK p n H) (fun p H => UBK p 0 H)) as (RM2 & PRES).
    rewrite SP1 in RM2.
    assert (RM2W : rmid (rc := rc) B (API rc) OP7_K (slot_sp E) (fun _ => False) (fun _ => False)
      L A m1 md L1 A1 m2 md1).
    { apply (rmid_widen B (API rc) ALLOC_STACK (slot_sp E)); [exact MR1| | | | | | |exact RM2].
      - change OP7_K with 8384. unfold ALLOC_STACK. lia.
      - lia.
      - change OP7_K with 8384. lia.
      - lia.
      - intros a Ha. apply SC1. left. exact Ha.
      - intros a _ X. exact X. }
    pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM1 RM2W) as R12.
    assert (RM : rmid (rc := rc) B (API rc) OP7_K (slot_sp E) (fun _ => False) (fun _ => False)
      L A mem md L1 A1 m2 md1).
    { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ R12); intros a [X|X]; exact X. }
    pose proof RM as (MR2 & _).
    assert (BSE : bytes_at (ms_segs B) m2 (ss_p E + K0) ee).
    { assert (BE : bytes_at (ms_segs B) mem (ss_p E + K0) ee).
      { rewrite <- (firstn_skipn (Z.to_nat EL) buf) in BB. apply bytes_at_app in BB. exact (proj1 BB). }
      eapply (rmid_bytes_block B (API rc) BW); [exact RM|exact INB|lia|intros X; exact X|exact BE|lia|lia|].
      intros i _ X. exact X. }
    unfold op7_P1.
    exists L1, A1, R1, m2, md1, K0, M, EL, res, ee.
    split; [rewrite G1; reflexivity|].
    split.
    { unfold op7_regs1, base_regs. repeat split.
      - s1_reg PRES GR 2. reflexivity.
      - s1_reg PRES GR 3. exact B3.
      - s1_reg PRES GR 4. exact B4.
      - s1_reg PRES GR 20. exact B20.
      - s1_reg PRES GR 21. exact F21.
      - s1_reg PRES GR 22. exact R22.
      - s1_reg PRES GR 24. exact F24.
      - s1_reg PRES GR 25. exact F25.
      - s1_reg PRES GR 26. exact F26.
      - s1_reg PRES GR 27. exact F27. }
    split; [s1_reg PRES GR 8; reflexivity|].
    split; [s1_reg PRES GR 18; reflexivity|].
    split; [s1_reg PRES GR 19; reflexivity|].
    split; [s1_reg PRES GR 23; reflexivity|].
    split; [exact A0'|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HKS|]. split; [lia|].
    split; [exact ELE|]. split; [exact ELZ|]. split; [exact BSE|].
    split; [exact RM|]. split; [exact INIT|]. split; [exact RO2|].
    split; [exact NZ|]. split; [exact AL16|]. split; [exact FRESH|].
    split; [exact BLK|].
    split.
    { destruct BLK as (b1 & b2 & BL1 & BL2).
      intros qq mm Hqq. rewrite BL2 in Hqq.
      assert (ND : List.NoDup (map fst (blocks L1 A1))).
      { first [exact (NDB L1 A1 m2 md1 MR2) | apply NoDup_ListNoDup; exact (NDB L1 A1 m2 md1 MR2)]. }
      rewrite BL1, map_app in ND. cbn [map fst] in ND. apply NoDup_remove_2 in ND.
      assert (NE : qq <> res).
      { intros ->. apply ND. rewrite <- map_app. exact (in_map fst _ (res, mm) Hqq). }
      split; [exact NE|].
      assert (I1 : In (qq, mm) (blocks L1 A1)).
      { rewrite BL1. apply in_or_app. destruct (in_app_or _ _ _ Hqq) as [X|X]; [left; exact X|right; right; exact X]. }
      assert (I2 : In (res, EL + 1) (blocks L1 A1)) by (rewrite BL1; apply in_or_app; right; left; reflexivity).
      destruct (blocks_disjoint B (API rc) L1 A1 m2 md1 qq mm res (EL + 1) MR2 I1 I2 NE) as [D|D];
        intros i Hi; lia. }
    exact (POST L1 A1 [SP 0 0] eq_refl RES').
Qed.
