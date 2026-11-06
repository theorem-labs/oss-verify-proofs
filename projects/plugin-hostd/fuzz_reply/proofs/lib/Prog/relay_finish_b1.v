From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  send_line_c gesture_end_c relay_event_c RelayFrame send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c
  RelayRep relay_finish_b_c KindB relay_finish_seg relay_finish_aux.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fi_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fi_rsame : forall m m' m0, ro_agree rsegs m -> mem_rel rsegs m' m0 -> m0 = normalize rsegs m ->
  ro_same rsegs m m' -> munch [] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m'.
Proof.
  intros m m' m0 RA MR -> RS.
  exact (fi_back m _ m' [] RA MR RS (munch_refl _ _) (wmono_refl _ _)).
Qed.

Lemma fi_rw0 : forall m m' A cs, rw_cells rsegs m A cs -> munch [] m m' -> wmono rsegs m m' -> rw_cells rsegs m' A cs.
Proof. intros m m' A cs H MU WM. exact (rw_cells_transport rsegs [] m m' A cs H MU WM I). Qed.

Lemma fi_by0 : forall m m' A bs, bytes_at rsegs m A bs -> munch [] m m' -> bytes_at rsegs m' A bs.
Proof. intros m m' A bs H MU. exact (bytes_at_transport rsegs [] m m' A bs H MU I). Qed.

Lemma fi_mb0 : forall m m' a, munch [] m m' -> 0 <= a < 2 ^ 64 -> YP09.mbyte rsegs m' a = YP09.mbyte rsegs m a.
Proof. intros m m' a MU Ha. exact (munch_mbyte rsegs [] m m' a MU Ha I). Qed.

Lemma fi_kst_tr0 : forall L A m m' e, fi_kst L A m e -> munch [] m m' -> fi_kst L A m' e.
Proof.
  intros L A m m' e [KH KS] MU. split.
  - intros H. destruct (KH H) as [I1 B1]. split; [exact I1 | exact (fi_by0 _ _ _ _ B1 MU)].
  - eapply Forall_impl; [|exact KS]. intros k [I1 B1]. split; [exact I1 | exact (fi_by0 _ _ _ _ B1 MU)].
Qed.

Lemma fi_est_tr0 : forall L A m m' l, Forall (fi_est L A m) l -> munch [] m m' -> Forall (fi_est L A m') l.
Proof.
  intros L A m m' l H MU. eapply Forall_impl; [|exact H]. intros e [B K].
  split; [exact B | exact (fi_kst_tr0 _ _ _ _ _ K MU)].
Qed.

Lemma fi_K : RELAY_FINISH_K = 8464.
Proof. reflexivity. Qed.

Lemma fi_GK : GESTURES_END_K = 8400.
Proof. reflexivity. Qed.

Lemma fi_ro_glob : forall a, 200640 <= a < 200768 -> ro_addr rsegs (wa a) = false.
Proof. intros a Ha. replace a with (200640 + (a - 200640)) by lia. apply fi_ro_g1. lia. Qed.

Lemma fi_ro_lis : forall a, 134456 <= a < 134464 -> ro_addr rsegs (wa a) = false.
Proof. intros a Ha. replace a with (134456 + (a - 134456)) by lia. apply fi_ro_g2. lia. Qed.

Lemma fi_ra1 : YK0s.ret_ok (Z_to_bv 64 77980).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fi_ra2 : YK0s.ret_ok (Z_to_bv 64 77992).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fi_tr_cells : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) -> outside W (A + j)) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs H MU WM HO. pose proof H as [_ (H0 & H1 & _)].
  apply (fi_rw_tr m m' A cs H). intros j Hj. split.
  - exact (munch_mbyte rsegs W m m' (A + j) MU ltac:(lia) (HO j Hj)).
  - intros Hw. exact (WM _ Hw).
Qed.

Lemma fi_tr_bytes : forall W m m' A bs, bytes_at rsegs m A bs -> munch W m m' ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> outside W (A + j)) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs H MU HO. pose proof H as (H0 & H1 & _).
  apply (bytes_at_transfer rsegs m m' A bs H). intros j Hj.
  exact (munch_mbyte rsegs W m m' (A + j) MU ltac:(lia) (HO j Hj)).
Qed.

Lemma fi_wr_hi : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> YP09.writable_at rsegs m a ->
  wview rsegs m (wa a) <> None /\ exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha W. split; [exact W|].
  destruct (writable_hi_present m a Ha W) as [b E]. exists b. unfold mrd, wa. rewrite E. reflexivity.
Qed.

Section Regs.
Context {fx : YK11.FPState}.

Lemma fi_bridge : forall R pc m md (Q : machine_state -> Prop) (P : config -> Prop),
  ro_agree rsegs m -> m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of R) fp_regs pc fp_csr None (normalize rsegs m) (seg_rom rsegs)) ->
  (forall s0 R' m', Q s0 -> Regs6ss.xregs_eqv (ms_regs s0) R' -> mem_rel rsegs m' (ms_mem s0) -> ro_same rsegs m m' ->
     SR rsegs (mkCfg {| ms_regs := R'; ms_fregs := ms_fregs s0; ms_pc_val := ms_pc_val s0;
       ms_svc_pending := ms_svc_pending s0; ms_resv := ms_resv s0; ms_fcsr := ms_fcsr s0; ms_mem := m';
       ms_rom := ms_rom s0 |} md) P) ->
  SR rsegs (mkCfg (YK11.mkst R pc m (seg_rom rsegs)) md) P.
Proof.
  intros R pc m md Q P HRA Hh Hl HE K.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite fi_canon. eapply evt_normalize; [exact fi_wx | exact HRA | exact HE]. }
  intros ms' PK. destruct (fi_unpack _ _ _ PK) as (s0 & R' & m' & HQ & -> & X & MRl & RS).
  exact (K s0 R' m' HQ X MRl RS).
Qed.

Lemma fi_kA0 : forall R pc m md (Q : machine_state -> Prop) (P : config -> Prop),
  ro_agree rsegs m -> m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of R) fp_regs pc fp_csr None (normalize rsegs m) (seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R0 pc0, s0 = MS R0 fp_regs pc0 fp_csr None (normalize rsegs m) (seg_rom rsegs)) ->
  (forall R0 pc0 R' m', Q (MS R0 fp_regs pc0 fp_csr None (normalize rsegs m) (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R0 R' -> munch [] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     SR rsegs (mkCfg (YK11.mkst R' pc0 m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (YK11.mkst R pc m (seg_rom rsegs)) md) P.
Proof using.
  intros R pc m md Q P HRA Hh Hl HE SH K.
  eapply fi_bridge; [exact HRA | exact Hh | exact Hl | exact HE |].
  intros s0 R' m' HQ X MRl RS.
  destruct (SH s0 HQ) as (R0 & pc0 & ->).
  destruct (fi_rsame m m' _ HRA MRl eq_refl RS) as (MU & WM & RA').
  exact (K R0 pc0 R' m' HQ X MU WM RA').
Qed.

End Regs.

Section RP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis SEGS : ms_segs Bm = rsegs.

Lemma fi_rp_keep2 : forall K E F L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k,
  relay_post Bm API K E F L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  In (q, k) (blocks L1 A1) -> 0 < k -> ~ F q ->
  In (q, k) (blocks L2 A2) /\
  (forall j, 0 <= j < k -> ~ E (q + j) -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j)).
Proof using SEGS.
  intros K E F L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k RP Hq Hk NF.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  destruct (proj1 (fi_blocks_in _ _ _ _) Hq) as (p & Ep & Hp).
  assert (NF' : ~ F (ptr_addr L1 p)) by (rewrite Ep; exact NF).
  pose proof (SV2 p k Hp Hk NF') as Hp2.
  pose proof (AD2 p k Hp Hp2 NF') as E2.
  split.
  { apply fi_blocks_in. exists p. split; [congruence | exact Hp2]. }
  intros j Hj NE. rewrite <- Ep, <- SEGS. apply (BY2 p k j Hp Hp2 NF' Hj). rewrite Ep. exact NE.
Qed.

End RP.
