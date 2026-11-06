From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSlotPlan SlotBridge SegSetModel.
Import ListNotations.
Open Scope Z_scope.

Definition jal_post (s0 : machine_state) (tgt ret : Z) (a0 : word) (s1 : machine_state) : Prop :=
  ms_pc_val s1 = w64 tgt /\ rg s1 1 = w64 ret /\
  rg s1 2 = rg s0 2 /\ rg s1 3 = rg s0 3 /\ rg s1 4 = rg s0 4 /\ rg s1 8 = rg s0 8 /\ rg s1 9 = rg s0 9 /\
  rg s1 10 = a0 /\ rg s1 18 = rg s0 18 /\ rg s1 19 = rg s0 19 /\ rg s1 20 = rg s0 20 /\
  rg s1 21 = rg s0 21 /\ rg s1 22 = rg s0 22 /\ rg s1 23 = rg s0 23 /\ rg s1 24 = rg s0 24 /\
  rg s1 25 = rg s0 25 /\ rg s1 26 = rg s0 26 /\ rg s1 27 = rg s0 27 /\
  ms_fregs s1 = ms_fregs s0 /\ ms_fcsr s1 = ms_fcsr s0 /\ ms_resv s1 = None /\ ms_svc_pending s1 = None /\
  ms_rom s1 = ms_rom s0 /\ ms_mem s1 = ms_mem s0.

Lemma jal_post_inv : forall s0 tgt ret a0, eqv_inv (jal_post s0 tgt ret a0).
Proof.
  intros s0 tgt ret a0 a b He Ha. pose proof (fun k => rg_eqv a b k He) as RG.
  destruct He as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro). unfold jal_post in *. rewrite !RG.
  rewrite <- HF, <- Hpc, <- Hsvc, <- Hrv, <- Hfc, <- Hm, <- Hro. exact Ha.
Qed.

Ltac jal_tac := 
  intros s0 Hpc Hsvc Hrv; apply evt_canon; [apply jal_post_inv|];
  rewrite canon_rg by exact Hsvc; rewrite Hpc; unfold w64;
  repeat (zstep; try (apply evt_done; unfold jal_post;
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS];
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try exact Hrv;
    rg_eval; reflexivity)).

Lemma jal_at_mallocT : forall s0, ms_pc_val s0 = w64 PC_MALLOC_T -> ms_svc_pending s0 = None -> ms_resv s0 = None ->
  evt rsegs (jal_post s0 MALLOC_PC PC_MALLOC_T_RET (rg s0 10)) s0.
Proof. jal_tac. Qed.

Lemma jal_at_mallocSW1 : forall s0, ms_pc_val s0 = w64 PC_MALLOC_SW1 -> ms_svc_pending s0 = None -> ms_resv s0 = None ->
  evt rsegs (jal_post s0 MALLOC_PC PC_MALLOC_SW1_RET (rg s0 10)) s0.
Proof. jal_tac. Qed.

Lemma jal_at_mallocSW2 : forall s0, ms_pc_val s0 = w64 PC_MALLOC_SW2 -> ms_svc_pending s0 = None -> ms_resv s0 = None ->
  evt rsegs (jal_post s0 MALLOC_PC PC_MALLOC_SW2_RET (rg s0 10)) s0.
Proof. jal_tac. Qed.

Lemma jal_at_freeSW1 : forall s0, ms_pc_val s0 = w64 PC_FREE_SW1 -> ms_svc_pending s0 = None -> ms_resv s0 = None ->
  evt rsegs (jal_post s0 FREE_PC PC_FREE_SW1_RET (rg s0 10)) s0.
Proof. jal_tac. Qed.

Lemma jal_at_freeSW2 : forall s0, ms_pc_val s0 = w64 PC_FREE_SW2 -> ms_svc_pending s0 = None -> ms_resv s0 = None ->
  evt rsegs (jal_post s0 FREE_PC PC_FREE_SW2_RET (rg s0 10)) s0.
Proof. jal_tac. Qed.

Lemma jal_at_freeT : forall s0, ms_pc_val s0 = w64 0x13cc8 -> ms_svc_pending s0 = None -> ms_resv s0 = None ->
  evt rsegs (jal_post s0 FREE_PC PC_FREE_T_RET (rg s0 8)) s0.
Proof. jal_tac. Qed.
