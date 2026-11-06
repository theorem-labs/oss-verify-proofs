From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Exec Frame Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSlotPlan.
Import ListNotations.
Open Scope Z_scope.

Lemma getr_xregs : forall R R' r, xregs_eqv R R' -> PropExec.getr R r = PropExec.getr R' r.
Proof.
  intros R R' r H. unfold PropExec.getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply H. unfold is_x0. apply Z.eqb_neq. intro H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma rg_eqv : forall a b k, ms_eqv a b -> rg b k = rg a k.
Proof. intros a b k [HR _]. unfold rg. symmetry. apply getr_xregs. exact HR. Qed.

Lemma canon_MS : forall ms, ms_svc_pending ms = None ->
  canonical_register_state ms =
  MS (mkR_of (ms_regs ms)) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. unfold canonical_register_state, MS. rewrite H. reflexivity. Qed.

Lemma rg_canon : forall ms k, rg (canonical_register_state ms) k = rg ms k.
Proof. intros ms k. apply rg_eqv. apply canonical_register_state_eqv. Qed.

Definition eqv_inv (Q : machine_state -> Prop) : Prop := forall a b, ms_eqv a b -> Q a -> Q b.

Lemma evt_canon : forall (Q : machine_state -> Prop) ms,
  eqv_inv Q -> evt rsegs Q (canonical_register_state ms) -> evt rsegs Q ms.
Proof.
  intros Q ms HQ H. eapply evt_mono; [apply canonical_contract_transport; exact H|].
  intros ms' (c & Hc & He). exact (HQ c ms' He Hc).
Qed.

Ltac plan_unfold :=
  unfold At_entry, At_ret0, At_mallocT, At_mallocT_ret, At_set0, At_set, At_unset0, At_unset, At_admit,
    At_mallocSW1, At_mallocSW1_ret, At_freeSW1, At_raw, At_mallocSW2, At_mallocSW2_ret,
    At_freeSW2, At_freeSW2_ret, At_sched, At_freeT, kept in *;
  unfold at_after_admit in *;
  unfold body in *; unfold common, slots, cslot, cur, table, arrays, sregs in *.

Ltac eqv_inv_tac :=
  let a := fresh "a" in let b := fresh "b" in let He := fresh "He" in let Ha := fresh "Ha" in
  intros a b He Ha;
  pose proof (fun k => rg_eqv a b k He) as RG;
  destruct He as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro);
  plan_unfold;
  rewrite ?RG; rewrite <- ?HF, <- ?Hpc, <- ?Hsvc, <- ?Hrv, <- ?Hfc, <- ?Hm, <- ?Hro;
  exact Ha.

Lemma eqv_At_ret0 : forall x, eqv_inv (At_ret0 x). Proof. intros x. eqv_inv_tac. Qed.
Lemma eqv_At_mallocT : forall x, eqv_inv (At_mallocT x). Proof. intros x. eqv_inv_tac. Qed.
Lemma eqv_At_mallocT_ret : forall x t, eqv_inv (At_mallocT_ret x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_set0 : forall x t, eqv_inv (At_set0 x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_set : forall x t i, eqv_inv (At_set x t i). Proof. intros x t i. eqv_inv_tac. Qed.
Lemma eqv_At_unset0 : forall x t, eqv_inv (At_unset0 x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_unset : forall x t c, eqv_inv (At_unset x t c). Proof. intros x t c. eqv_inv_tac. Qed.
Lemma eqv_At_admit : forall x t, eqv_inv (At_admit x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_mallocSW1 : forall x t, eqv_inv (At_mallocSW1 x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_mallocSW1_ret : forall x t s, eqv_inv (At_mallocSW1_ret x t s). Proof. intros x t s. eqv_inv_tac. Qed.
Lemma eqv_At_freeSW1 : forall x t s, eqv_inv (At_freeSW1 x t s). Proof. intros x t s. eqv_inv_tac. Qed.
Lemma eqv_At_raw : forall x t pc, eqv_inv (At_raw x t pc). Proof. intros x t pc. eqv_inv_tac. Qed.
Lemma eqv_At_mallocSW2 : forall x t, eqv_inv (At_mallocSW2 x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_mallocSW2_ret : forall x t s, eqv_inv (At_mallocSW2_ret x t s). Proof. intros x t s. eqv_inv_tac. Qed.
Lemma eqv_At_freeSW2 : forall x t s, eqv_inv (At_freeSW2 x t s). Proof. intros x t s. eqv_inv_tac. Qed.
Lemma eqv_At_freeSW2_ret : forall x t, eqv_inv (At_freeSW2_ret x t). Proof. intros x t. eqv_inv_tac. Qed.
Lemma eqv_At_sched : forall x t i, eqv_inv (At_sched x t i). Proof. intros x t i. eqv_inv_tac. Qed.
Lemma eqv_At_freeT : forall x t, eqv_inv (At_freeT x t). Proof. intros x t. eqv_inv_tac. Qed.

Lemma eqv_kept : forall x W ms, eqv_inv (kept x W ms). Proof. intros x W ms. eqv_inv_tac. Qed.

Lemma eqv_and : forall P Q, eqv_inv P -> eqv_inv Q -> eqv_inv (fun ms => P ms /\ Q ms).
Proof. intros P Q HP HQ a b He [Ha Hb]. split; [exact (HP a b He Ha) | exact (HQ a b He Hb)]. Qed.

Lemma eqv_or : forall P Q, eqv_inv P -> eqv_inv Q -> eqv_inv (fun ms => P ms \/ Q ms).
Proof. intros P Q HP HQ a b He [Ha | Hb]; [left; exact (HP a b He Ha) | right; exact (HQ a b He Hb)]. Qed.

Lemma eqv_const : forall (A : Prop) P, eqv_inv P -> eqv_inv (fun ms => A /\ P ms).
Proof. intros A P HP a b He [Ha Hb]. split; [exact Ha | exact (HP a b He Hb)]. Qed.
