(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt Stdio Harness Adapter Driver PState Prog StepB TargetSafe
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PCaps LB_Hist LB_Proph LB_PStdio.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import Keeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).


Section TARGETP.
Variable P : Z -> Z.
Hypothesis HPc : forall c, P c <= Penv c.
Hypothesis HP8 : forall c, validc c = true -> AMBC <= P c.

Definition malok (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET /\ n <= NREQ.

Lemma malok_amb0 : forall n A, AMBZ A -> (length A <= 3)%nat -> 0 <= n <= 24 * 2^24 + 12 -> malok A n.
Proof.
  intros n A HA HL Hn.
  destruct (amb_counts A HA) as (A1 & A2 & A3). pose proof PHI_Penv as HPh. unfold RBIG in HPh. pose proof (PHI_mono P Penv HPc) as PM.
  assert (Hbb : bigb n <= 24 * 2^24 + 8192).
  { unfold bigb. destruct (_ <=? _); [|pose proof (bigb_nonneg n); lia]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
    pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  split; [| split; [unfold W in *; lia| unfold NREQ; lia]].
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (A1 (size_to_class n)). specialize (HP8 _ Vc). unfold AMBC in *. lia.
  - intros Hbig. specialize (HP8 63 validc_63). unfold AMBC in *. lia.
Qed.


Definition Q (X : list (bptr * Z)) : assn PState := QI X P.
Local Notation mspecL := (mspecL LBUDGET).

Lemma Q_minv X s mo : Q X s mo -> minv mo /\ m_halted mo = None. Proof. apply QI_minv. Qed.
Lemma Q_fds X s mo mo' : Q X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> Q X s mo'. Proof. apply QI_fds. Qed.
Lemma Q_live X s mo : Q X s mo -> live mo <= LBUDGET. Proof. apply QI_live. Qed.
Lemma Q_so X s mo v : Q X s mo -> Q X (set_so_ps v s) mo. Proof. apply QI_set_so. Qed.
Lemma Q_perm X Y s mo : Permutation X Y -> Q X s mo -> Q Y s mo. Proof. apply QI_perm. Qed.

Lemma malloc_Q : forall X n, 0 <= n ->
  mspecL (fun s mo => Q X s mo /\ malok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Q ((p, n) :: X) s mo /\ n < 2^63 | None => Q X s mo end).
Proof. intros X n Hn. unfold Q, malok. eapply mspecL_pre; [apply raw_malloc_LQ; exact Hn|]. intros s mo [H1 (H2 & H3 & H4)]. auto. Qed.

Lemma free_Q : forall X p n, mspecL (Q ((p, n) :: X)) (raw_free p) (fun _ => Q X).
Proof. intros X p n. unfold Q. apply raw_free_LQ. Qed.

Lemma emit_Q : forall X v, mspecL (Q X) (io_emit io v) (fun _ => Q X).
Proof. intros X v. cbn [io io_emit io_S]. apply (s_emit_L LBUDGET (Q X) (Q_live X) (Q_so X)). Qed.

Local Ltac ret_Q := apply mspecL_ret; intros ? ? HH; exact HH.


Lemma fuzz_one_Q : forall A data, mspecL (Q A) (Prog.fuzz_one data) (fun _ => Q A).
Proof. intros A data. unfold Prog.fuzz_one, Harness.fuzz_one. ret_Q. Qed.


Lemma run_calls_Q : forall A n payload rc,
  mspecL (Q A) (run_calls Prog.fuzz_one (io_emit io) n payload rc) (fun _ => Q A).
Proof.
  intros A n. induction n as [|n IH]; intros payload rc; cbn [run_calls]; [ret_Q|].
  eapply mspecL_seq; [apply fuzz_one_Q|]. intros rc'.
  eapply mspecL_seq; [apply emit_Q|]. intros _. apply IH.
Qed.

Lemma run_QP : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL (Q [(b, cap)]) (run cfg payload) (fun _ => Q [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp. unfold run, target_run.
  assert (HA1 : AMBZ [(b, cap)]) by (apply AMBZ_cons; [apply AMBZ_nil| cbn; lia| unfold MAX_INPUT in *; lia]).
  eapply mspecL_bind with (Q1 := fun a s mo => match a with
                                               | None => Q [(b, cap)] s mo
                                               | Some None => Q [(b, cap)] s mo
                                               | Some (Some p) => Q [(p, zlength payload); (b, cap)] s mo
                                               end).
  { apply mspecL_if; intros _; [ret_Q|].
    eapply mspecL_bind.
    - eapply mspecL_pre; [apply malloc_Q; unfold zlength; lia|]. intros s mo HQ. split; [exact HQ|].
      apply (malok_amb0 (zlength payload) [(b, cap)] HA1 ltac:(cbn; lia)). unfold MAX_INPUT, zlength in *. lia.
    - intros [p|]; apply mspecL_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecL_seq; [apply run_calls_Q|]. intros rc.
    eapply mspecL_seq; [apply free_Q|]. intros _. ret_Q.
  - eapply mspecL_seq; [apply run_calls_Q|]. intros rc. eapply mspecL_seq; [ret_Q|]. intros _. ret_Q.
  - ret_Q.
Qed.
End TARGETP.


Definition Qamb (X : list (bptr * Z)) : assn PState := QI X Pamb.
Definition Qrun (X : list (bptr * Z)) : assn PState := fun s mo =>
  exists P, (forall c, P c <= Penv c) /\ (forall c, validc c = true -> AMBC <= P c) /\ QI X P s mo.

Lemma Qamb_Qrun X s mo : Qamb X s mo -> Qrun X s mo.
Proof. intros H. exists Pamb. split; [exact Pamb_le_Penv|]. split; [exact Pamb_amb| exact H]. Qed.

Lemma Qamb_minv X s mo : Qamb X s mo -> minv mo /\ m_halted mo = None. Proof. apply QI_minv. Qed.
Lemma Qamb_fds X s mo mo' : Qamb X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> Qamb X s mo'. Proof. apply QI_fds. Qed.
Lemma Qamb_live X s mo : Qamb X s mo -> live mo <= LBUDGET. Proof. apply QI_live. Qed.
Lemma Qamb_so X s mo v : Qamb X s mo -> Qamb X (set_so_ps v s) mo. Proof. apply QI_set_so. Qed.
Lemma Qamb_perm X Y s mo : Permutation X Y -> Qamb X s mo -> Qamb Y s mo. Proof. apply QI_perm. Qed.
Lemma Qrun_minv X s mo : Qrun X s mo -> minv mo /\ m_halted mo = None. Proof. intros (P & _ & _ & H). eapply QI_minv. exact H. Qed.
Lemma Qrun_fds X s mo mo' : Qrun X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> Qrun X s mo'.
Proof. intros (P & H1 & H2 & H) E M N. exists P. split; [exact H1|]. split; [exact H2|]. eapply QI_fds; eauto. Qed.
Lemma Qrun_live X s mo : Qrun X s mo -> live mo <= LBUDGET. Proof. intros (P & _ & _ & H). eapply QI_live. exact H. Qed.
Lemma Qrun_so X s mo v : Qrun X s mo -> Qrun X (set_so_ps v s) mo.
Proof. intros (P & H1 & H2 & H). exists P. split; [exact H1|]. split; [exact H2|]. apply QI_set_so. exact H. Qed.

Definition malokA (X : list (bptr * Z)) (n : Z) : Prop :=
  forall P, (forall c, P c <= Penv c) -> (forall c, validc c = true -> AMBC <= P c) -> malok P X n.

Lemma malokA_amb0 : forall n A, AMBZ A -> (length A <= 3)%nat -> 0 <= n <= 24 * 2^24 + 12 -> malokA A n.
Proof. intros n A HA HL Hn P HPc HP8. apply (malok_amb0 P HPc HP8 n A HA HL Hn). Qed.

Lemma malloc_Qamb : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => Qamb X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Qamb ((p, n) :: X) s mo /\ n < 2^63 | None => Qamb X s mo end).
Proof. intros X n Hn. eapply mspecL_pre; [apply (malloc_Q Pamb n X Hn) || apply (malloc_Q Pamb X n Hn)|]. intros s mo [HQ HM]. split; [exact HQ|]. apply HM; [exact Pamb_le_Penv| exact Pamb_amb]. Qed.

Lemma free_Qamb : forall X p n, mspecL LBUDGET (Qamb ((p, n) :: X)) (raw_free p) (fun _ => Qamb X).
Proof. intros. unfold Qamb. apply raw_free_LQ. Qed.

Lemma free_Qrun : forall X p n, mspecL LBUDGET (Qrun ((p, n) :: X)) (raw_free p) (fun _ => Qrun X).
Proof.
  intros X p n s mo (P & H1 & H2 & H). eapply etwl_mono; [apply (raw_free_LQ X P p n s mo H)|].
  intros [u s'] mo' HQ. cbn in HQ |- *. exists P. auto.
Qed.

Theorem run_Q : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL LBUDGET (Qamb [(b, cap)]) (run cfg payload) (fun _ => Qrun [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp s mo HQ.
  eapply etwl_mono; [apply (run_QP Pamb Pamb_le_Penv Pamb_amb b cap cfg payload Hcap Hp s mo HQ)|].
  intros [u s'] mo' H. cbn in H |- *. exists Pamb. split; [exact Pamb_le_Penv|]. split; [exact Pamb_amb| exact H].
Qed.
