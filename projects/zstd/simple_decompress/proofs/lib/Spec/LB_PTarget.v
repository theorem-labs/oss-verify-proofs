(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt Stdio Harness Adapter Driver PState Prog StepB TargetSafe
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PCaps LB_Hist LB_PAmb LB_PStdio.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import Keeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TARGETP.
Variable P : Z -> Z.
Hypothesis HPc : forall c, P c <= Pamb c.   (* [comment removed for export] *)
Hypothesis HP8 : forall c, validc c = true -> AMBC <= P c.

(* [comment removed for export] *)
Definition malok (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET /\ n <= NREQ.

(* [comment removed for export] *)
Lemma malok_amb0 : forall n A, AMBZ A -> (length A <= 3)%nat -> 0 <= n <= 24 * 2^24 + 12 -> malok A n.
Proof.
  intros n A HA HL Hn.
  destruct (amb_counts A HA) as (A1 & A2 & A3). pose proof PHI_Pamb_eq as HPh. pose proof (PHI_mono P Pamb HPc) as PM.
  assert (Hbb : bigb n <= 24 * 2^24 + 8192).
  { unfold bigb. destruct (_ <=? _); [|pose proof (bigb_nonneg n); lia]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
    pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  split; [| split; [unfold LBUDGET in *; lia| unfold NREQ; lia]].   (* [comment removed for export] *)
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (A1 (size_to_class n)). specialize (HP8 _ Vc). unfold AMBC in *. lia.
  - intros Hbig. specialize (HP8 63 validc_63). unfold AMBC in *. lia.
Qed.

(* [comment removed for export] *)
Definition AMB4 (Z0 : list (bptr * Z)) : Prop := (length Z0 <= 4)%nat /\ Forall (fun b => 0 <= snd b <= 2^26 + 64) Z0.

Lemma amb4_counts : forall Z0, AMB4 Z0 -> (forall c, LRX Z0 c <= 4) /\ n63X Z0 <= 4 /\ R63X Z0 <= 4 * (2^26 + 8192).
Proof.
  intros Z0 [Hl HF].
  assert (G : forall Z1, Forall (fun b => 0 <= snd b <= 2^26 + 64) Z1 -> (forall c, LRX Z1 c <= Z.of_nat (length Z1)) /\ n63X Z1 <= Z.of_nat (length Z1) /\ R63X Z1 <= Z.of_nat (length Z1) * (2^26 + 8192)).
  { induction Z1 as [|[p n] Z1 IH]; intros HF1.
    - unfold LRX, n63X, R63X, zcount, zlen. cbn. splits; intros; lia.
    - apply Forall_cons_iff in HF1 as [Hn HF1]. cbn [snd] in Hn. destruct (IH HF1) as (A1 & A2 & A3). cbn [length]. rewrite Nat2Z.inj_succ.
      splits.
      + intros c. rewrite LRX_cons. specialize (A1 c). destruct (_ && _); lia.
      + rewrite n63X_cons. destruct (_ <=? _); lia.
      + rewrite R63X_cons. assert (bigb n <= 2^26 + 8192); [|lia]. unfold bigb. destruct (_ <=? _); [|lia].
        rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
        pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  destruct (G Z0 HF) as (A1 & A2 & A3). splits; [intros c; specialize (A1 c); lia| lia| nia].
Qed.

Lemma AMB4_of_AMBZ p n A : AMBZ A -> 0 <= n <= 2^26 + 64 -> AMB4 ((p, n) :: A).
Proof. intros [Hl HF] Hn. split; [cbn [length]; lia| constructor; [exact Hn| exact HF]]. Qed.

Lemma malok_big4 : forall n A, AMB4 A -> 0 <= n <= NREQ -> malok A n.
Proof.
  intros n A HA Hn.
  destruct (amb4_counts A HA) as (A1 & A2 & A3). pose proof PHI_Pamb_eq as HPh. pose proof (PHI_mono P Pamb HPc) as PM.
  assert (Hbb : bigb n <= NREQ + 8192).
  { unfold bigb. destruct (_ <=? _); [|unfold NREQ; lia]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
    pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  split; [| split; [unfold NREQ, LBUDGET in *; lia| lia]].
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (A1 (size_to_class n)). specialize (HP8 _ Vc). unfold AMBC in *. lia.
  - intros Hbig. specialize (HP8 63 validc_63). unfold AMBC in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bp0 : bptr := ((0%N, 0), 0).
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

Lemma new_handler_Q : forall X (R : Empty_set -> assn PState), mspecL (Q X) new_handler R.
Proof. intros X R. unfold new_handler. apply mspecL_munr. Qed.

Lemma emit_Q : forall X v, mspecL (Q X) (io_emit io v) (fun _ => Q X).
Proof. intros X v. cbn [io io_emit io_S]. apply (s_emit_L LBUDGET (Q X) (Q_live X) (Q_so X)). Qed.

Local Ltac ret_Q := apply mspecL_ret; intros ? ? HH; exact HH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition olistQ (o : option bptr) (n : Z) : list (bptr * Z) := match o with Some p => [(p, n)] | None => [] end.

Lemma fuzz_malloc_Q : forall X n,
  mspecL (fun s mo => Q X s mo /\ (0 < n -> malok X n)) (fuzz_malloc raw_malloc new_handler n)
         (fun r => Q (olistQ r n ++ X)).
Proof.
  intros X n. unfold fuzz_malloc.
  apply mspecL_if; intros C.
  - apply Z.ltb_lt in C.
    eapply mspecL_bind.
    + eapply mspecL_pre; [apply malloc_Q; lia|]. intros s mo [HQ HM]. split; [exact HQ| exact (HM C)].
    + intros [p|]; cbn beta iota.
      * apply mspecL_pure. intros _. ret_Q.
      * eapply mspecL_bind; [apply (new_handler_Q X (fun _ _ _ => False))|]. intros [].
  - apply mspecL_ret. intros s mo [HQ _]. exact HQ.
Qed.

Lemma free_opt_Q : forall X o n,
  mspecL (Q (olistQ o n ++ X)) (free_opt raw_free o) (fun _ => Q X).
Proof. intros X [p|] n; cbn [free_opt olistQ app]; [apply free_Q| ret_Q]. Qed.

Lemma AMBZ_olistQ : forall o n A, AMBZ A -> (length A <= 2)%nat -> 0 <= n <= 2^26 + 64 -> AMBZ (olistQ o n ++ A).
Proof. intros [p|] n A HA HL Hn; cbn [olistQ app]; [apply AMBZ_cons; assumption| exact HA]. Qed.

Lemma length_olistQ : forall o n (A : list (bptr * Z)), (length (olistQ o n ++ A) <= S (length A))%nat.
Proof. intros [p|] n A; cbn [olistQ app length]; lia. Qed.

Lemma AMB4_olistQ : forall o n A, AMBZ A -> 0 <= n <= 2^26 + 64 -> AMB4 (olistQ o n ++ A).
Proof.
  intros [p|] n A HA Hn; cbn [olistQ app]; [apply AMB4_of_AMBZ; assumption|].
  destruct HA as [Hl HF]. split; [lia| exact HF].
Qed.

Lemma fuzz_one_Q : forall A data, AMBZ A -> (length A <= 2)%nat -> zlength data <= MAX_INPUT ->
  mspecL (Q A) (Prog.fuzz_one data) (fun _ => Q A).
Proof.
  intros A data HA HL Hlen. unfold Prog.fuzz_one, Harness.fuzz_one.
  pose proof (buff_size_range data ltac:(unfold MAX_INPUT in Hlen; lia)) as Hb. unfold BUFF_MAX in Hb.
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    apply (malok_amb0 PRODUCER_SIZE A HA ltac:(lia)). unfold PRODUCER_SIZE. lia. }
  intros producer.
  pose proof (AMBZ_olistQ producer PRODUCER_SIZE A HA HL ltac:(unfold PRODUCER_SIZE; lia)) as HA1.
  pose proof (length_olistQ producer PRODUCER_SIZE A) as HL1.
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    apply (malok_amb0 DCTX_SIZE _ HA1 ltac:(lia)). unfold DCTX_SIZE. lia. }
  intros dctx.
  pose proof (AMB4_olistQ dctx DCTX_SIZE _ HA1 ltac:(unfold DCTX_SIZE; lia)) as HA2.
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    apply (malok_big4 (buff_size data) _ HA2). unfold NREQ. lia. }
  intros rbuf.
  eapply mspecL_seq; [apply free_opt_Q|]. intros _.
  eapply mspecL_seq.
  { eapply mspecL_pre; [apply (free_opt_Q (olistQ dctx DCTX_SIZE ++ A) producer PRODUCER_SIZE)|].
    intros s mo H. eapply Q_perm; [|exact H]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  intros _.
  eapply mspecL_seq; [apply free_opt_Q|]. intros _.
  ret_Q.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_Q : forall A n payload rc, AMBZ A -> (length A <= 2)%nat -> zlength payload <= MAX_INPUT ->
  mspecL (Q A) (run_calls Prog.fuzz_one (io_emit io) n payload rc) (fun _ => Q A).
Proof.
  intros A n. induction n as [|n IH]; intros payload rc HA HL Hp; cbn [run_calls]; [ret_Q|].
  eapply mspecL_seq; [apply fuzz_one_Q; assumption|]. intros rc'.
  eapply mspecL_seq; [apply emit_Q|]. intros _. apply IH; assumption.
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
  - eapply mspecL_seq; [apply run_calls_Q; [apply AMBZ_cons; [exact HA1| cbn; lia| unfold MAX_INPUT, zlength in *; lia]| cbn; lia| exact Hp]|]. intros rc.
    eapply mspecL_seq; [apply free_Q|]. intros _. ret_Q.
  - eapply mspecL_seq; [apply run_calls_Q; [exact HA1| cbn; lia| exact Hp]|]. intros rc. eapply mspecL_seq; [ret_Q|]. intros _. ret_Q.
  - ret_Q.
Qed.
End TARGETP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Qamb (X : list (bptr * Z)) : assn PState := QI X Pamb.
Definition Qrun (X : list (bptr * Z)) : assn PState := fun s mo =>
  exists P, (forall c, P c <= Pamb c) /\ (forall c, validc c = true -> AMBC <= P c) /\ QI X P s mo.

Lemma Qamb_Qrun X s mo : Qamb X s mo -> Qrun X s mo.
Proof. intros H. exists Pamb. split; [intros c; apply Z.le_refl|]. split; [exact Pamb_amb| exact H]. Qed.

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

(* [comment removed for export] *)
Definition malokA (X : list (bptr * Z)) (n : Z) : Prop :=
  forall P, (forall c, P c <= Pamb c) -> (forall c, validc c = true -> AMBC <= P c) -> malok P X n.

Lemma malokA_amb0 : forall n A, AMBZ A -> (length A <= 3)%nat -> 0 <= n <= 24 * 2^24 + 12 -> malokA A n.
Proof. intros n A HA HL Hn P HPc HP8. apply (malok_amb0 P HPc HP8 n A HA HL Hn). Qed.

Lemma malloc_Qamb : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => Qamb X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Qamb ((p, n) :: X) s mo /\ n < 2^63 | None => Qamb X s mo end).
Proof. intros X n Hn. eapply mspecL_pre; [apply (malloc_Q Pamb n X Hn) || apply (malloc_Q Pamb X n Hn)|]. intros s mo [HQ HM]. split; [exact HQ|]. apply HM; [intros c; apply Z.le_refl| exact Pamb_amb]. Qed.

Lemma free_Qamb : forall X p n, mspecL LBUDGET (Qamb ((p, n) :: X)) (raw_free p) (fun _ => Qamb X).
Proof. intros. unfold Qamb. apply raw_free_LQ. Qed.

Lemma free_Qrun : forall X p n, mspecL LBUDGET (Qrun ((p, n) :: X)) (raw_free p) (fun _ => Qrun X).
Proof.
  intros X p n s mo (P & H1 & H2 & H). eapply etwl_mono; [apply (raw_free_LQ X P p n s mo H)|].
  intros [u s'] mo' HQ. cbn in HQ |- *. exists P. auto.
Qed.

(* [comment removed for export] *)
Theorem run_Q : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL LBUDGET (Qamb [(b, cap)]) (run cfg payload) (fun _ => Qrun [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp s mo HQ.
  eapply etwl_mono; [apply (run_QP Pamb (fun c => Z.le_refl _) Pamb_amb b cap cfg payload Hcap Hp s mo HQ)|].
  intros [u s'] mo' H. cbn in H |- *. apply Qamb_Qrun. exact H.
Qed.
