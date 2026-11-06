(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad MSafe STree Malloc KStep MI_Inv MI_Cnt Stdio HarnessM Adapter Driver PState ProgP StepB
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PCaps LB_Hist LB_Amb LB_PStdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Keeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Local Notation mspecL := (mspecL LBUDGET).
Local Ltac ret_Q := apply mspecL_ret; intros ? ? HH; exact HH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_step_keeps_fa : forall atop e, keeps ps_fa (ev_step atop e).
Proof.
  intros atop e. destruct e; cbn [ev_step]; try apply keeps_unr.
  - destruct (_ =? 0); keeps_tac.
  - destruct (negb _); [keeps_tac|]. destruct (_ =? 0); keeps_tac.
  - keeps_tac.
  - keeps_tac.
Qed.

Lemma membed_keeps_fa : forall {R} atop (t : stree ev Z R), keeps ps_fa (membed atop t).
Proof.
  intros R atop t. induction t as [r|e k IH]; cbn [membed]; [apply keeps_ret|].
  apply keeps_bind; [apply ev_step_keeps_fa| exact IH].
Qed.

Lemma raw_malloc_keeps_fa : forall n, keeps ps_fa (raw_malloc n).
Proof.
  intros n. unfold raw_malloc. apply keeps_getk. intros s0. apply keeps_bind; [apply membed_keeps_fa|].
  intros [st' p]. keeps_tac.
Qed.

Lemma raw_free_keeps_fa : forall p, keeps ps_fa (raw_free p).
Proof.
  intros p. unfold raw_free. apply keeps_getk. intros s0. apply keeps_bind; [apply membed_keeps_fa|].
  intros st'. keeps_tac.
Qed.

(* [comment removed for export] *)
Lemma twl_tall : forall {A} B (t : itree node (exc A)) mo (Qm : A -> Model -> Prop) (Phi : A -> Prop),
  etwl B t mo Qm -> tall Phi t -> etwl B t mo (fun a mo' => Qm a mo' /\ Phi a).
Proof.
  intros A B t. induction t as [r|n k IH]; intros mo Qm Phi He Ht.
  - destruct r as [a|]; cbn in *; auto.
  - cbn -[NF] in *. destruct He as [HN He]. split; [exact HN|]. intros rsp mo' evs Hst. destruct (He rsp mo' evs Hst) as [HB He']. split; [exact HB|]. apply IH; [exact He'| apply Ht].
Qed.

Lemma mspecL_tall {A} (P0 : assn PState) (m : Monad.M PState A) (R : A -> assn PState) (Phi : A * PState -> Prop) :
  mspecL P0 m R -> (forall s, tall Phi (m s)) -> mspecL P0 m (fun a s mo => R a s mo /\ Phi (a, s)).
Proof.
  intros Hm Ht s mo HP. eapply etwl_mono; [apply (twl_tall LBUDGET (m s) mo _ Phi (Hm s mo HP) (Ht s))|]. intros [a s'] mo' [H1 H2]. cbn. auto.
Qed.

(* [comment removed for export] *)
Lemma mspecL_keeps_fa {A} (c : option bptr) (P0 : assn PState) (m : Monad.M PState A) (R : A -> assn PState) :
  mspecL P0 m R -> keeps ps_fa m ->
  mspecL (fun s mo => P0 s mo /\ ps_fa s = c) m (fun a s mo => R a s mo /\ ps_fa s = c).
Proof.
  intros Hm Hk s mo [HP Hc].
  eapply etwl_mono; [apply (twl_tall LBUDGET (m s) mo _ (fun p => ps_fa (snd p) = ps_fa s) (Hm s mo HP) (Hk s))|].
  intros [a s'] mo' [H1 H2]. cbn in *. split; [exact H1| congruence].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition clbQ (c : option bptr) : list (bptr * Z) := match c with Some p => [(p, CLIENT_VEC_BYTES)] | None => [] end.

Definition QambC (c : option bptr) (X : list (bptr * Z)) : assn PState := fun s mo => QI (clbQ c ++ X) Pamb s mo /\ ps_fa s = c.
Definition Qamb (X : list (bptr * Z)) : assn PState := fun s mo => exists c, QambC c X s mo.

Lemma Qamb_minv X s mo : Qamb X s mo -> minv mo /\ m_halted mo = None. Proof. intros (c & H & _). eapply QI_minv; exact H. Qed.
Lemma Qamb_fds X s mo mo' : Qamb X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> Qamb X s mo'.
Proof. intros (c & H & E) A B C. exists c. split; [eapply QI_fds; eauto| exact E]. Qed.
Lemma Qamb_live X s mo : Qamb X s mo -> live mo <= LBUDGET. Proof. intros (c & H & _). eapply QI_live; exact H. Qed.
Lemma Qamb_so X s mo v : Qamb X s mo -> Qamb X (set_so_ps v s) mo.
Proof. intros (c & H & E). exists c. split; [apply QI_set_so; exact H| exact E]. Qed.
Lemma Qamb_perm X Y s mo : Permutation X Y -> Qamb X s mo -> Qamb Y s mo.
Proof. intros HP (c & H & E). exists c. split; [eapply QI_perm; [apply Permutation_app_head; exact HP| exact H]| exact E]. Qed.

(* [comment removed for export] *)
Definition malok (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X Pamb n /\ PHI Pamb + R63X X + bigb n <= LBUDGET /\ n <= NREQ.
Definition malokA (X : list (bptr * Z)) (n : Z) : Prop := forall c, malok (clbQ c ++ X) n.

(* [comment removed for export] *)
Definition AMBK (k : nat) (Z0 : list (bptr * Z)) : Prop := (length Z0 <= k)%nat /\ Forall (fun b => 0 <= snd b <= 2^26 + 64) Z0.

Lemma AMBK_counts : forall k Z0, AMBK k Z0 ->
  (forall c, LRX Z0 c <= Z.of_nat k) /\ n63X Z0 <= Z.of_nat k /\ R63X Z0 <= Z.of_nat k * (2^26 + 8192).
Proof.
  intros k Z0 [Hl HF].
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
  destruct (G Z0 HF) as (A1 & A2 & A3). assert (Hk : Z.of_nat (length Z0) <= Z.of_nat k) by lia.
  splits; [intros c; specialize (A1 c); lia| lia| nia].
Qed.

Lemma AMBK_nil k : AMBK k []. Proof. split; [cbn; lia| constructor]. Qed.
Lemma AMBK_cons k p n Z0 : AMBK k Z0 -> 0 <= n <= 2^26 + 64 -> AMBK (S k) ((p, n) :: Z0).
Proof. intros [Hl HF] Hn. split; [cbn; lia| constructor; [exact Hn| exact HF]]. Qed.
Lemma AMBK_mono k k' Z0 : (k <= k')%nat -> AMBK k Z0 -> AMBK k' Z0.
Proof. intros Hk [Hl HF]. split; [lia| exact HF]. Qed.

(* [comment removed for export] *)
Lemma PHI_Pamb_le : PHI Pamb <= 2^28.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Lemma malok_ambK : forall n A, AMBK 5 A -> 0 <= n <= 2^26 + 64 -> malok A n.
Proof.
  intros n A HA Hn.
  destruct (AMBK_counts 5 A HA) as (A1 & A2 & A3). change (Z.of_nat 5) with 5 in A1, A2, A3. pose proof PHI_Pamb_le as PM.
  assert (Hbb : bigb n <= 2^26 + 8192).
  { unfold bigb. destruct (_ <=? _); [|pose proof (bigb_nonneg n); lia]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
    pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  split; [| split; [unfold LBUDGET; lia| unfold NREQ; lia]].
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (A1 (size_to_class n)). pose proof (Pamb_amb _ Vc). unfold AMBC in *. lia.
  - intros Hbig. pose proof (Pamb_amb 63 validc_63). unfold AMBC in *. lia.
Qed.

Lemma AMBK_clbQ : forall c A, AMBK 4 A -> AMBK 5 (clbQ c ++ A).
Proof.
  intros [p|] A HA; cbn [clbQ app]; [| apply (AMBK_mono 4); [lia| exact HA]].
  apply AMBK_cons; [exact HA| unfold CLIENT_VEC_BYTES; lia].
Qed.

Lemma malokA_ambK : forall n A, AMBK 4 A -> 0 <= n <= 2^26 + 64 -> malokA A n.
Proof. intros n A HA Hn c. apply malok_ambK; [apply AMBK_clbQ; exact HA| exact Hn]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma malloc_QambC : forall c X n, 0 <= n ->
  mspecL (fun s mo => QambC c X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => QambC c ((p, n) :: X) s mo /\ n < 2^63 | None => QambC c X s mo end).
Proof.
  intros c X n Hn.
  eapply mspecL_conseq; [apply (mspecL_keeps_fa c _ _ _ (raw_malloc_LQ (clbQ c ++ X) Pamb n Hn) (raw_malloc_keeps_fa n))| |].
  - intros s mo [[HQ E] HM]. destruct (HM c) as (H2 & H3 & H4). auto.
  - intros [p|] s mo [H E]; cbn beta iota in *.
    + destruct H as [H H63]. split; [| exact H63]. split; [| exact E]. eapply QI_perm; [| exact H]. apply Permutation_middle.
    + split; [exact H| exact E].
Qed.

Lemma free_QambC : forall c X p n, mspecL (QambC c ((p, n) :: X)) (raw_free p) (fun _ => QambC c X).
Proof.
  intros c X p n.
  eapply mspecL_conseq; [apply (mspecL_keeps_fa c _ _ _ (raw_free_LQ (clbQ c ++ X) Pamb p n) (raw_free_keeps_fa p))| |].
  - intros s mo [HQ E]. split; [| exact E]. eapply QI_perm; [| exact HQ]. apply Permutation_sym, Permutation_middle.
  - intros a s mo H; exact H.
Qed.

Lemma malloc_Qamb : forall X n, 0 <= n ->
  mspecL (fun s mo => Qamb X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Qamb ((p, n) :: X) s mo /\ n < 2^63 | None => Qamb X s mo end).
Proof.
  intros X n Hn. eapply (mspecL_pre LBUDGET _ (fun s mo => exists c, QambC c X s mo /\ malokA X n)); [| intros s mo [[c H] HM]; exists c; auto].
  apply mspecL_exI. intros c. eapply mspecL_post; [apply malloc_QambC; exact Hn|].
  intros [p|] s mo; cbn beta iota; [intros [H H63]; split; [exists c; exact H| exact H63]| intros H; exists c; exact H].
Qed.

Lemma free_Qamb : forall X p n, mspecL (Qamb ((p, n) :: X)) (raw_free p) (fun _ => Qamb X).
Proof. intros X p n. apply mspecL_exI. intros c. eapply mspecL_post; [apply free_QambC|]. intros a s mo H. exists c. exact H. Qed.

Lemma emit_Qamb : forall X v, mspecL (Qamb X) (io_emit io v) (fun _ => Qamb X).
Proof. intros X v. cbn [io io_emit io_S]. apply (s_emit_L LBUDGET (Qamb X) (Qamb_live X) (Qamb_so X)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma client_init_Q : forall A, AMBK 4 A ->
  mspecL (Qamb A) (HarnessM.client_init raw_malloc new_handler ps_fa set_fa_ps) (fun _ => Qamb A).
Proof.
  intros A HA. unfold HarnessM.client_init.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0. cbn beta.
  destruct (ps_fa s0) as [q|] eqn:E0.
  - apply mspecL_ret. intros s mo [_ H]. exact H.
  - eapply mspecL_bind with (Q1 := fun p => QambC None ((p, CLIENT_VEC_BYTES) :: A)).
    + unfold HarnessM.opnew. change (CLIENT_VEC_BYTES =? 0) with false. cbv iota.
      eapply mspecL_bind.
      * eapply mspecL_pre; [apply (malloc_QambC None A CLIENT_VEC_BYTES); unfold CLIENT_VEC_BYTES; lia|].
        intros s mo [-> (c & H & Ec)]. rewrite E0 in Ec. subst c. split; [split; [exact H| exact E0]|].
        apply malokA_ambK; [exact HA| unfold CLIENT_VEC_BYTES; lia].
      * intros [p|]; cbn beta iota.
        -- apply mspecL_ret. intros s mo [H _]. exact H.
        -- eapply mspecL_bind; [unfold new_handler; apply (mspecL_munr LBUDGET _ (fun _ _ _ => False))|]. intros [].
    + intros p. apply mspecL_upd'. intros s mo [H _]. exists (Some p). split; [| reflexivity].
      cbn [clbQ app] in *. apply QI_set_fa. exact H.
Qed.

(* [comment removed for export] *)
Lemma opnew_Q : forall X n, AMBK 4 X -> 0 < n <= 2^26 + 64 ->
  mspecL (Qamb X) (HarnessM.opnew raw_malloc new_handler n) (fun p => Qamb ((p, n) :: X)).
Proof.
  intros X n HX Hn. unfold HarnessM.opnew. cbv zeta. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  eapply mspecL_bind.
  - eapply mspecL_pre; [apply (malloc_Qamb X n); lia|]. intros s mo H. split; [exact H| apply malokA_ambK; [exact HX| lia]].
  - intros [p|]; cbn beta iota.
    + apply mspecL_ret. intros s mo [H _]. exact H.
    + eapply mspecL_bind; [unfold new_handler; apply (mspecL_munr LBUDGET _ (fun _ _ _ => False))|]. intros [].
Qed.

(* [comment removed for export] *)
Definition obQ (b : option bptr) (n : Z) : list (bptr * Z) := match b with Some p => [(p, n)] | None => [] end.

Lemma odelete_Q : forall X b n, mspecL (Qamb (obQ b n ++ X)) (HarnessM.odelete raw_free b) (fun _ => Qamb X).
Proof.
  intros X [p|] n; cbn [obQ app HarnessM.odelete].
  - unfold HarnessM.opdelete. apply free_Qamb.
  - ret_Q.
Qed.

Lemma AMBK_obQ : forall k b n X, AMBK k X -> 0 <= n <= 2^26 + 64 -> AMBK (S k) (obQ b n ++ X).
Proof. intros k [p|] n X HX Hn; cbn [obQ app]; [apply AMBK_cons; assumption| apply (AMBK_mono k); [lia| exact HX]]. Qed.

(* [comment removed for export] *)
Lemma minify_call_Q : forall A data, AMBK 2 A -> zlength data <= MAX_INPUT ->
  mspecL (Qamb A) (HarnessM.minify_call raw_malloc raw_free new_handler data) (fun _ => Qamb A).
Proof.
  intros A data HA Hlen. unfold HarnessM.minify_call. cbv zeta.
  set (n := Z.of_nat (length data)).
  assert (Hn : 0 <= n <= 2^26 + 64) by (unfold n, zlength, MAX_INPUT in *; lia).
  eapply mspecL_bind with (Q1 := fun b => Qamb (obQ b n ++ A)).
  { destruct (n =? 0) eqn:E.
    - ret_Q.
    - eapply mspecL_bind; [apply opnew_Q; [apply (AMBK_mono 2); [lia| exact HA]| apply Z.eqb_neq in E; lia]|]. intros p. ret_Q. }
  intros b. destruct (unclosed data).
  - eapply mspecL_bind; [apply (opnew_Q (obQ b n ++ A) ERRSTR_BYTES); [apply (AMBK_mono 3); [lia| apply AMBK_obQ; assumption]| unfold ERRSTR_BYTES; lia]|].
    intros t.
    eapply mspecL_bind with (Q1 := fun b' => Qamb ((t, ERRSTR_BYTES) :: obQ b' (if ERRMSG_LEN <=? n then n else ERRMSG_LEN) ++ A)).
    { destruct (ERRMSG_LEN <=? n).
      - ret_Q.
      - eapply mspecL_seq with (R := Qamb ((t, ERRSTR_BYTES) :: A)).
        + eapply mspecL_pre; [apply (odelete_Q ((t, ERRSTR_BYTES) :: A) b n)|].
          intros s mo H. eapply Qamb_perm; [| exact H]. destruct b as [p|]; cbn [obQ app]; [apply perm_swap| apply Permutation_refl].
        + intros _. eapply mspecL_bind.
          * apply (opnew_Q ((t, ERRSTR_BYTES) :: A) ERRMSG_LEN); [apply (AMBK_mono 3); [lia| apply AMBK_cons; [exact HA| unfold ERRSTR_BYTES; lia]]| unfold ERRMSG_LEN; lia].
          * intros p'. apply mspecL_ret. intros s mo H. eapply Qamb_perm; [| exact H]. cbn [obQ app]. apply perm_swap. }
    intros b'. eapply mspecL_seq.
    + unfold HarnessM.opdelete. apply free_Qamb.
    + intros _. apply odelete_Q.
  - apply odelete_Q.
Qed.

Lemma fuzz_one_Q : forall A data, AMBK 2 A -> zlength data <= MAX_INPUT ->
  mspecL (Qamb A) (fuzz_one data) (fun _ => Qamb A).
Proof.
  intros A data HA Hlen. unfold fuzz_one, HarnessM.fuzz_one.
  eapply mspecL_seq; [apply client_init_Q; apply (AMBK_mono 2); [lia| exact HA]|]. intros _.
  eapply mspecL_seq; [apply minify_call_Q; assumption|]. intros _. ret_Q.
Qed.

Lemma client_exit_Q : forall X, mspecL (Qamb X) client_exit (fun _ => Qamb X).
Proof.
  intros X. unfold client_exit, HarnessM.client_exit.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0. cbn beta.
  destruct (ps_fa s0) as [q|] eqn:E0.
  - eapply mspecL_seq with (R := QI X Pamb).     (* [comment removed for export] *)
    + unfold HarnessM.opdelete. eapply mspecL_pre; [apply (raw_free_LQ X Pamb q CLIENT_VEC_BYTES)|].
      intros s mo [-> (c & H & Ec)]. rewrite E0 in Ec. subst c. exact H.
    + intros _. apply mspecL_upd'. intros s mo H. exists None. split; [| reflexivity]. cbn [clbQ app]. apply QI_set_fa. exact H.
  - apply mspecL_ret. intros s mo [_ H]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_Q : forall A n payload rc, AMBK 2 A -> zlength payload <= MAX_INPUT ->
  mspecL (Qamb A) (run_calls fuzz_one (io_emit io) n payload rc) (fun _ => Qamb A).
Proof.
  intros A n. induction n as [|n IH]; intros payload rc HA Hl; cbn [run_calls]; [ret_Q|].
  eapply mspecL_seq; [apply fuzz_one_Q; assumption|]. intros rc'.
  eapply mspecL_seq; [apply emit_Qamb|]. intros _. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Theorem run_Q : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL (Qamb [(b, cap)]) (run cfg payload) (fun _ => Qamb [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp. unfold run, target_run.
  assert (HA1 : AMBK 1 [(b, cap)]) by (apply AMBK_cons; [apply AMBK_nil| unfold MAX_INPUT in *; lia]).
  eapply mspecL_bind with (Q1 := fun a s mo => match a with
                                               | None => Qamb [(b, cap)] s mo
                                               | Some None => Qamb [(b, cap)] s mo
                                               | Some (Some p) => Qamb [(p, zlength payload); (b, cap)] s mo
                                               end).
  { apply mspecL_if; intros _; [ret_Q|].
    eapply mspecL_bind.
    - eapply mspecL_pre; [apply malloc_Qamb; unfold zlength; lia|]. intros s mo HQ. split; [exact HQ|].
      apply (malokA_ambK (zlength payload) [(b, cap)]); [apply (AMBK_mono 1); [lia| exact HA1]| unfold MAX_INPUT, zlength in *; lia].
    - intros [p|]; apply mspecL_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecL_seq; [apply run_calls_Q; [apply AMBK_cons; [exact HA1| unfold MAX_INPUT, zlength in *; lia]| exact Hp]|]. intros rc.
    eapply mspecL_seq; [apply free_Qamb|]. intros _. ret_Q.
  - eapply mspecL_seq; [apply run_calls_Q; [apply (AMBK_mono 1); [lia| exact HA1]| exact Hp]|]. intros rc. eapply mspecL_seq; [ret_Q|]. intros _. ret_Q.
  - ret_Q.
Qed.

(* [comment removed for export] *)
Lemma OK_firstQ : malokA [] 65536.
Proof. apply malokA_ambK; [apply AMBK_nil| lia]. Qed.

Lemma OK_growQ : forall b k, (k <= 9)%nat -> malokA [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
  intros b k Hk. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as Hq.
  assert (Hp : 2 ^ Z.of_nat k <= 512). { change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
  apply malokA_ambK; [apply (AMBK_mono 1); [lia| apply AMBK_cons; [apply AMBK_nil| lia]]| lia].
Qed.
