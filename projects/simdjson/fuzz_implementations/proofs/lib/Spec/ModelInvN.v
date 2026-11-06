(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad MSafe MSafeN STree Malloc Stdio SjModel Target TargetSafe Driver Prog KInv KStep KStepC ModelInv.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Image.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section WithCeiling. Context {CE__ : Ceiling}.

Section DriverSpecN.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable rstage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.

Variable own : list ptr -> assn St.

Definition diag_ok (d : diag_msg) : Prop :=
  match d with
  | DUsage a | DCannotOpen a | DReadError a => zlength a < 2^32
  | _ => True
  end.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecN (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspecN (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, diag_ok d -> mspecN (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspecN (own X) (io_exit io) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspecN (own X) (alloc_init bm) (fun _ => own X).

Variable own' : list ptr -> assn St.
Hypothesis Hrun : forall X cfg payload, zlength payload <= MAX_INPUT -> mspecN (own X) (run cfg payload) (fun _ => own' X).
Hypothesis Hdf' : forall X p, mspecN (own' (p :: X)) (drv_free p) (fun _ => own' X).
Hypothesis Hcount' : forall X, mspecN (own' X) alloc_count (fun _ => own' X).

Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.

Lemma own_after_node : forall X s mo n rsp mo' evs,
  own X s mo -> nsafe n mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X s mo'.
Proof.
  intros X s mo n rsp mo' evs Ho Hsafe Hst Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hsafe Hst) as [Hh' Hmi']. eapply Hown_fds; eauto.
Qed.

Definition rd_inv (X : list ptr) (st : rd_st) : assn St := fun s mo =>
  own (rd_buf st :: X) s mo
  /\ zlength (rd_content st) <= rd_cap st
  /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).

Definition rd_meas (st : @rd_st ptr) : nat := Z.to_nat (MAX_INPUT + 1 - zlength (rd_content st)).

Lemma zlength_app {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_u8s : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.

Lemma pow2_le_1024 : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof.
  intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia.
Qed.

Lemma read_loop_body_spec : forall X fd path st,
  zlength path < 2^32 -> 0 <= fd ->
  mspecN (rd_inv X st) (read_loop_body io drv_malloc drv_free rstage fd path st)
        (fun r s mo => match r with
                       | inl st' => rd_inv X st' s mo /\ (rd_meas st' < rd_meas st)%nat
                       | inr RdExit => exists X', own X' s mo
                       | inr (RdDone buf content) => own (buf :: X) s mo /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros X fd path st Hpath Hfd. unfold read_loop_body.
  eapply mspecN_bind with
    (Q1 := fun g s mo => match g with
                         | None => exists X', own X' s mo
                         | Some st1 => rd_inv X st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                         end).
  { apply mspecN_if_pre.
    - apply mspecN_if_pre.
      + eapply mspecN_seq; [eapply mspecN_pre; [apply Hdiag; exact I|]|].
        { intros s mo [[[Ho _] _] _]. exact Ho. }
        intros _. apply mspecN_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
      + apply mspecN_pointwise. intros s0 mo0 [[(Ho0 & Hlen & k & Hk & Hcap) Heq] Hlt].
        apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
        pose proof (pow2_le_1024 k Hk) as Hp.
        eapply mspecN_bind. { eapply mspecN_pre; [apply Hdm; lia|]. intros s mo [-> ->]. exact Ho0. }
        intros [nb|]; cbn beta iota.
        * apply mspecN_pure. intros _. eapply mspecN_seq.
          { eapply mspecN_pre; [apply (Hdf (nb :: X) (rd_buf st))|].
            intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
          intros _. apply mspecN_ret. intros s mo Ho. cbn. unfold rd_inv. cbn. splits; auto; try lia.
          exists (S k). split; [unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia|].
          rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
        * eapply mspecN_seq; [apply Hdiag; exact I|]. intros _. apply mspecN_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
    - apply mspecN_ret. intros s mo [[Ho [Hlen Hk]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
  intros [st1|]; cbn beta iota.
  2:{ apply mspecN_ret. intros s mo H. exact H. }
  eapply mspecN_bind; [apply mspecN_get|]. intros sg. cbn beta iota.
  apply mspecN_pointwise. intros s1 mo1 [Hsg ((Ho & Hlen & k & Hk & Hcap) & Hct & Hlt)]. subst sg.
  pose proof (pow2_le_1024 k Hk) as Hp.
  apply mspecN_bind with (Q1 := fun a s mo => s = s1 /\ own (rd_buf st1 :: X) s mo /\
                       match a with RdErr _ => True | RdData bs => zlength bs <= rd_cap st1 - zlength (rd_content st) end).
  { apply mspecN_sys. intros s mo [-> ->]. split; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (nstep_dec_read fd _ (Z.min (rd_cap st1 - zlength (rd_content st)) 65536) mo1 rsp mo' evs ltac:(unfold MAX_INPUT, zlength in *; lia) Hst) as (_ & a & Hdec & Ha).
    exists a. split; [exact Hdec|].
    cbn beta. split; [reflexivity|].
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
    { destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
      destruct Ha as (p & off & data & _ & _ & _ & ->). reflexivity. }
    split; [eapply own_after_node; eauto; exact I|].
    destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
    unfold zlength. pose proof (length_file_read_le_count data off (Z.min (rd_cap st1 - Z.of_nat (length (rd_content st))) 65536) ltac:(unfold zlength, MAX_INPUT in *; lia)). lia. }
  intros [e|bs]; cbn beta iota.
  - eapply mspecN_seq. { eapply mspecN_pre; [apply Hdiag; exact Hpath|]. intros s mo (_ & Ho' & _). exact Ho'. }
    intros _. apply mspecN_ret. intros s mo Ho'. exists (rd_buf st1 :: X). exact Ho'.
  - apply mspecN_if; intros C.
    + apply mspecN_ret. intros s mo (-> & Ho' & _). split; [exact Ho'|]. rewrite Hct. unfold MAX_INPUT in *. lia.
    + apply mspecN_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
      assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
      split.
      * unfold rd_inv. cbn. split; [exact Ho'|]. rewrite zlength_app, zlength_u8s, Hct. split; [lia|]. exists k. auto.
      * unfold rd_meas. cbn. rewrite zlength_app, zlength_u8s, Hct. unfold MAX_INPUT in *. lia.
Qed.

Lemma m_vmmaps_with_fds : forall f mo, m_vmmaps (with_fds f mo) = m_vmmaps mo.
Proof. reflexivity. Qed.

Lemma read_all_spec : forall X path, zlength path < 2^32 -> path_okZ path ->
  mspecN (own X) (read_all io drv_malloc drv_free rstage path)
        (fun r s mo => match r with
                       | RdExit => exists X', own X' s mo
                       | RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT
                       end).
Proof.
  intros X path Hpath Hpok. unfold read_all.
  apply mspecN_bind with (Q1 := fun r s mo => own X s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
  { apply mspecN_sys. intros s mo Ho. split; [exact Hpok|]. intros rsp mo' evs Hst.
    destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
    pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
    exists a. split; [exact Hdec|]. cbn beta.
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
    { destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). reflexivity. }
    split; [eapply own_after_node; eauto; exact Hpok|]. destruct a as [e|fd]; [exact I|]. lia. }
  intros [e|fd]; cbn beta iota.
  - apply mspecN_pure. intros _. eapply mspecN_seq; [apply Hdiag; exact Hpath|]. intros _. apply mspecN_ret. intros s mo Ho. exists X. exact Ho.
  - apply mspecN_pure. intros Hfd. eapply mspecN_bind; [apply Hdm; lia|]. intros [buf|]; cbn beta iota.
    2:{ eapply mspecN_seq; [apply Hdiag; exact I|]. intros _. apply mspecN_ret. intros s mo Ho. exists X. exact Ho. }
    apply mspecN_pure. intros _.
    eapply mspecN_bind.
    + eapply mspecN_pre.
      * apply (mspecN_loop (read_loop_body io drv_malloc drv_free rstage fd path) (rd_inv X)
                 (fun r s mo => match r with RdExit => exists X', own X' s mo
                                | RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT end)
                 rd_meas).
        { intros st. eapply mspecN_post; [apply read_loop_body_spec; [exact Hpath| exact Hfd]|].
          intros [st'|[|b c]] s mo H; exact H. }
        unfold rd_meas, READ_FUEL. cbn [rd_content]. unfold zlength. cbn [length Z.of_nat]. unfold MAX_INPUT. lia.
      * intros s mo Ho. unfold rd_inv. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia|reflexivity].
    + intros [|buf' content]; cbn beta iota; [apply mspecN_ret; intros s mo H; exact H|].
      apply mspecN_pointwise. intros s1 mo1 [Ho1 Hlen].
      eapply mspecN_bind with (Q1 := fun _ s mo => own (buf' :: X) s mo).
      * apply mspecN_sys. intros s mo [-> ->]. split; [exact I|]. intros rsp mo' evs Hst.
        pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
        exists a. split; [exact Hdec|]. cbn beta.
        assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
        { destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). reflexivity. }
        eapply own_after_node; eauto; exact I.
      * intros _. apply mspecN_ret. intros s mo Ho. split; [exact Ho| exact Hlen].
Qed.

Lemma skipn_length_le {A} (n : nat) (l : list A) : (length (skipn n l) <= length l)%nat.
Proof. rewrite length_skipn. lia. Qed.

Lemma main_model_spec : forall X argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecN (own X) (main_model io drv_malloc drv_free rstage alloc_init run alloc_count argv)
        (fun _ s mo => (exists X', own X' s mo) \/ (exists X', own' X' s mo)).
Proof.
  intros X argv Hargv Hpaths. unfold main_model.
  assert (Hnth : forall i, zlength (nth i argv []) < 2^32).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  apply mspecN_if; intros Hlen2.
  { eapply mspecN_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply mspecN_ret. intros s mo Ho. left. exists X; exact Ho. }
  assert (Hp1 : path_okZ (nth 1 argv [])).
  { apply Bool.negb_false_iff in Hlen2. apply Z.eqb_eq in Hlen2.
    destruct argv as [|a0 [|a1 rest]]; cbn in Hlen2; try lia. cbn. inversion Hpaths; assumption. }
  eapply mspecN_bind; [apply read_all_spec; [apply Hnth| exact Hp1]|].
  intros [|buf content]; cbn beta iota; [apply mspecN_ret; intros s mo H; left; exact H|].
  apply mspecN_pure. intros Hlen.
  apply mspecN_if; intros _.
  { eapply mspecN_seq; [apply Hdiag; exact I|]. intros _. eapply mspecN_seq; [apply Hdf|]. intros _. apply mspecN_ret. intros s mo Ho; left; exists X; exact Ho. }
  apply mspecN_if; intros _.
  { eapply mspecN_seq; [apply Hdiag; exact I|]. intros _. eapply mspecN_seq; [apply Hdf|]. intros _. apply mspecN_ret. intros s mo Ho; left; exists X; exact Ho. }
  eapply mspecN_seq; [apply Hinit|]. intros _.
  eapply mspecN_seq; [apply Hrun; pose proof (skipn_length_le (Z.to_nat (6 + Z.land (le16 content) 0x7fff)) content) as HSK; unfold zlength in *; lia|]. intros status.
  eapply mspecN_seq with (R := own' (buf :: X)).
  { destruct (Z.testbit _ 15); [|apply mspecN_ret; intros s mo H; exact H].
    eapply mspecN_seq; [apply Hcount'|]. intros n. apply mspecN_ret. intros s mo H; exact H. }
  intros status'. eapply mspecN_seq; [apply Hdf'|]. intros _. apply mspecN_ret. intros s mo Ho. right. exists X. exact Ho.
Qed.

Lemma exit_model_spec : forall code,
  mspecN (fun s mo => exists X, own X s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_model. eapply mspecN_seq with (R := fun s mo => exists X, own X s mo).
  - apply mspecN_exI. intros X. eapply mspecN_post; [apply Hexit|]. intros a s mo Ho. exists X. exact Ho.
  - intros _. apply mspecN_sys. intros s mo _. split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverSpecN.

Definition raw_malloc_some_stmt : Prop := forall X n, 0 <= n < 2^62 ->
  mspecN (GI X) (raw_malloc n) (fun r s mo => exists p, r = Some p /\ GI (p :: X) s mo).

Section Assembly.
Hypothesis HSOME : raw_malloc_some_stmt.

Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  | Cho k => forall z, tall P (k z)
  end.
Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
  induction t as [[|r]|n k IH|kc IHc]; cbn; intros H HP.
  - exact I.
  - apply HP. exact H.
  - intros rsp. eapply IH; [apply H| exact HP].
  - intros z. eapply IHc; [apply H| exact HP].
Qed.
Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
  induction t as [[|a]|n k IH|kc IHc]; cbn; intros f H HF; [exact I| apply HF; exact H| |intros z; apply IHc; [apply H| exact HF]].
  intros rsp. apply IH; [apply H| exact HF].
Qed.
Lemma twfN_tall : forall {R} (t : itree node (exc R)) mo (P : exc R -> Model -> Prop) (T : R -> Prop),
  twfN t mo P -> tall T t -> twfN t mo (fun r mo1 => P r mo1 /\ match r with Ok a => T a | _ => True end).
Proof.
  intros R t. induction t as [[|r]|n k IH|kc IHc]; cbn; intros mo P T H HT.
  - split; [exact H| exact I].
  - split; [exact H| exact HT].
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [eapply Hk; exact Hst| apply HT].
  - intros z. apply IHc; [apply H| apply HT].
Qed.
Section Keeps.
  Context {B : Type} (f : PState -> B).
  Definition keeps {A} (c : Monad.M PState A) : Prop := forall s, tall (fun p => f (snd p) = f s) (c s).
  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. reflexivity. Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. exact I. Qed.
  Lemma keeps_get : keeps mget.
  Proof. intros s. reflexivity. Qed.
  Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
  Proof. intros g Hg s. cbn. apply Hg. Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
  Lemma keeps_bind : forall {A C} (m : Monad.M PState A) (k : A -> Monad.M PState C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.
  Lemma keeps_getk : forall {C} (k : PState -> Monad.M PState C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  Lemma keeps_if : forall {A} (b : bool) (m1 m2 : Monad.M PState A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
End Keeps.
Arguments keeps {B} f {A} c.

Lemma keeps_x_ev_step : forall e, keeps ps_x (ev_step e).
Proof.
  intros e. destruct e; cbn [ev_step].
  - apply keeps_if.
    + apply keeps_bind; [apply keeps_sys|]. intros r. apply keeps_bind; [apply keeps_upd; intros [? ? ? ? ?]; reflexivity|]. intros _. apply keeps_ret.
    + apply keeps_getk. intros s0. apply keeps_bind; [apply keeps_sys|]. intros [|]; [| apply keeps_ret].
      apply keeps_bind; [apply keeps_upd; intros [? ? ? ? ?]; reflexivity|]. intros _. apply keeps_ret.
  - apply keeps_if; [| apply keeps_if]; (apply keeps_bind; [apply keeps_sys|]; intros a; apply keeps_ret).
  - apply keeps_bind; [apply keeps_sys|]. intros a. apply keeps_ret.
  - apply keeps_bind; [apply keeps_sys|]. intros a. apply keeps_ret.
  - apply keeps_unr.
  - apply keeps_unr.
Qed.
Lemma keeps_x_membed : forall {R} (t : stree ev Z R), keeps ps_x (membed t).
Proof.
  intros R t. induction t as [r|e k IH]; cbn [membed]; [apply keeps_ret|].
  apply keeps_bind; [apply keeps_x_ev_step| intros z; apply IH].
Qed.
Lemma keeps_x_raw_free : forall p, keeps ps_x (raw_free p).
Proof.
  intros p. unfold raw_free. apply keeps_getk. intros s0. apply keeps_bind; [apply keeps_x_membed|]. intros st'.
  apply keeps_upd. intros [? ? ? ? ?]; reflexivity.
Qed.

Lemma mspecN_keeps : forall {A B} (f : PState -> B) (c : Monad.M PState A) (P : assn PState) (Q : A -> assn PState) (v : B),
  keeps f c -> mspecN P c Q -> mspecN (fun s mo => P s mo /\ f s = v) c (fun r s mo => Q r s mo /\ f s = v).
Proof.
  intros A B f c P Q v K H s mo [HP Hf]. unfold mspecN, etwfN in *.
  eapply twfN_mono; [apply (twfN_tall _ _ _ _ (H s mo HP) (K s))|].
  intros [|[a s']] mo1; cbn; [tauto|]. intros [HQ E]. split; [exact HQ|]. congruence.
Qed.

Definition xl (s : PState) : list bptr := match ps_x s with Some p => [p] | None => [] end.
Definition GIx (X : list bptr) : assn PState := fun s mo => GI (xl s ++ X) s mo.

Lemma GI_set_x : forall X v s mo, GI X s mo -> GI X (set_x_ps v s) mo.
Proof. intros X v s mo H. eapply OWN_other; [exact H|reflexivity|reflexivity|]. exact (OWN_G _ _ _ _ H). Qed.

Lemma NoDup_app_middle {T} : forall (l2 l1 l3 : list T), List.NoDup (l1 ++ l2 ++ l3) -> List.NoDup (l1 ++ l3).
Proof.
  induction l2 as [|b l2 IH]; intros l1 l3 H; cbn in H; [exact H|].
  apply IH. exact (NoDup_remove_1 _ _ _ H).
Qed.
Lemma GI_drop_middle : forall A Bm C s mo, GI (A ++ Bm ++ C) s mo -> GI (A ++ C) s mo.
Proof.
  intros A Bm C s mo [(L & Hc & HK & Hi) [Hnd HG]]. split; [|split; [|exact HG]].
  - exists L. split; [exact Hc|]. split; [exact HK|]. intros c Hin. apply Hi. rewrite !map_app in *. rewrite !in_app_iff in *. tauto.
  - rewrite !map_app in *. exact (NoDup_app_middle _ _ _ Hnd).
Qed.

Lemma raw_free_GIx : forall X p, mspecN (GIx (p :: X)) (raw_free p) (fun _ => GIx X).
Proof.
  intros X p. apply mspecN_pointwise. intros s0 mo0 H0.
  eapply mspecN_conseq; [apply (mspecN_keeps ps_x (raw_free p) (GI (p :: (xl s0 ++ X))) (fun _ => GI (xl s0 ++ X)) (ps_x s0));
                         [apply keeps_x_raw_free| apply mspec_N; apply raw_free_GI]| |].
  - intros s mo [-> ->]. split; [|reflexivity]. eapply GI_perm; [| exact H0]. apply Permutation_sym. apply Permutation_middle.
  - intros u s mo [H E]. unfold GIx, xl in *. rewrite E. exact H.
Qed.

Lemma alloc_count_GIx : forall X, mspecN (GIx X) alloc_count (fun _ => GIx X).
Proof. intros X. unfold alloc_count. apply mspecN_ret. auto. Qed.

Lemma run_GIx : forall X cfg payload, zlength payload <= MAX_INPUT -> mspecN (GI X) (run cfg payload) (fun _ => GIx X).
Proof.
  intros X cfg payload Hpl. unfold run.
  eapply mspecN_bind.
  - apply (target_run_mspecN raw_malloc raw_free ps_so set_so_ps GI).
    + exact HSOME.
    + intros X' p. apply mspec_N. apply raw_free_GI.
    + apply GI_perm.
    + intros X'. apply mspec_N. apply stdout_vprintf_GI. unfold pieces_emit_0. repeat constructor; unfold zlength; cbn; lia.
    + unfold MAX_INPUT in Hpl. change (2^32) with 4294967296. lia.
  - intros r. cbn beta. eapply mspecN_seq with (R := GIx X).
    + apply mspecN_upd'. intros s mo [H _]. unfold GIx.
      replace (xl (set_x_ps (snd r) s)) with (olist (snd r)) by (destruct s; destruct (snd r); reflexivity).
      apply GI_set_x. exact H.
    + intros _. apply mspecN_ret. intros s mo H. exact H.
Qed.

Lemma keeps_loop : forall {B X R} (f : PState -> B) fuel (body : X -> Monad.M PState (X + R)),
  (forall x, keeps f (body x)) -> forall x, keeps f (mloop fuel body x).
Proof.
  intros B X R f. induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
  apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
Qed.
Lemma keeps_x_raw_malloc : forall n, keeps ps_x (raw_malloc n).
Proof.
  intros n. unfold raw_malloc. apply keeps_getk. intros s0. apply keeps_bind; [apply keeps_x_membed|]. intros [st' p].
  apply keeps_bind; [apply keeps_upd; intros [? ? ? ? ?]; reflexivity|]. intros _. apply keeps_ret.
Qed.
Lemma keeps_x_stdio_writev : forall fd buf bs, keeps ps_x (stdio_writev (St:=PState) fd buf bs).
Proof.
  intros fd buf bs. unfold stdio_writev. apply keeps_loop. intros x. unfold wv_body.
  apply keeps_bind; [apply keeps_sys|]. intros k. apply keeps_if; apply keeps_ret.
Qed.
Lemma keeps_x_stderr_pieces : forall ps buf, keeps ps_x (stderr_pieces (St:=PState) buf ps).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply keeps_ret|].
  apply keeps_if; [| apply IH]. apply keeps_bind; [apply keeps_x_stdio_writev|]. intros _. apply IH.
Qed.
Lemma keeps_x_s_diag : forall d, keeps ps_x (s_diag (St:=PState) d).
Proof.
  intros d. unfold s_diag. destruct d; unfold stderr_fprintf, stderr_fwrite;
  try (apply keeps_bind; [apply keeps_x_stderr_pieces| intros buf; apply keeps_x_stdio_writev]);
  (apply keeps_if; [apply keeps_x_stdio_writev| apply keeps_ret]).
Qed.
Lemma keeps_x_startup : keeps ps_x startup.
Proof. unfold startup. apply keeps_bind; [apply keeps_sys|]. intros _. apply keeps_ret. Qed.

Definition GI0 (X : list bptr) : assn PState := fun s mo => GI X s mo /\ ps_x s = None.

Lemma GI0_of_keeps : forall {A} (c : Monad.M PState A) X (Q : A -> list bptr),
  keeps ps_x c -> mspec (GI X) c (fun r s mo => GI (Q r) s mo) -> mspecN (GI0 X) c (fun r s mo => GI0 (Q r) s mo).
Proof.
  intros A c X Q K H. unfold GI0. eapply mspecN_conseq; [apply (mspecN_keeps ps_x c (GI X) (fun r s mo => GI (Q r) s mo) None K); apply mspec_N; exact H| |];
  cbn beta; intros; tauto.
Qed.

Lemma raw_malloc_GI0 : forall X n, 0 <= n ->
  mspecN (GI0 X) (raw_malloc n) (fun r s mo => match r with Some p => GI0 (p :: X) s mo /\ n < 2^63 | None => GI0 X s mo end).
Proof.
  intros X n Hn. unfold GI0.
  eapply mspecN_conseq;
    [apply (mspecN_keeps ps_x (raw_malloc n) (GI X)
              (fun r s mo => match r with Some p => GI (p :: X) s mo /\ n < 2^63 | None => GI X s mo end) None);
     [apply keeps_x_raw_malloc| apply mspec_N; apply raw_malloc_GI; exact Hn]| |].
  - cbn beta. intros; tauto.
  - cbn beta. intros [p|] s mo [H E]; tauto.
Qed.
Lemma raw_free_GI0 : forall X p, mspecN (GI0 (p :: X)) (raw_free p) (fun _ => GI0 X).
Proof. intros X p. apply (GI0_of_keeps (raw_free p) (p :: X) (fun _ => X)); [apply keeps_x_raw_free| apply raw_free_GI]. Qed.
Lemma GI0_perm : forall X Y s mo, Permutation X Y -> GI0 X s mo -> GI0 Y s mo.
Proof. intros X Y s mo HP [H E]. split; [eapply GI_perm; eauto| exact E]. Qed.
Lemma s_diag_GI0 : forall X d, diag_ok d -> mspecN (GI0 X) (io_diag io d) (fun _ => GI0 X).
Proof. intros X d Hd. apply (GI0_of_keeps _ X (fun _ => X)); [apply keeps_x_s_diag| apply s_diag_GI; exact Hd]. Qed.
Lemma alloc_init_GI0 : forall X bm, mspecN (GI0 X) (alloc_init bm) (fun _ => GI0 X).
Proof. intros X bm. unfold alloc_init. apply mspecN_ret. auto. Qed.
Lemma alloc_count_GI0 : forall X, mspecN (GI0 X) alloc_count (fun _ => GI0 X).
Proof. intros X. unfold alloc_count. apply mspecN_ret. auto. Qed.
Lemma GI0_minv : forall X s mo, GI0 X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo [H _]. eapply GI_minv; exact H. Qed.
Lemma GI0_fds : forall X s mo mo', GI0 X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> GI0 X s mo'.
Proof. intros X s mo mo' [H E] Hv Hm Hh. split; [eapply GI_fds; eauto| exact E]. Qed.
Lemma GIx_perm : forall X Y s mo, Permutation X Y -> GIx X s mo -> GIx Y s mo.
Proof. intros X Y s mo HP H. unfold GIx in *. eapply GI_perm; [| exact H]. apply Permutation_app_head. exact HP. Qed.
Lemma GIx_minv : forall X s mo, GIx X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo H. eapply GI_minv; exact H. Qed.
Lemma GIx_fds : forall X s mo mo', GIx X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> GIx X s mo'.
Proof. intros X s mo mo' H Hv Hm Hh. unfold GIx in *. eapply GI_fds; eauto. Qed.
Lemma run_GI0 : forall X cfg payload, zlength payload <= MAX_INPUT -> mspecN (GI0 X) (run cfg payload) (fun _ => GIx X).
Proof. intros X cfg payload Hpl. eapply mspecN_pre; [apply run_GIx; exact Hpl|]. intros s mo [H _]. exact H. Qed.
Lemma startup_GI0 : forall X, mspecN (GI0 X) startup (fun _ => GI0 X).
Proof. intros X. apply (GI0_of_keeps startup X (fun _ => X)); [apply keeps_x_startup| apply startup_GI]. Qed.

Lemma xfree_GIN : mspecN (fun s mo => (exists X, GI0 X s mo) \/ (exists X, GIx X s mo)) xfree (fun _ s mo => exists X, GI X s mo).
Proof.
  unfold xfree. eapply mspecN_bind; [apply mspecN_get|]. intros s0. cbn beta.
  apply mspecN_pointwise. intros s mo [<- H].
  destruct (ps_x s0) as [p|] eqn:E.
  - destruct H as [[X [H E']]|[X H]]; [congruence|].
    eapply mspecN_conseq; [apply mspec_N; apply (raw_free_GI X p)| |].
    + intros s' mo' [-> ->]. unfold GIx, xl in H. rewrite E in H. exact H.
    + intros u s' mo' H'. exists X. exact H'.
  - apply mspecN_ret. intros s' mo' [-> ->].
    destruct H as [[X [H _]]|[X H]]; exists X; [exact H|]. unfold GIx, xl in H. rewrite E in H. exact H.
Qed.

Lemma exit_imp_spec : forall code,
  mspecN (fun s mo => (exists X, GI0 X s mo) \/ (exists X, GIx X s mo)) (exit_imp code) (fun _ _ _ => False).
Proof.
  intros code. unfold exit_imp. eapply mspecN_seq; [apply xfree_GIN|]. intros _.
  eapply (exit_model_spec io GI); first [(intros; apply mspec_N; apply stdout_exit_flush_GI) | apply GI_minv | apply GI_fds].
Qed.

Lemma prog_with_GIN : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecN (GI0 []) (prog_with rstage argv) (fun _ _ _ => False).
Proof.
  intros rstage argv Hargv Hpaths. unfold prog_with.
  eapply mspecN_seq; [apply startup_GI0|]. intros _.
  eapply mspecN_bind.
  - eapply (main_model_spec io raw_malloc raw_free rstage alloc_init run alloc_count GI0);
      [ (intros X n Hn; apply raw_malloc_GI0; exact Hn) | (intros X p; apply raw_free_GI0) | apply GI0_perm
      | (intros; apply s_diag_GI0; assumption)
      | (intros; apply alloc_init_GI0) | apply run_GI0 | (intros X p; apply raw_free_GIx) | apply alloc_count_GIx
      | apply GI0_minv | apply GI0_fds | exact Hargv | exact Hpaths ].
  - intros code. apply exit_imp_spec.
Qed.

Theorem prog_model_ok : forall segs rstage pc ph lim en inp,
  segs_pu segs ->
  valid_entry (mkImage segs pc ph) en inp ->
  valid_input_either inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  tsafe nstep node_noerrN (prog segs rstage (in_argv inp)) (mo0 segs lim en inp) ->
  leaves_unreachable_m nstep (prog segs rstage (in_argv inp)) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (prog segs rstage (in_argv inp)) (mo0 segs lim en inp).
Proof.
  intros segs rstage pc ph lim [sp brk0 mbase] inp Hsegs Hve Hvi Htop HN.
  destruct Hve as (_ & Hbrk & _). destruct Hvi as (Hargv & _).
  unfold prog, mo0 in *. cbn [en_brk en_mmap_base en_sp] in *.
  apply (mspecN_program (GI0 []) (prog_with rstage (argv_Z (in_argv inp)))); [| | exact HN].
  - apply prog_with_GIN; [apply argv_Z_short| apply argv_Z_paths]; exact Hargv.
  - cbn [img_segments] in Hbrk.
    split; [| reflexivity].
    apply (GI_init segs); [exact Hbrk| apply reserved_top_pu; exact Hsegs| apply ceil_pu; exact Hsegs| exact Htop].
Qed.

Theorem prog_model_ok_P : forall en inp,
  valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) en inp -> valid_input_either inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  tsafe nstep node_noerrN (prog psegs pstage (in_argv inp)) (mo0 psegs source_alloc_limit en inp) ->
  leaves_unreachable_m nstep (prog psegs pstage (in_argv inp)) (mo0 psegs source_alloc_limit en inp)
  /\ tsafe nstep nsafe (prog psegs pstage (in_argv inp)) (mo0 psegs source_alloc_limit en inp).
Proof. intros en inp. apply prog_model_ok. apply segs_pu_P. Qed.

Theorem prog_model_ok_U : forall en inp,
  valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input_either inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  tsafe nstep node_noerrN (prog usegs ustage (in_argv inp)) (mo0 usegs target_alloc_limit en inp) ->
  leaves_unreachable_m nstep (prog usegs ustage (in_argv inp)) (mo0 usegs target_alloc_limit en inp)
  /\ tsafe nstep nsafe (prog usegs ustage (in_argv inp)) (mo0 usegs target_alloc_limit en inp).
Proof. intros en inp. apply prog_model_ok. apply segs_pu_U. Qed.

End Assembly.
End WithCeiling.

