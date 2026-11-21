(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc Stdio Harness Adapter Driver StepB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).


Section FsimEq.
Context {StG StC : Type}.
Variables (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Local Notation rel := (rel StG StC).
Local Notation fsim := (fsim debtG debtC stepG).

Definition fsimeq {A} (R : rel) (mG : M StG A) (mC : M StC A) (Q : A -> rel) : Prop :=
  fsim R mG mC (fun a b sG moG sC moC => a = b /\ Q a sG moG sC moC).

Lemma fsimeq_bind {A B} (R : rel) (mG : M StG A) (mC : M StC A) (Q1 : A -> rel) (kG : A -> M StG B) (kC : A -> M StC B) Q :
  fsimeq R mG mC Q1 -> (forall a, fsimeq (Q1 a) (kG a) (kC a) Q) -> fsimeq R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. unfold fsimeq. eapply fsim_bind_eq; [exact H1| exact H2]. Qed.

Lemma fsimeq_ret {A} (R : rel) (a : A) (Q : A -> rel) :
  (forall sG moG sC moC, R sG moG sC moC -> Q a sG moG sC moC) -> fsimeq R (mret a) (mret a) Q.
Proof. intros H. unfold fsimeq. apply fsim_ret. intros; split; [reflexivity| apply H; assumption]. Qed.

Lemma fsimeq_munr {A} (R : rel) (Q : A -> rel) : fsimeq R (munr (A:=A)) (munr (A:=A)) Q.
Proof. unfold fsimeq. apply fsim_munr. Qed.

Lemma fsimeq_conseq {A} (R R' : rel) (mG : M StG A) (mC : M StC A) (Q Q' : A -> rel) :
  fsimeq R mG mC Q -> (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) ->
  (forall a sG moG sC moC, Q a sG moG sC moC -> Q' a sG moG sC moC) -> fsimeq R' mG mC Q'.
Proof. intros H HR HQ. unfold fsimeq in *. eapply fsim_conseq; [exact H| exact HR|]. intros a b sG moG sC moC [-> HQa]. auto. Qed.

Lemma fsimeq_pre {A} (R R' : rel) (mG : M StG A) (mC : M StC A) (Q : A -> rel) :
  fsimeq R mG mC Q -> (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) -> fsimeq R' mG mC Q.
Proof. intros H HR. eapply fsimeq_conseq; eauto. Qed.

Lemma fsimeq_post {A} (R : rel) (mG : M StG A) (mC : M StC A) (Q Q' : A -> rel) :
  fsimeq R mG mC Q -> (forall a sG moG sC moC, Q a sG moG sC moC -> Q' a sG moG sC moC) -> fsimeq R mG mC Q'.
Proof. intros H HQ. eapply fsimeq_conseq; eauto. Qed.

Lemma fsimeq_seq {A B} (R R1 : rel) (mG : M StG A) (mC : M StC A) (kG : A -> M StG B) (kC : A -> M StC B) Q :
  fsimeq R mG mC (fun _ => R1) -> (forall a, fsimeq R1 (kG a) (kC a) Q) -> fsimeq R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. eapply fsimeq_bind; [exact H1| exact H2]. Qed.

Lemma fsimeq_pointwise {A} (R : rel) (mG : M StG A) (mC : M StC A) Q :
  (forall sG moG sC moC, R sG moG sC moC -> fsimeq (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) mG mC Q) ->
  fsimeq R mG mC Q.
Proof. intros H. unfold fsimeq. apply fsim_pointwise. exact H. Qed.

Lemma fsimeq_if {A} (b : bool) (R : rel) (m1G m2G : M StG A) (m1C m2C : M StC A) Q :
  (b = true -> fsimeq R m1G m1C Q) -> (b = false -> fsimeq R m2G m2C Q) -> fsimeq R (if b then m1G else m2G) (if b then m1C else m2C) Q.
Proof. intros H1 H2. destruct b; auto. Qed.


Lemma fsimeq_loop {X A} (I : X -> rel) (Q : A -> rel) (bodyG : X -> M StG (X + A)) (bodyC : X -> M StC (X + A)) :
  (forall x, fsimeq (I x) (bodyG x) (bodyC x) (fun r => match r with inl x' => I x' | inr a => Q a end)) ->
  forall fuel x, fsimeq (I x) (mloop fuel bodyG x) (mloop fuel bodyC x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply fsimeq_munr|].
  eapply fsimeq_bind; [apply Hb|]. intros [x'|a]; cbn beta; [apply IH| apply fsimeq_ret; auto].
Qed.
End FsimEq.


Definition E1 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 1)) (to_bytes l).
Definition E2 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 2)) (to_bytes l).
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
Definition PIECE_MAX : Z := 1048576.

Section Det.
Context {St : Type}.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.

Definition detio {A} (t : itree node (exc (A * St))) (mo : Model) (P : list event -> A -> St -> Prop) : Prop :=
  exists tr a s', tpath stp t mo tr (Ok (a, s')) mo /\ P tr a s'
    /\ (forall tr' x mo', tpath stp t mo tr' x mo' -> x = Ok (a, s') /\ mo' = mo /\ tr' = tr)
    /\ (forall tr', ~ texit stp nexit t mo tr').






End Det.


Section StdioChar.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall v s, get_so (set_so v s) = v.
Hypothesis set_set : forall v w s, set_so v (set_so w s) = set_so v s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Hypothesis st_sub : forall n mo r mo' e, ~ nf_node n -> stp n mo r mo' e -> nstep n mo r mo' e.
Hypothesis st_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stp n mo r mo e.
Local Notation detio := (detio (stp:=stp)).

Definition wr_post (s : St) (buf0 bs : list Z) (tr : list event) (u : unit) (s' : St) : Prop :=
  exists so', s' = set_so so' s /\ so_active so' = true /\ zlength (so_buf so') <= STDOUT_BUFSIZ
    /\ tr ++ E1 (so_buf so') = E1 buf0 ++ E1 bs.
Definition WR (m : Monad.M St unit) (bs : list Z) : Prop :=
  forall s mo, so_active (get_so s) = true -> zlength (so_buf (get_so s)) <= STDOUT_BUFSIZ -> zlength bs <= PIECE_MAX ->
    detio (m s) mo (wr_post s (so_buf (get_so s)) bs).
Definition WR0 (m : Monad.M St unit) (bs : list Z) : Prop :=
  forall s mo, zlength (so_buf (get_so s)) <= STDOUT_BUFSIZ -> zlength bs <= PIECE_MAX ->
    detio (m s) mo (fun tr u s' => wr_post s (so_buf (get_so s)) bs tr u s' /\ so_buf (get_so s') = []).


Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros n l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

Lemma iov_advance_concat : forall iov cnt, (length iov <= 2)%nat -> 0 <= cnt <= Z.of_nat (length (concat iov)) ->
  concat (map to_bytes (iov_advance iov cnt)) = skipn (Z.to_nat cnt) (concat (map to_bytes iov))
  /\ (length (iov_advance iov cnt) <= 2)%nat.
Proof.
  intros iov cnt Hl Hc. destruct iov as [|a [|b [|c rest]]]; cbn in Hl, Hc |- *; [| | |lia].
  - split; [destruct (Z.to_nat cnt); reflexivity| lia].
  - rewrite !app_nil_r. split; [apply to_bytes_skipn| cbn; lia].
  - rewrite app_nil_r in *. rewrite length_app in Hc. destruct (Z.ltb_spec (zlength a) cnt); cbn; rewrite ?app_nil_r.
    + unfold zlength in *. split; [|lia]. rewrite to_bytes_skipn, skipn_app, to_bytes_length.
      replace (skipn (Z.to_nat cnt) (to_bytes a)) with (@nil byte) by (symmetry; apply skipn_all2; rewrite to_bytes_length; lia).
      cbn. f_equal. lia.
    + unfold zlength in *. split; [|lia]. rewrite to_bytes_skipn, skipn_app, to_bytes_length.
      replace (Z.to_nat cnt - length a)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma length_concat_to_bytes' : forall iov, length (concat (map to_bytes iov)) = length (concat iov).
Proof. induction iov as [|a iov IH]; cbn; [reflexivity|]. rewrite !length_app, to_bytes_length, IH. reflexivity. Qed.

Lemma stdio_write_loop_det : forall fuel fd iov (st : St) mo,
  (length (concat (map to_bytes iov)) < fuel)%nat -> (length iov <= 2)%nat -> Z.of_nat (length (concat (map to_bytes iov))) < 2^63 ->
  detio (stdio_write_loop (St:=St) fuel fd iov st) mo
        (fun tr _ s' => s' = st /\ tr = map (WriteEv (Z_to_bv 64 fd)) (concat (map to_bytes iov))).
Proof.
  induction fuel as [|fuel IH]; intros fd iov st mo Hf Hl Hb; [lia|]. cbn [stdio_write_loop].
  set (all := concat (map to_bytes iov)) in *. set (T := Z.of_nat (length all)) in *.
  assert (Htot : iov_total iov = T). { unfold iov_total, zlength. subst T all. rewrite length_concat_to_bytes'. reflexivity. }
  rewrite Htot.
  assert (Hans : forall rsp mo' evs, stp (NWritev fd (map to_bytes iov)) mo rsp mo' evs ->
            mo' = mo /\ exists k, 0 <= k <= T /\ (k = T \/ 1 <= k < T) /\ dec_writev T rsp = Some k /\
                             evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) all)).
  { intros rsp mo' evs Hst. apply st_sub in Hst; [|cbn; tauto]. pose proof (nstep_dec_writev fd (map to_bytes iov) mo rsp mo' evs ltac:(fold all T; lia) Hst) as (k & Hd & Hk & -> & ->).
    fold all in Hd, Hk |- *. fold T in Hd, Hk. split; [reflexivity|]. exists k. split; [lia|]. split; [lia|]. split; [exact Hd| reflexivity]. }
  assert (HstF : stp (NWritev fd (map to_bytes iov)) mo (eff0 (Z_to_bv 64 T)) mo (map (WriteEv (Z_to_bv 64 fd)) all)).
  { apply st_same; [cbn; tauto|]. cbn [nstep]. split; [reflexivity|]. fold all. fold T. destruct (Z.eqb_spec T 0) as [E|NE].
    - split; [rewrite E; reflexivity|]. subst T. destruct all; [reflexivity| cbn in E; lia].
    - exists T. split; [lia|]. split; [reflexivity|]. subst T. rewrite Nat2Z.id, firstn_all. reflexivity. }
  assert (HdF : dec_writev T (eff0 (Z_to_bv 64 T)) = Some T).
  { unfold dec_writev, dec_count, dec_count0, eff0. rewrite unsigned_lit by lia. destruct (Z.eqb_spec T 0) as [E|NE].
    - rewrite E. reflexivity.
    - replace (1 <=? T) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.leb_refl. reflexivity. }
  exists (map (WriteEv (Z_to_bv 64 fd)) all), tt, st. split; [|split; [auto|split]].
  - apply tpath_mbind_ok. exists (map (WriteEv (Z_to_bv 64 fd)) all), T, st, mo, []. split; [apply tpath_msys_ok; exists (eff0 (Z_to_bv 64 T)); auto|].
    rewrite Z.eqb_refl, app_nil_r. split; [apply tpath_mret; auto| reflexivity].
  - intros tr' x mo' Hp. apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & cnt & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + exfalso. apply tpath_msys_any in Hp as (rsp & Hst & E). destruct (Hans _ _ _ Hst) as (_ & k & _ & _ & Hd & _). rewrite Hd in E. discriminate.
    + apply tpath_msys_ok in Hp1 as (rsp & Hst & Hd & ->). destruct (Hans _ _ _ Hst) as (-> & k & Hk & Hcase & Hd' & ->).
      rewrite Hd in Hd'. injection Hd' as <-.
      destruct (Z.eqb_spec cnt T) as [->|NE].
      * apply tpath_mret in Hp2 as (-> & -> & ->). rewrite app_nil_r. subst T. rewrite Nat2Z.id, firstn_all. auto.
      * destruct Hcase as [->|Hlt]; [congruence|].
        destruct (iov_advance_concat iov cnt Hl ltac:(fold all T; rewrite <- length_concat_to_bytes'; fold all; lia)) as [Ec Hl'].
        fold all in Ec.
        assert (Hlen' : length (concat (map to_bytes (iov_advance iov cnt))) = (length all - Z.to_nat cnt)%nat).
        { rewrite Ec, length_skipn. reflexivity. }
        destruct (IH fd (iov_advance iov cnt) st mo ltac:(rewrite Hlen'; lia) Hl' ltac:(rewrite Hlen'; lia)) as (trI & [] & sI & _ & [-> ->] & HuI & _).
        destruct (HuI _ _ _ Hp2) as (-> & -> & ->). rewrite Ec, <- map_app, firstn_skipn. auto.
  - intros tr' Hx. apply texit_mbind in Hx as [Hx|(tr1 & cnt & s1 & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + exact (texit_msys_nonexit (NWritev fd (map to_bytes iov)) _ _ _ _ I Hx).
    + apply tpath_msys_ok in Hp1 as (rsp & Hst & Hd & ->). destruct (Hans _ _ _ Hst) as (-> & k & Hk & Hcase & Hd' & ->).
      rewrite Hd in Hd'. injection Hd' as <-.
      destruct (Z.eqb_spec cnt T) as [->|NE]; [exact Hx2|].
      destruct Hcase as [->|Hlt]; [congruence|].
      destruct (iov_advance_concat iov cnt Hl ltac:(fold all T; rewrite <- length_concat_to_bytes'; fold all; lia)) as [Ec Hl']. fold all in Ec.
      assert (Hlen' : length (concat (map to_bytes (iov_advance iov cnt))) = (length all - Z.to_nat cnt)%nat).
      { rewrite Ec, length_skipn. reflexivity. }
      destruct (IH fd (iov_advance iov cnt) st mo ltac:(rewrite Hlen'; lia) Hl' ltac:(rewrite Hlen'; lia)) as (trI & aI & sI & _ & _ & _ & HxI).
      exact (HxI _ Hx2).
Qed.

Lemma stdio_write_det : forall fd buf s (st : St) mo, zlength buf + zlength s <= WRITE_MAX ->
  detio (stdio_write (St:=St) fd buf s st) mo (fun tr _ s' => s' = st /\ tr = map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))).
Proof.
  intros fd buf s st mo Hlen. unfold stdio_write.
  destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)); [lia|].
  set (iov := match buf with [] => [s] | _ :: _ => [buf; s] end).
  assert (Hc : concat (map to_bytes iov) = to_bytes (buf ++ s)). { subst iov. destruct buf; cbn; rewrite ?app_nil_r, ?to_bytes_app; reflexivity. }
  assert (Hl : (length iov <= 2)%nat) by (subst iov; destruct buf; cbn; lia).
  rewrite <- Hc. apply stdio_write_loop_det; [| exact Hl|]; rewrite Hc, to_bytes_length, length_app; unfold zlength, WRITE_MAX in *; lia.
Qed.

Let upd_so := (upd_so get_so set_so).
Let rd_so := (rd_so (St:=St) get_so).















End StdioChar.

Local Open Scope list_scope. Local Open Scope Z_scope.
Definition diag_short (d : diag_msg) : Prop :=
  match d with
  | DUsage a | DCannotOpen a | DReadError a => zlength a <= PIECE_MAX
  | _ => True
  end.

Lemma digits_aux_length : forall f n acc, (length (digits_aux f n acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros n acc; cbn [digits_aux]; [lia|].
  destruct (n =? 0); [cbn; lia|]. specialize (IH (n / 10) (48 + n mod 10 :: acc)). cbn in IH. lia.
Qed.
Lemma fmt_u_length : forall n, (length (fmt_u n) <= 20)%nat.
Proof. intros n. unfold fmt_u. pose proof (digits_aux_length 20 n []). cbn [length Nat.add] in H. exact H. Qed.

Section IOS.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall v s, get_so (set_so v s) = v.
Hypothesis set_set : forall v w s, set_so v (set_so w s) = set_so v s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Hypothesis st_sub : forall n mo r mo' e, ~ nf_node n -> stp n mo r mo' e -> nstep n mo r mo' e.
Hypothesis st_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stp n mo r mo e.
Local Notation detio := (detio (stp:=stp)).


End IOS.


Section DetSim.
Context {StG StC : Type} (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.

Lemma fsim_of_detio {A B} (R : rel StG StC) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel StG StC) :
  (forall sG moG sC moC, R sG moG sC moC ->
     exists PG PC, detio (stp:=stepG) (mG sG) moG PG /\ detio (stp:=nstep) (mC sC) moC PC /\
       forall trG a sG' trC b sC', PG trG a sG' -> PC trC b sC' ->
         exists v, trG ++ debtG sG' = debtG sG ++ v /\ trC ++ debtC sC' = debtC sC ++ v /\ Q a b sG' moG sC' moC) ->
  fsim debtG debtC stepG R mG mC Q.
Proof.
  intros H sG moG sC moC HR.
  destruct (H _ _ _ _ HR) as (PG & PC & (trG & a & sG' & HpG & HPG & HuG & HxG) & (trC & b & sC' & HpC & HPC & HuC & HxC) & HQ).
  split.
  - intros trG' a' sG'' moG' Hp. destruct (HuG _ _ _ Hp) as (E & -> & ->). injection E as -> ->.
    destruct (HQ _ _ _ _ _ _ HPG HPC) as (v & E1 & E2 & HQ'). exists trC, b, sC', moC, v. auto.
  - intros trG' Hx. exfalso. exact (HxG _ Hx).
Qed.
End DetSim.


Section StdioSim.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let d0 : St -> list event := fun _ => [].
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis stepG_sub : forall n mo r mo' e, ~ nf_node n -> stepG n mo r mo' e -> nstep n mo r mo' e.
Hypothesis stepG_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stepG n mo r mo e.
Variable R : rel St St.
Hypothesis HRget : forall sG moG sC moC, R sG moG sC moC -> get_so sG = get_so sC.
Hypothesis HRset : forall sG moG sC moC v, R sG moG sC moC -> R (set_so v sG) moG (set_so v sC) moC.
Local Notation fsimeq := (fsimeq d0 d0 stepG).
Local Notation fsim := (fsim d0 d0 stepG).

Let upd_so := (upd_so get_so set_so).
Let rd_so := (rd_so (St:=St) get_so).
Local Ltac ret_same := apply fsimeq_ret; intros ? ? ? ? HH; exact HH.

Lemma rd_so_sim : fsimeq R rd_so rd_so (fun _ => R).
Proof.
  unfold rd_so, Stdio.rd_so, fsimeq. eapply fsim_bind; [apply fsim_get|]. intros a b. cbn beta.
  apply fsim_ret. intros sG moG sC moC (-> & -> & HR). split; [apply (HRget _ _ _ _ HR)| exact HR].
Qed.

Lemma upd_so_sim : forall f, fsimeq R (upd_so f) (upd_so f) (fun _ => R).
Proof.
  intros f. unfold upd_so, Stdio.upd_so, fsimeq. apply fsim_upd. intros sG moG sC moC HR.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. rewrite (HRget _ _ _ _ HR). apply HRset. exact HR.
Qed.

Lemma stdio_write_sim : forall fd buf s, fsimeq R (stdio_write fd buf s) (stdio_write fd buf s) (fun _ => R).
Proof.
  intros fd buf s. destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)) as [Hbig|Hok].
  - unfold stdio_write. replace (WRITE_MAX <? zlength buf + zlength s) with true by (symmetry; apply Z.ltb_lt; exact Hbig). apply fsimeq_munr.
  - unfold fsimeq. apply fsim_of_detio. intros sG moG sC moC HR.
    eexists _, _. split; [apply (stdio_write_det stepG_sub stepG_same); exact Hok|]. split; [apply (stdio_write_det (stp:=nstep) ltac:(auto) ltac:(auto)); exact Hok|].
    intros trG [] sG' trC [] sC' [-> ->] [-> ->]. exists (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))). unfold d0. rewrite !app_nil_r. cbn [app]. auto.
Qed.

Lemma stdout_stdio_write_sim : forall s, fsimeq R (stdout_stdio_write get_so set_so s) (stdout_stdio_write get_so set_so s) (fun _ => R).
Proof.
  intros s. unfold stdout_stdio_write.
  eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  eapply fsimeq_seq; [apply stdio_write_sim|]. intros _. apply upd_so_sim.
Qed.

Lemma ioctl_sim : fsimeq R (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) (fun _ => R).
Proof.
  unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. destruct Hst as (-> & -> & ->). split; [left; reflexivity|]. exists (efferr ENOTTY), moC, a. cbn. auto.
  - intros code moG' Hx. destruct Hx.
Qed.

Lemma stdout_writefn_sim : forall s, fsimeq R (stdout_writefn get_so set_so s) (stdout_writefn get_so set_so s) (fun _ => R).
Proof.
  intros s. unfold stdout_writefn.
  eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  eapply fsimeq_seq.
  - apply fsimeq_if; intros _; [|ret_same].
    eapply fsimeq_seq; [apply upd_so_sim|]. intros _.
    eapply fsimeq_bind; [apply ioctl_sim|]. intros [e|v]; [apply upd_so_sim| apply fsimeq_munr].
  - intros _. apply stdout_stdio_write_sim.
Qed.

Lemma stdout_towrite_sim : fsimeq R (stdout_towrite get_so set_so) (stdout_towrite get_so set_so) (fun _ => R).
Proof. unfold stdout_towrite. apply upd_so_sim. Qed.

Lemma stdout_fwritex_sim : forall s, fsimeq R (stdout_fwritex get_so set_so s) (stdout_fwritex get_so set_so s) (fun _ => R).
Proof.
  intros s. unfold stdout_fwritex.
  eapply fsimeq_seq; [apply stdout_towrite_sim|]. intros _.
  eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  apply fsimeq_if; intros _; [apply stdout_writefn_sim|].
  apply fsimeq_if; intros _; [|apply upd_so_sim].
  eapply fsimeq_seq; [apply fsimeq_if; intros _; [apply stdout_writefn_sim| ret_same]|]. intros _. apply upd_so_sim.
Qed.

Lemma out_pieces_sim : forall ps, fsimeq R (out_pieces get_so set_so ps) (out_pieces get_so set_so ps) (fun _ => R).
Proof.
  induction ps as [|p ps IH]; cbn [out_pieces]; [ret_same|].
  eapply fsimeq_seq; [apply stdout_fwritex_sim|]. intros _. apply IH.
Qed.

Lemma stdout_vprintf_sim : forall ps, fsimeq R (stdout_vprintf get_so set_so ps) (stdout_vprintf get_so set_so ps) (fun _ => R).
Proof. intros ps. unfold stdout_vprintf. eapply fsimeq_seq; [apply stdout_towrite_sim|]. intros _. apply out_pieces_sim. Qed.

Lemma stdout_exit_flush_sim : fsimeq R (stdout_exit_flush get_so set_so) (stdout_exit_flush get_so set_so) (fun _ => R).
Proof.
  unfold stdout_exit_flush. eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  apply fsimeq_if; intros _; [apply stdout_writefn_sim| ret_same].
Qed.

Lemma stderr_pieces_sim : forall ps buf, fsimeq R (stderr_pieces (St:=St) buf ps) (stderr_pieces (St:=St) buf ps) (fun _ => R).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [ret_same|].
  apply fsimeq_if; intros _; [|apply IH].
  eapply fsimeq_seq; [apply stdio_write_sim|]. intros _. apply IH.
Qed.

Lemma stderr_fprintf_sim : forall ps, fsimeq R (stderr_fprintf (St:=St) ps) (stderr_fprintf (St:=St) ps) (fun _ => R).
Proof. intros ps. unfold stderr_fprintf. eapply fsimeq_bind; [apply stderr_pieces_sim|]. intros buf. apply stdio_write_sim. Qed.

Lemma stderr_fwrite_sim : forall s, fsimeq R (stderr_fwrite (St:=St) s) (stderr_fwrite (St:=St) s) (fun _ => R).
Proof. intros s. unfold stderr_fwrite. apply fsimeq_if; intros _; [apply stdio_write_sim| ret_same]. Qed.

Lemma s_diag_sim : forall d, fsimeq R (s_diag d) (s_diag d) (fun _ => R).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_sim | apply stderr_fwrite_sim]. Qed.

Lemma s_emit_sim : forall v, fsimeq R (s_emit get_so set_so v) (s_emit get_so set_so v) (fun _ => R).
Proof. intros v. unfold s_emit. apply stdout_vprintf_sim. Qed.
End StdioSim.
