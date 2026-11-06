(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc Stdio Harness Adapter Driver StepB.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FsimEq.
Context {StG StC : Type}.
Variables (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Local Notation rel := (rel StG StC).
Local Notation fsim := (fsim debtG debtC stepG).

Definition fsimeq {A} (R : rel) (mG : M StG A) (mC : M StC A) (Q : A -> rel) : Prop :=
  fsim R mG mC (fun a b sG moG sC moC => a = b /\ Q a sG moG sC moC).

#[using="Type"] Lemma fsimeq_bind {A B} (R : rel) (mG : M StG A) (mC : M StC A) (Q1 : A -> rel) (kG : A -> M StG B) (kC : A -> M StC B) Q :
  fsimeq R mG mC Q1 -> (forall a, fsimeq (Q1 a) (kG a) (kC a) Q) -> fsimeq R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. unfold fsimeq. eapply fsim_bind_eq; [exact H1| exact H2]. Qed.

#[using="Type"] Lemma fsimeq_ret {A} (R : rel) (a : A) (Q : A -> rel) :
  (forall sG moG sC moC, R sG moG sC moC -> Q a sG moG sC moC) -> fsimeq R (mret a) (mret a) Q.
Proof. intros H. unfold fsimeq. apply fsim_ret. intros; split; [reflexivity| apply H; assumption]. Qed.

#[using="Type"] Lemma fsimeq_munr {A} (R : rel) (Q : A -> rel) : fsimeq R (munr (A:=A)) (munr (A:=A)) Q.
Proof. unfold fsimeq. apply fsim_munr. Qed.

#[using="Type"] Lemma fsimeq_conseq {A} (R R' : rel) (mG : M StG A) (mC : M StC A) (Q Q' : A -> rel) :
  fsimeq R mG mC Q -> (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) ->
  (forall a sG moG sC moC, Q a sG moG sC moC -> Q' a sG moG sC moC) -> fsimeq R' mG mC Q'.
Proof. intros H HR HQ. unfold fsimeq in *. eapply fsim_conseq; [exact H| exact HR|]. intros a b sG moG sC moC [-> HQa]. auto. Qed.

#[using="Type"] Lemma fsimeq_pre {A} (R R' : rel) (mG : M StG A) (mC : M StC A) (Q : A -> rel) :
  fsimeq R mG mC Q -> (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) -> fsimeq R' mG mC Q.
Proof. intros H HR. eapply fsimeq_conseq; eauto. Qed.

#[using="Type"] Lemma fsimeq_post {A} (R : rel) (mG : M StG A) (mC : M StC A) (Q Q' : A -> rel) :
  fsimeq R mG mC Q -> (forall a sG moG sC moC, Q a sG moG sC moC -> Q' a sG moG sC moC) -> fsimeq R mG mC Q'.
Proof. intros H HQ. eapply fsimeq_conseq; eauto. Qed.

#[using="Type"] Lemma fsimeq_seq {A B} (R R1 : rel) (mG : M StG A) (mC : M StC A) (kG : A -> M StG B) (kC : A -> M StC B) Q :
  fsimeq R mG mC (fun _ => R1) -> (forall a, fsimeq R1 (kG a) (kC a) Q) -> fsimeq R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. eapply fsimeq_bind; [exact H1| exact H2]. Qed.

#[using="Type"] Lemma fsimeq_pointwise {A} (R : rel) (mG : M StG A) (mC : M StC A) Q :
  (forall sG moG sC moC, R sG moG sC moC -> fsimeq (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) mG mC Q) ->
  fsimeq R mG mC Q.
Proof. intros H. unfold fsimeq. apply fsim_pointwise. exact H. Qed.

#[using="Type"] Lemma fsimeq_if {A} (b : bool) (R : rel) (m1G m2G : M StG A) (m1C m2C : M StC A) Q :
  (b = true -> fsimeq R m1G m1C Q) -> (b = false -> fsimeq R m2G m2C Q) -> fsimeq R (if b then m1G else m2G) (if b then m1C else m2C) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

#[using="Type"] Lemma fsimeq_false {A} (mG : M StG A) (mC : M StC A) Q : fsimeq (fun _ _ _ _ => False) mG mC Q.
Proof. unfold fsimeq. apply fsim_false. Qed.

#[using="Type"] Lemma fsimeq_loop {X A} (I : X -> rel) (Q : A -> rel) (bodyG : X -> M StG (X + A)) (bodyC : X -> M StC (X + A)) :
  (forall x, fsimeq (I x) (bodyG x) (bodyC x) (fun r => match r with inl x' => I x' | inr a => Q a end)) ->
  forall fuel x, fsimeq (I x) (mloop fuel bodyG x) (mloop fuel bodyC x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply fsimeq_munr|].
  eapply fsimeq_bind; [apply Hb|]. intros [x'|a]; cbn beta; [apply IH| apply fsimeq_ret; auto].
Qed.
End FsimEq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition E1 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 1)) (to_bytes l).
Definition E2 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 2)) (to_bytes l).
Lemma E1_app : forall a b, E1 (a ++ b) = E1 a ++ E1 b.
Proof. intros. unfold E1, to_bytes. rewrite !map_app. reflexivity. Qed.
Lemma E2_app : forall a b, E2 (a ++ b) = E2 a ++ E2 b.
Proof. intros. unfold E2, to_bytes. rewrite !map_app. reflexivity. Qed.
Lemma E1_nil : E1 [] = []. Proof. reflexivity. Qed.
Lemma E2_nil : E2 [] = []. Proof. reflexivity. Qed.
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
(* [comment removed for export] *)
Definition PIECE_MAX : Z := 1048576.

Section Det.
Context {St : Type}.
(* [comment removed for export] *)
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.

Definition detio {A} (t : itree node (exc (A * St))) (mo : Model) (P : list event -> A -> St -> Prop) : Prop :=
  exists tr a s', tpath stp t mo tr (Ok (a, s')) mo /\ P tr a s'
    /\ (forall tr' x mo', tpath stp t mo tr' x mo' -> x = Ok (a, s') /\ mo' = mo /\ tr' = tr)
    /\ (forall tr', ~ texit stp nexit t mo tr').

#[using="Type"] Lemma detio_ret {A} : forall (a : A) (s : St) mo (P : list event -> A -> St -> Prop), P [] a s -> detio (mret a s) mo P.
Proof.
  intros a s mo P HP. exists [], a, s. split; [cbn; auto|]. split; [exact HP|]. split; [| intros tr' []].
  intros tr' x mo' (E & -> & ->). auto.
Qed.

#[using="Type"] Lemma detio_upd : forall (f : St -> St) s mo (P : list event -> unit -> St -> Prop), P [] tt (f s) -> detio (mupd f s) mo P.
Proof.
  intros f s mo P HP. exists [], tt, (f s). split; [cbn; auto|]. split; [exact HP|]. split; [| intros tr' []].
  intros tr' x mo' (E & -> & ->). auto.
Qed.

#[using="Type"] Lemma detio_bind {A B} : forall (m : Monad.M St A) (k : A -> Monad.M St B) s mo P Q,
  detio (m s) mo P -> (forall tr a s', P tr a s' -> detio (k a s') mo (fun tr2 b s2 => Q (tr ++ tr2) b s2)) ->
  detio (mbind m k s) mo Q.
Proof.
  intros m k s mo P Q (tr1 & a & s1 & Hp1 & HP1 & Hu1 & Hx1) Hk.
  destruct (Hk tr1 a s1 HP1) as (tr2 & b & s2 & Hp2 & HP2 & Hu2 & Hx2).
  exists (tr1 ++ tr2), b, s2. split; [apply tpath_mbind_ok; exists tr1, a, s1, mo, tr2; auto|]. split; [exact HP2|]. split.
  - intros tr' x mo' Hp. destruct x as [|[b' s2']].
    + unfold mbind in Hp. apply tpath_ebind in Hp. destruct Hp as [[Hp _]|(tr3 & [a3 s3] & mo3 & tr4 & Hp3 & Hp4 & ->)].
      * destruct (Hu1 _ _ _ Hp) as (E & _). discriminate.
      * destruct (Hu1 _ _ _ Hp3) as (E & -> & ->). injection E as -> ->. cbn [fst snd] in Hp4. destruct (Hu2 _ _ _ Hp4) as (E' & _). discriminate.
    + apply tpath_mbind_ok in Hp as (tr3 & a3 & s3 & mo3 & tr4 & Hp3 & Hp4 & ->).
      destruct (Hu1 _ _ _ Hp3) as (E & -> & ->). injection E as -> ->. destruct (Hu2 _ _ _ Hp4) as (E' & -> & ->). auto.
  - intros tr' Hx. apply texit_mbind in Hx as [Hx|(tr3 & a3 & s3 & mo3 & tr4 & Hp3 & Hx4 & ->)]; [exact (Hx1 _ Hx)|].
    destruct (Hu1 _ _ _ Hp3) as (E & -> & ->). injection E as -> ->. exact (Hx2 _ Hx4).
Qed.

#[using="Type"] Lemma detio_mono {A} : forall (t : itree node (exc (A * St))) mo (P Q : list event -> A -> St -> Prop),
  detio t mo P -> (forall tr a s, P tr a s -> Q tr a s) -> detio t mo Q.
Proof. intros t mo P Q (tr & a & s & H1 & H2 & H3 & H4) HPQ. exists tr, a, s. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma detio_sys {A} : forall n (dec : resp -> option A) (s : St) mo rsp evs a (P : list event -> A -> St -> Prop),
  stp n mo rsp mo evs -> dec rsp = Some a ->
  (forall rsp' mo' evs', stp n mo rsp' mo' evs' -> rsp' = rsp /\ mo' = mo /\ evs' = evs) ->
  match n with NExit _ => False | _ => True end ->
  P evs a s -> detio (msys n dec s) mo P.
Proof.
  intros n dec s mo rsp evs a P Hst Hd Hu Hn HP. exists evs, a, s. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [exact HP|]. split.
  - intros tr' x mo' Hp. unfold msys in Hp. apply tpath_enode in Hp as (rsp' & Hst' & E). destruct (Hu _ _ _ Hst') as (-> & -> & ->). rewrite Hd in E. subst. auto.
  - intros tr' Hx. eapply texit_msys_nonexit; [| exact Hx]. exact Hn.
Qed.

End Det.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition so_inv (so : stdout_st) : Prop := (so_active so = false -> so_buf so = []) /\ zlength (so_buf so) <= STDOUT_BUFSIZ.

Section StdioChar.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall v s, get_so (set_so v s) = v.
Hypothesis set_set : forall v w s, set_so v (set_so w s) = set_so v s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
(* [comment removed for export] *)
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Hypothesis st_sub : forall n mo r mo' e, ~ nf_node n -> stp n mo r mo' e -> nstep n mo r mo' e.   (* [comment removed for export] *)
Hypothesis st_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stp n mo r mo e.
Local Notation detio := (detio (stp:=stp)).

(* [comment removed for export] *)
Definition wr_post (s : St) (buf0 bs : list Z) (tr : list event) (u : unit) (s' : St) : Prop :=
  exists so', s' = set_so so' s /\ so_active so' = true /\ zlength (so_buf so') <= STDOUT_BUFSIZ
    /\ tr ++ E1 (so_buf so') = E1 buf0 ++ E1 bs.
Definition WR (m : Monad.M St unit) (bs : list Z) : Prop :=
  forall s mo, so_active (get_so s) = true -> zlength (so_buf (get_so s)) <= STDOUT_BUFSIZ -> zlength bs <= PIECE_MAX ->
    detio (m s) mo (wr_post s (so_buf (get_so s)) bs).
(* [comment removed for export] *)
Definition WR0 (m : Monad.M St unit) (bs : list Z) : Prop :=
  forall s mo, zlength (so_buf (get_so s)) <= STDOUT_BUFSIZ -> zlength bs <= PIECE_MAX ->
    detio (m s) mo (fun tr u s' => wr_post s (so_buf (get_so s)) bs tr u s' /\ so_buf (get_so s') = []).

#[using="Type"] Lemma zlength_app_ {A} (a b : list A) : zlength (a ++ b) = zlength a + zlength b.
Proof. unfold zlength. rewrite length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62108319258.12000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros n l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
#[using="Type"] Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

#[using="Type"] Lemma iov_advance_concat : forall iov cnt, (length iov <= 2)%nat -> 0 <= cnt <= Z.of_nat (length (concat iov)) ->
  concat (map to_bytes (iov_advance iov cnt)) = skipn (Z.to_nat cnt) (concat (map to_bytes iov))
  /\ (length (iov_advance iov cnt) <= 2)%nat.
Proof.
  intros iov cnt Hl Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0080>11243032820.1616007654544.1523094145225.1323100433956.1528200660786.1241480806399.1544831285033.1567643081.15   00000400=00A00H00O00X00a00hS2HlS2Hl2Hc1HS2HlS2Hl2HcS2Hl2HcS2Hl2Hc1HS2Hl2Hc1HS2Hl2Hc".
destruct iov as [|a [|b [|c rest]]]; cbn in Hl, Hc |- *; [| | |lia].
  - split; [destruct (Z.to_nat cnt); reflexivity| lia].
  - rewrite !app_nil_r. split; [apply to_bytes_skipn| cbn; lia].
  - rewrite app_nil_r in *. rewrite length_app in Hc. destruct (Z.ltb_spec (zlength a) cnt); cbn; rewrite ?app_nil_r.
    + unfold zlength in *. split; [|lia]. rewrite to_bytes_skipn, skipn_app, to_bytes_length.
      replace (skipn (Z.to_nat cnt) (to_bytes a)) with (@nil byte) by (symmetry; apply skipn_all2; rewrite to_bytes_length; lia).
      cbn. f_equal. lia.
    + unfold zlength in *. split; [|lia]. rewrite to_bytes_skipn, skipn_app, to_bytes_length.
      replace (Z.to_nat cnt - length a)%nat with 0%nat by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma length_concat_to_bytes' : forall iov, length (concat (map to_bytes iov)) = length (concat iov).
Proof. induction iov as [|a iov IH]; cbn; [reflexivity|]. rewrite !length_app, to_bytes_length, IH. reflexivity. Qed.

#[using="st_sub st_same"] Lemma stdio_write_loop_det : forall fuel fd iov (st : St) mo,
  (length (concat (map to_bytes iov)) < fuel)%nat -> (length iov <= 2)%nat -> Z.of_nat (length (concat (map to_bytes iov))) < 2^63 ->
  detio (stdio_write_loop (St:=St) fuel fd iov st) mo
        (fun tr _ s' => s' = st /\ tr = map (WriteEv (Z_to_bv 64 fd)) (concat (map to_bytes iov))).
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "00>0>1448173107.16 1876134254.26 22481159167.3622481159167.3829406272477.253376111990.36 3376111990.38 45774887436.264614126463.23 64831266161.2467186943210.3367186943210.358184223268.23 9753470396.23 00000700A00Y01101;01P01e01o02802B02M02X02b02lS2Hf2HlS2Hf2Hl2HkS2Hf2Hl2Hb3Hlt3Hl'5Hlen'S2Hf2Hl2Hb3Hlt3Hl'5Hlen'S2Hf2Hl2HbS2Hf2Hl3Hlt3Hl'5Hlen'S2Hf2Hl3Hlt3Hl'5Hlen'S2Hf2Hl2HkS2Hf2Hl1ES2Hf2Hl2NES2Hf2Hl3HltS2Hf2Hl3HltS2Hf2Hl2HbS2Hf2Hl2NE".
induction fuel as [|fuel IH]; intros fd iov st mo Hf Hl Hb; [lia|]. cbn [stdio_write_loop].
  set (all := concat (map to_bytes iov)) in *. set (T := Z.of_nat (length all)) in *.
  assert (Htot : iov_total iov = T). { unfold iov_total, zlength. subst T all. rewrite length_concat_to_bytes'. reflexivity. }
  rewrite Htot.
  (* [comment removed for export] *)
  assert (Hans : forall rsp mo' evs, stp (NWritev fd (map to_bytes iov)) mo rsp mo' evs ->
            mo' = mo /\ exists k, 0 <= k <= T /\ (k = T \/ 1 <= k < T) /\ dec_writev T rsp = Some k /\
                             evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) all)).
  { intros rsp mo' evs Hst. apply st_sub in Hst; [|cbn; tauto]. pose proof (nstep_dec_writev fd (map to_bytes iov) mo rsp mo' evs ltac:(fold all T; lia) Hst) as (k & Hd & Hk & -> & ->).
    fold all in Hd, Hk |- *. fold T in Hd, Hk. split; [reflexivity|]. exists k. split; [lia|]. split; [lia|]. split; [exact Hd| reflexivity]. }
  (* [comment removed for export] *)
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st_sub st_same"] Lemma stdio_write_det : forall fd buf s (st : St) mo, zlength buf + zlength s <= WRITE_MAX ->
  detio (stdio_write (St:=St) fd buf s st) mo (fun tr _ s' => s' = st /\ tr = map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))).
Proof.
  intros fd buf s st mo Hlen. unfold stdio_write.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>13546083599.1922466479674.1923094145225.1648155385697.1673936932.18   00000400=00>00F00GS2HlS4Hlen2HlSS4Hlen1HS".
destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)); [lia|].
  set (iov := match buf with [] => [s] | _ :: _ => [buf; s] end).
  assert (Hc : concat (map to_bytes iov) = to_bytes (buf ++ s)). { subst iov. destruct buf; cbn; rewrite ?app_nil_r, ?to_bytes_app; reflexivity. }
  assert (Hl : (length iov <= 2)%nat) by (subst iov; destruct buf; cbn; lia).
  rewrite <- Hc. apply stdio_write_loop_det; [| exact Hl|]; rewrite Hc, to_bytes_length, length_app; unfold zlength, WRITE_MAX in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Let upd_so := (upd_so get_so set_so).
Let rd_so := (rd_so (St:=St) get_so).

#[using="Type"] Lemma rd_so_det : forall s mo, detio (rd_so s) mo (fun tr a s' => tr = [] /\ a = get_so s /\ s' = s).
Proof.
  intros s mo. unfold rd_so, Stdio.rd_so. eapply (detio_bind mget (fun s0 => mret (get_so s0)) s mo (fun tr a s' => tr = [] /\ a = s /\ s' = s)).
  - exists [], s, s. cbn. split; [auto|]. split; [auto|]. split; [intros tr' x mo' (E & -> & ->); auto| intros ? []].
  - intros tr a s' (-> & -> & ->). apply detio_ret. cbn. auto.
Qed.

#[using="Type"] Lemma upd_so_det : forall f st mo, detio (upd_so f st) mo (fun tr _ s' => tr = [] /\ s' = set_so (f (get_so st)) st).
Proof. intros f st mo. unfold upd_so, Stdio.upd_so. apply detio_upd. auto. Qed.

#[using="get_set st_sub st_same rd_so"] Lemma stdout_stdio_write_WR0 : forall s, WR0 (stdout_stdio_write get_so set_so s) s.
Proof.
  intros s st mo Hsz Hlen. unfold stdout_stdio_write. unfold STDOUT_BUFSIZ in Hsz.
  eapply detio_bind; [apply rd_so_det|]. intros tr a s' (-> & -> & ->). cbn [app].
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>43353373554.167371729852.16 00000100;SS3Hsz4Hlen".
eapply detio_bind; [apply stdio_write_det; unfold STDOUT_BUFSIZ, WRITE_MAX, PIECE_MAX in *; lia|]. intros tr' [] s'' [-> ->]. cbn [app].
  apply detio_upd. rewrite get_set. cbn [so_buf]. split; [|reflexivity].
  exists (mkStdout true [] (so_lbf_nl (get_so st)) (so_first (get_so st))). split; [reflexivity|].
  split; [reflexivity|]. split; [cbn; unfold zlength, STDOUT_BUFSIZ; cbn; lia|].
  cbn [so_buf]. fold (E1 (so_buf (get_so st) ++ s)). rewrite E1_app, E1_nil, !app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st_sub st_same"] Lemma ioctl_det : forall st mo,
  detio ((r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
          match r with
          | SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
          | SVal _ => munr
          end) st) mo
        (fun tr _ s' => tr = [] /\ s' = set_so (mkStdout (so_active (get_so st)) (so_buf (get_so st)) false (so_first (get_so st))) st).
Proof.
  intros st mo. eapply (detio_bind _ _ st mo (fun tr a s2 => tr = [] /\ a = SErr ENOTTY /\ s2 = st)).
  - eapply (detio_sys (NIoctl 1 TIOCGWINSZ) dec_ioctl st mo (efferr ENOTTY) [] (SErr ENOTTY)).
    + apply st_same; [cbn; tauto|]. cbn. auto.
    + apply dec_plain_err. Local Ltac2 Set LiaHints.tbl := fun () => "0010>31841965958.13000001S".
unfold ENOTTY; lia.
    + intros rsp' mo' evs' Hst'. apply st_sub in Hst'; [|cbn; tauto]. destruct Hst' as (-> & -> & ->). auto.
    + exact I.
    + auto.
  - intros tr a s2 (-> & -> & ->). cbn [app]. apply upd_so_det.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="get_set set_set set_get st_sub st_same upd_so rd_so"] Lemma stdout_writefn_WR0 : forall s, WR0 (stdout_writefn get_so set_so s) s.
Proof.
  intros s st mo Hsz Hlen. unfold stdout_writefn.
  eapply detio_bind; [apply rd_so_det|]. intros tr a s1 (-> & -> & ->). cbn [app].
  eapply detio_bind with (P := fun tr _ s' => tr = [] /\ exists so', s' = set_so so' st /\ so_buf so' = so_buf (get_so st)).
  - destruct (so_first (get_so st)).
    + eapply detio_bind; [apply upd_so_det|]. intros tr [] s' [-> ->]. cbn [app].
      eapply detio_mono; [apply ioctl_det|]. intros tr2 [] s2 [-> ->]. split; [reflexivity|].
      rewrite get_set, set_set. eexists. split; [reflexivity|]. reflexivity.
    + apply detio_ret. split; [reflexivity|]. exists (get_so st). rewrite set_get. auto.
  - intros tr [] s' (-> & so' & -> & Hb). cbn [app].
    eapply detio_mono; [apply stdout_stdio_write_WR0; [rewrite get_set, Hb; exact Hsz| exact Hlen]|].
    intros tr2 [] s2 [(so2 & -> & Ha2 & Hs2 & Heq) Hb2]. rewrite set_set, get_set in *. rewrite Hb in Heq.
    split; [exists so2; auto| exact Hb2].
Qed.

#[using="Type"] Lemma WR0_WR : forall m bs, WR0 m bs -> WR m bs.
Proof. intros m bs H s mo _ Hsz Hlen. eapply detio_mono; [apply H; assumption|]. intros tr u s' [Hp _]. exact Hp. Qed.

#[using="Type"] Lemma skipn_le_length : forall (n : nat) (l : list Z), (length (skipn n l) <= length l)%nat.
Proof. intros. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>64146793380.13000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="get_set set_set set_get st_sub st_same upd_so rd_so"] Lemma stdout_fwritex_post : forall s st mo,
  so_inv (get_so st) -> zlength s <= PIECE_MAX ->
  detio (stdout_fwritex get_so set_so s st) mo (wr_post st (so_buf (get_so st)) s).
Proof.
  intros s st mo [Hact Hsz] Hlen. unfold stdout_fwritex. unfold STDOUT_BUFSIZ in *.
  (* [comment removed for export] *)
  eapply detio_bind with (P := fun tr _ s1 => tr = [] /\ exists so1, s1 = set_so so1 st /\ so_active so1 = true /\ so_buf so1 = so_buf (get_so st)).
  { unfold stdout_towrite. eapply detio_mono; [apply upd_so_det|]. intros tr [] s1 [-> ->]. split; [reflexivity|].
    destruct (so_active (get_so st)) eqn:Ea.
    - exists (get_so st). auto.
    - eexists. split; [reflexivity|]. split; [reflexivity|]. cbn. symmetry. apply Hact. reflexivity. }
  intros tr [] s1 (-> & so1 & -> & Ha1 & Hb1). cbn [app].
  eapply detio_bind; [apply rd_so_det|]. intros tr2 a s2 (-> & -> & ->). cbn [app]. rewrite get_set.
  destruct (Z.ltb_spec (1024 - zlength (so_buf so1)) (zlength s)) as [Hbig|Hsmall]; [|rewrite Hb1 in Hsmall].
  - eapply detio_mono; [apply (WR0_WR _ _ (stdout_writefn_WR0 s)); rewrite ?get_set; [exact Ha1| rewrite Hb1; exact Hsz| exact Hlen]|].
    intros tr3 [] s3 (so3 & -> & Ha3 & Hs3 & Heq3). exists so3. rewrite set_set, get_set, Hb1 in *. auto.
  - destruct (so_lbf_nl so1).
    + set (i := after_last_nl s).
      eapply detio_bind with (P := fun tr3 _ s3 => exists so3, s3 = set_so so3 st /\ so_active so3 = true
            /\ tr3 ++ E1 (so_buf so3) = E1 (so_buf (get_so st)) ++ E1 (firstn (Z.to_nat i) s)
            /\ zlength (so_buf so3) + zlength (skipn (Z.to_nat i) s) <= 1024).
      * destruct (Z.ltb_spec 0 i).
        -- Local Ltac2 Set LiaHints.tbl := fun () => "0060>17779049769.233220250820.27 41303976697.3065911253395.237367535038.21 7378025562.23 00000300900D00L00T00\S1HS4Hle3S6Hsmall2H0S4Hlen1HS6HsmallS6Hsmall".
eapply detio_mono; [apply stdout_writefn_WR0; rewrite ?get_set; [rewrite Hb1; exact Hsz| unfold zlength in *; rewrite firstn_length; lia]|].
           intros tr3 [] s3 [(so3 & -> & Ha3 & Hs3 & Heq3) Hb3]. rewrite set_set, get_set in *. rewrite Hb1 in Heq3.
           exists so3. splits; auto. rewrite Hb3. unfold zlength in *. cbn. pose proof (skipn_le_length (Z.to_nat i) s). lia.
        -- apply detio_ret. exists so1. replace (Z.to_nat i) with 0%nat by lia. rewrite firstn_O, skipn_O, Hb1, E1_nil, app_nil_r. cbn [app]. splits; auto. lia.
      * intros tr3 [] s3 (so3 & -> & Ha3 & Heq3 & Hle3). eapply detio_mono; [apply upd_so_det|]. intros tr4 [] s4 [-> ->].
        rewrite get_set, set_set, app_nil_r. eexists. split; [reflexivity|]. cbn [so_active so_buf]. split; [exact Ha3|].
        split; [rewrite zlength_app_; unfold STDOUT_BUFSIZ; lia|].
        rewrite E1_app, app_assoc, Heq3, <- app_assoc, <- E1_app, firstn_skipn. reflexivity.
    + eapply detio_mono; [apply upd_so_det|]. intros tr3 [] s3 [-> ->]. rewrite get_set, set_set.
      eexists. split; [reflexivity|]. cbn [so_active so_buf]. split; [exact Ha1|]. rewrite Hb1.
      split; [rewrite zlength_app_; unfold STDOUT_BUFSIZ; lia|]. rewrite E1_app. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="get_set set_set set_get st_sub st_same upd_so rd_so"] Lemma out_pieces_post : forall ps st mo,
  so_active (get_so st) = true -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> zlength (concat ps) <= PIECE_MAX ->
  detio (out_pieces get_so set_so ps st) mo (wr_post st (so_buf (get_so st)) (concat ps)).
Proof.
  induction ps as [|p ps IH]; intros st mo Ha Hsz Hlen; cbn [out_pieces concat].
  - apply detio_ret. exists (get_so st). rewrite set_get, E1_nil, app_nil_r. auto.
  - cbn in Hlen. rewrite zlength_app_ in Hlen. pose proof (Zle_0_nat (length p)). pose proof (Zle_0_nat (length (concat ps))). unfold zlength in Hlen, H, H0.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>36594627246.2636623038549.2100000800AS4Hlen1HS4Hlen2H0".
eapply detio_bind; [apply stdout_fwritex_post; [split; [rewrite Ha; discriminate| exact Hsz]| unfold zlength; lia]|].
    intros tr [] s1 (so1 & -> & Ha1 & Hs1 & Heq1).
    eapply detio_mono; [apply IH; rewrite ?get_set; [exact Ha1| exact Hs1| unfold zlength; lia]|].
    intros tr2 [] s2 (so2 & -> & Ha2 & Hs2 & Heq2). rewrite set_set, get_set in *. exists so2. splits; auto.
    rewrite E1_app, app_assoc, <- Heq1, <- app_assoc, Heq2, app_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="get_set set_set set_get st_sub st_same upd_so rd_so"] Lemma stdout_vprintf_post : forall ps st mo,
  so_inv (get_so st) -> zlength (concat ps) <= PIECE_MAX ->
  detio (stdout_vprintf get_so set_so ps st) mo (wr_post st (so_buf (get_so st)) (concat ps)).
Proof.
  intros ps st mo [Hact Hsz] Hlen. unfold stdout_vprintf.
  eapply detio_bind with (P := fun tr _ s1 => tr = [] /\ exists so1, s1 = set_so so1 st /\ so_active so1 = true /\ so_buf so1 = so_buf (get_so st)).
  { unfold stdout_towrite. eapply detio_mono; [apply upd_so_det|]. intros tr [] s1 [-> ->]. split; [reflexivity|].
    destruct (so_active (get_so st)) eqn:Ea.
    - exists (get_so st). auto.
    - eexists. split; [reflexivity|]. split; [reflexivity|]. cbn. symmetry. apply Hact. reflexivity. }
  intros tr [] s1 (-> & so1 & -> & Ha1 & Hb1). cbn [app].
  eapply detio_mono; [apply out_pieces_post; rewrite ?get_set; [exact Ha1| rewrite Hb1; exact Hsz| exact Hlen]|].
  intros tr2 [] s2 (so2 & -> & Ha2 & Hs2 & Heq2). rewrite get_set, Hb1 in Heq2. exists so2. rewrite set_set. auto.
Qed.

#[using="Type"] Lemma zlength_nil_inv {A} (l : list A) : zlength l <= 0 -> l = [].
Proof. unfold zlength. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8825004492.14000001S".
destruct l; cbn; [reflexivity| lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="get_set set_set set_get st_sub st_same upd_so rd_so"] Lemma stdout_exit_flush_post : forall st mo, so_inv (get_so st) ->
  detio (stdout_exit_flush get_so set_so st) mo
        (fun tr _ s' => tr = E1 (so_buf (get_so st)) /\ exists so', s' = set_so so' st /\ so_buf so' = []).
Proof.
  intros st mo [Hact Hsz]. unfold stdout_exit_flush.
  eapply detio_bind; [apply rd_so_det|]. intros tr a s1 (-> & -> & ->). cbn [app].
  destruct (Z.ltb_spec 0 (zlength (so_buf (get_so st)))) as [Hpos|Hz].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0010>43353370729.16000001S".
eapply detio_mono; [apply stdout_writefn_WR0; [exact Hsz| unfold zlength, PIECE_MAX, STDOUT_BUFSIZ, INTERNAL_BUFSIZ, WRITE_MAX; cbn; lia]|].
    intros tr2 [] s2 [(so2 & -> & Ha2 & Hs2 & Heq2) Hb2]. rewrite get_set in Hb2. rewrite Hb2, !E1_nil, !app_nil_r in Heq2.
    split; [exact Heq2|]. exists so2. auto.
  - apply detio_ret. rewrite (zlength_nil_inv _ Hz). split; [reflexivity|]. exists (get_so st). rewrite set_get. split; [reflexivity|]. apply zlength_nil_inv. exact Hz.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="st_sub st_same"] Lemma stderr_pieces_det : forall ps buf st mo,
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p <= PIECE_MAX) ps ->
  detio (stderr_pieces (St:=St) buf ps st) mo (fun tr r s' => s' = st /\ zlength r <= INTERNAL_BUFSIZ /\ E2 buf ++ E2 (concat ps) = tr ++ E2 r).
Proof.
  induction ps as [|p ps IH]; intros buf st mo Hb Hps; cbn [stderr_pieces concat].
  - apply detio_ret. unfold E2 at 2. cbn. rewrite app_nil_r. auto.
  - apply Forall_cons_iff in Hps as [Hp Hps]. unfold INTERNAL_BUFSIZ in *.
    destruct (Z.ltb_spec (80 - zlength buf) (zlength p)) as [Hbig|Hsmall].
    + Local Ltac2 Set LiaHints.tbl := fun () => "0030>17147201907.2141071613557.2155197241462.2100000800900@S6HsmallSS2Hb2Hp".
eapply detio_bind; [apply stdio_write_det; unfold STDOUT_BUFSIZ, WRITE_MAX, PIECE_MAX in *; lia|]. intros tr [] s1 [-> ->].
      eapply detio_mono; [apply IH; [unfold zlength, PIECE_MAX, STDOUT_BUFSIZ, INTERNAL_BUFSIZ, WRITE_MAX; cbn; lia| exact Hps]|]. intros tr2 r s2 (-> & Hr & Heq).
      split; [reflexivity|]. split; [exact Hr|]. rewrite E2_nil in Heq. cbn [app] in Heq.
      change (map (WriteEv (Z_to_bv 64 2)) (to_bytes (buf ++ p))) with (E2 (buf ++ p)).
      rewrite !E2_app, <- !app_assoc, Heq. reflexivity.
    + eapply detio_mono; [apply IH; [rewrite zlength_app_; lia| exact Hps]|]. intros tr r s' (-> & Hr & Heq).
      rewrite !E2_app in *. rewrite <- Heq, !app_assoc. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st_sub st_same"] Lemma stderr_fprintf_det : forall ps st mo, Forall (fun p => zlength p <= PIECE_MAX) ps ->
  detio (stderr_fprintf (St:=St) ps st) mo (fun tr _ s' => s' = st /\ tr = E2 (concat ps)).
Proof.
  intros ps st mo Hps. unfold stderr_fprintf.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>41086295017.1559080019236.19000001005SS2Hr".
eapply detio_bind; [apply stderr_pieces_det; [unfold zlength, PIECE_MAX, STDOUT_BUFSIZ, INTERNAL_BUFSIZ, WRITE_MAX; cbn; lia| exact Hps]|].
  intros tr r s' (-> & Hr & Heq). eapply detio_mono; [apply stdio_write_det; unfold zlength, PIECE_MAX, STDOUT_BUFSIZ, INTERNAL_BUFSIZ, WRITE_MAX in *; cbn; lia|].
  intros tr2 [] s2 [-> ->]. split; [reflexivity|]. rewrite app_nil_r. cbn [E2 map to_bytes] in Heq. exact (eq_sym Heq).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st_sub st_same"] Lemma stderr_fwrite_det : forall s st mo, zlength s <= PIECE_MAX ->
  detio (stderr_fwrite (St:=St) s st) mo (fun tr _ s' => s' = st /\ tr = E2 s).
Proof.
  intros s st mo Hlen. unfold stderr_fwrite. destruct (Z.ltb_spec 0 (zlength s)) as [Hp|Hz].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0010>41303968441.16000006S4Hlen".
eapply detio_mono; [apply stdio_write_det; unfold zlength, PIECE_MAX, STDOUT_BUFSIZ, INTERNAL_BUFSIZ, WRITE_MAX in *; cbn; lia|]. intros tr [] s' [-> ->]. auto.
  - apply detio_ret. rewrite (zlength_nil_inv _ Hz). auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End StdioChar.

Local Open Scope list_scope. Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition diag_pieces (d : diag_msg) : list (list Z) :=
  match d with
  | DUsage a => pieces_usage a
  | DCannotOpen p => pieces_cannot_open p
  | DReadError p => pieces_read_error p
  | DOom => pieces_oom
  | DTooBig => pieces_too_big
  | DShortHdr => pieces_short_hdr
  | DCfgOverrun => pieces_cfg_overrun
  end.
Definition diag_text (d : diag_msg) : list Z := concat (diag_pieces d).

Definition diag_short (d : diag_msg) : Prop :=
  match d with
  | DUsage a | DCannotOpen a | DReadError a => zlength a <= PIECE_MAX
  | _ => True
  end.

Lemma digits_aux_length : forall f n acc, (length (digits_aux f n acc) <= f + length acc)%nat.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=24928963119.25147600765.4 61848453818.4000001005006SS2IHS".
induction f as [|f IH]; intros n acc; cbn [digits_aux]; [lia|].
  destruct (n =? 0); [cbn; lia|]. specialize (IH (n / 10) (48 + n mod 10 :: acc)). cbn in IH. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma fmt_u_length : forall n, (length (fmt_u n) <= 20)%nat.
Proof. intros n. unfold fmt_u. pose proof (digits_aux_length 20 n []). cbn [length Nat.add] in H. exact H. Qed.
Lemma pieces_pct_d_length : forall v, zlength (concat (pieces_pct_d v)) <= 22.
Proof.
  intros v. unfold pieces_pct_d, zlength. Local Ltac2 Set LiaHints.tbl := fun () => "0030=13934899620.127157662442.349846576849.300000100700=SS1H2H0S1H2H0".
destruct (v =? 0); [cbn; lia|].
  pose proof (fmt_u_length (-v)). pose proof (fmt_u_length v).
  destruct (v <? 0); cbn [concat app]; cbn [length]; rewrite length_app; cbn [length]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section IOS.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall v s, get_so (set_so v s) = v.
Hypothesis set_set : forall v w s, set_so v (set_so w s) = set_so v s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Hypothesis st_sub : forall n mo r mo' e, ~ nf_node n -> stp n mo r mo' e -> nstep n mo r mo' e.   (* [comment removed for export] *)
Hypothesis st_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stp n mo r mo e.
Local Notation detio := (detio (stp:=stp)).

#[using="st_sub st_same"] Lemma s_diag_det : forall d (st : St) mo, diag_short d ->
  detio (s_diag d st) mo (fun tr _ s' => s' = st /\ tr = E2 (diag_text d)).
Proof.
  intros d st mo Hd. destruct d; cbn [s_diag]; cbn in Hd; unfold diag_text; cbn [diag_pieces].
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>2978566891.13 34344364739.1343365956344.1243365956344.1352521273649.1362686943062.1262686943062.1300000400800900:00;00<00=S2HdS2HdSSSSS".
1,2,3,5: apply (stderr_fprintf_det st_sub st_same); unfold pieces_usage, pieces_cannot_open, pieces_read_error, pieces_too_big;
       repeat (apply Forall_cons || apply Forall_nil); unfold zlength, PIECE_MAX in *; cbn; lia.
  all: eapply detio_mono; [apply (stderr_fwrite_det st_sub st_same); unfold zlength, PIECE_MAX; cbn; lia|]; intros tr [] s' [-> ->]; auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="get_set set_set set_get st_sub st_same"] Lemma s_emit_post : forall v (st : St) mo, so_inv (get_so st) ->
  detio (s_emit get_so set_so v st) mo (wr_post set_so st (so_buf (get_so st)) (concat (pieces_pct_d v))).
Proof.
  intros v st mo Hinv. unfold s_emit.
  apply (stdout_vprintf_post get_so set_so get_set set_set set_get st_sub st_same); [exact Hinv|].
  pose proof (pieces_pct_d_length v). unfold PIECE_MAX. Local Ltac2 Set LiaHints.tbl := fun () => "0010>53689065514.14000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End IOS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DetSim.
Context {StG StC : Type} (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.

#[using="Type"] Lemma fsim_of_detio {A B} (R : rel StG StC) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel StG StC) :
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StdioSim.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let d0 : St -> list event := fun _ => [].
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis stepG_sub : forall n mo r mo' e, ~ nf_node n -> stepG n mo r mo' e -> nstep n mo r mo' e.   (* [comment removed for export] *)
Hypothesis stepG_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stepG n mo r mo e.
Variable R : rel St St.
Hypothesis HRget : forall sG moG sC moC, R sG moG sC moC -> get_so sG = get_so sC.
Hypothesis HRset : forall sG moG sC moC v, R sG moG sC moC -> R (set_so v sG) moG (set_so v sC) moC.
Local Notation fsimeq := (fsimeq d0 d0 stepG).
Local Notation fsim := (fsim d0 d0 stepG).

Let upd_so := (upd_so get_so set_so).
Let rd_so := (rd_so (St:=St) get_so).
Local Ltac ret_same := apply fsimeq_ret; intros ? ? ? ? HH; exact HH.

#[using="HRget"] Lemma rd_so_sim : fsimeq R rd_so rd_so (fun _ => R).
Proof.
  unfold rd_so, Stdio.rd_so, fsimeq. eapply fsim_bind; [apply fsim_get|]. intros a b. cbn beta.
  apply fsim_ret. intros sG moG sC moC (-> & -> & HR). split; [apply (HRget _ _ _ _ HR)| exact HR].
Qed.

#[using="HRget HRset"] Lemma upd_so_sim : forall f, fsimeq R (upd_so f) (upd_so f) (fun _ => R).
Proof.
  intros f. unfold upd_so, Stdio.upd_so, fsimeq. apply fsim_upd. intros sG moG sC moC HR.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. rewrite (HRget _ _ _ _ HR). apply HRset. exact HR.
Qed.

#[using="stepG_sub stepG_same"] Lemma stdio_write_sim : forall fd buf s, fsimeq R (stdio_write fd buf s) (stdio_write fd buf s) (fun _ => R).
Proof.
  intros fd buf s. destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)) as [Hbig|Hok].
  - unfold stdio_write. replace (WRITE_MAX <? zlength buf + zlength s) with true by (symmetry; apply Z.ltb_lt; exact Hbig). apply fsimeq_munr.
  - unfold fsimeq. apply fsim_of_detio. intros sG moG sC moC HR.
    eexists _, _. split; [apply (stdio_write_det stepG_sub stepG_same); exact Hok|]. split; [apply (stdio_write_det (stp:=nstep) ltac:(auto) ltac:(auto)); exact Hok|].
    intros trG [] sG' trC [] sC' [-> ->] [-> ->]. exists (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))). unfold d0. rewrite !app_nil_r. cbn [app]. auto.
Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma stdout_stdio_write_sim : forall s, fsimeq R (stdout_stdio_write get_so set_so s) (stdout_stdio_write get_so set_so s) (fun _ => R).
Proof.
  intros s. unfold stdout_stdio_write.
  eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  eapply fsimeq_seq; [apply stdio_write_sim|]. intros _. apply upd_so_sim.
Qed.

#[using="stepG_sub"] Lemma ioctl_sim : fsimeq R (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) (fun _ => R).
Proof.
  unfold fsimeq. apply fsim_sys. intros sG moG sC moC HR. split.
  - intros rspG moG' evs a Hst Hd. apply stepG_sub in Hst; [|cbn; tauto]. destruct Hst as (-> & -> & ->). split; [left; reflexivity|]. exists (efferr ENOTTY), moC, a. cbn. auto.
  - intros code moG' Hx. destruct Hx.
Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma stdout_writefn_sim : forall s, fsimeq R (stdout_writefn get_so set_so s) (stdout_writefn get_so set_so s) (fun _ => R).
Proof.
  intros s. unfold stdout_writefn.
  eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  eapply fsimeq_seq.
  - apply fsimeq_if; intros _; [|ret_same].
    eapply fsimeq_seq; [apply upd_so_sim|]. intros _.
    eapply fsimeq_bind; [apply ioctl_sim|]. intros [e|v]; [apply upd_so_sim| apply fsimeq_munr].
  - intros _. apply stdout_stdio_write_sim.
Qed.

#[using="HRget HRset upd_so"] Lemma stdout_towrite_sim : fsimeq R (stdout_towrite get_so set_so) (stdout_towrite get_so set_so) (fun _ => R).
Proof. unfold stdout_towrite. apply upd_so_sim. Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma stdout_fwritex_sim : forall s, fsimeq R (stdout_fwritex get_so set_so s) (stdout_fwritex get_so set_so s) (fun _ => R).
Proof.
  intros s. unfold stdout_fwritex.
  eapply fsimeq_seq; [apply stdout_towrite_sim|]. intros _.
  eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  apply fsimeq_if; intros _; [apply stdout_writefn_sim|].
  apply fsimeq_if; intros _; [|apply upd_so_sim].
  eapply fsimeq_seq; [apply fsimeq_if; intros _; [apply stdout_writefn_sim| ret_same]|]. intros _. apply upd_so_sim.
Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma out_pieces_sim : forall ps, fsimeq R (out_pieces get_so set_so ps) (out_pieces get_so set_so ps) (fun _ => R).
Proof.
  induction ps as [|p ps IH]; cbn [out_pieces]; [ret_same|].
  eapply fsimeq_seq; [apply stdout_fwritex_sim|]. intros _. apply IH.
Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma stdout_vprintf_sim : forall ps, fsimeq R (stdout_vprintf get_so set_so ps) (stdout_vprintf get_so set_so ps) (fun _ => R).
Proof. intros ps. unfold stdout_vprintf. eapply fsimeq_seq; [apply stdout_towrite_sim|]. intros _. apply out_pieces_sim. Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma stdout_exit_flush_sim : fsimeq R (stdout_exit_flush get_so set_so) (stdout_exit_flush get_so set_so) (fun _ => R).
Proof.
  unfold stdout_exit_flush. eapply fsimeq_bind; [apply rd_so_sim|]. intros so.
  apply fsimeq_if; intros _; [apply stdout_writefn_sim| ret_same].
Qed.

#[using="stepG_sub stepG_same"] Lemma stderr_pieces_sim : forall ps buf, fsimeq R (stderr_pieces (St:=St) buf ps) (stderr_pieces (St:=St) buf ps) (fun _ => R).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [ret_same|].
  apply fsimeq_if; intros _; [|apply IH].
  eapply fsimeq_seq; [apply stdio_write_sim|]. intros _. apply IH.
Qed.

#[using="stepG_sub stepG_same"] Lemma stderr_fprintf_sim : forall ps, fsimeq R (stderr_fprintf (St:=St) ps) (stderr_fprintf (St:=St) ps) (fun _ => R).
Proof. intros ps. unfold stderr_fprintf. eapply fsimeq_bind; [apply stderr_pieces_sim|]. intros buf. apply stdio_write_sim. Qed.

#[using="stepG_sub stepG_same"] Lemma stderr_fwrite_sim : forall s, fsimeq R (stderr_fwrite (St:=St) s) (stderr_fwrite (St:=St) s) (fun _ => R).
Proof. intros s. unfold stderr_fwrite. apply fsimeq_if; intros _; [apply stdio_write_sim| ret_same]. Qed.

(* [comment removed for export] *)
#[using="stepG_sub stepG_same"] Lemma s_diag_sim : forall d, fsimeq R (s_diag d) (s_diag d) (fun _ => R).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_sim | apply stderr_fwrite_sim]. Qed.

#[using="stepG_sub stepG_same HRget HRset upd_so rd_so"] Lemma s_emit_sim : forall v, fsimeq R (s_emit get_so set_so v) (s_emit get_so set_so v) (fun _ => R).
Proof. intros v. unfold s_emit. apply stdout_vprintf_sim. Qed.
End StdioSim.
