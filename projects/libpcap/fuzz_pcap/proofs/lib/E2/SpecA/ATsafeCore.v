(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA NodesSil NodesMmSh NodesAS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ProtoS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Core.
Variable NMAX : nat.
Variable SHM : list (Z * Z).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition postT (R : Type) : Type := R -> footprint -> alw -> Model -> Prop.

Fixpoint TS {R} (RNG : footprint) (A : alw) (t : itree node R) (mo : Model) (Q : postT R) {struct t} : Prop :=
  acct_ok NMAX RNG A mo /\
  match t with
  | Ret r => Q r RNG A mo
  | Vis n k => nsafeA NMAX SHM n mo /\
      forall rsp mo' evs, nstepA n mo rsp mo' evs ->
        exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q
  end.

#[using="Type"] Lemma TS_acct : forall {R} RNG A (t : itree node R) mo Q, TS RNG A t mo Q -> acct_ok NMAX RNG A mo.
Proof. intros R RNG A [r|n k] mo Q H; exact (proj1 H). Qed.

#[using="Type"] Lemma TS_unfold_vis : forall {R} RNG A n (k : resp -> itree node R) mo Q,
  TS RNG A (Vis n k) mo Q <->
  (acct_ok NMAX RNG A mo /\ nsafeA NMAX SHM n mo /\
   forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q).
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TS_tsafeA : forall {R} (t : itree node R) RNG A mo Q,
  TS RNG A t mo Q -> tsafeA nstepA (nsafeA NMAX SHM) fstepS NMAX RNG A t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG A mo Q H; cbn in H |- *.
  - split; [exact (proj1 H)| exact I].
  - destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH. exact HT.
Qed.

#[using="Type"] Lemma TS_mono : forall {R} (t : itree node R) RNG A mo (Q Q' : postT R),
  TS RNG A t mo Q -> (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q r RNG' A' mo' -> Q' r RNG' A' mo') -> TS RNG A t mo Q'.
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG A mo Q Q' H HQ; cbn in H |- *.
  - destruct H as [HA HQ1]. split; [exact HA| apply HQ; assumption].
  - destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HQ].
Qed.

#[using="Type"] Lemma TS_ret : forall {R} (r : R) RNG A mo (Q : postT R),
  acct_ok NMAX RNG A mo -> Q r RNG A mo -> TS RNG A (Ret r) mo Q.
Proof. intros. cbn. split; assumption. Qed.

#[using="Type"] Lemma TS_bind : forall {X Y} (t : itree node X) (k : X -> itree node Y) RNG A mo (Q1 : postT X) (Q : postT Y),
  TS RNG A t mo Q1 ->
  (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 r RNG' A' mo' -> TS RNG' A' (k r) mo' Q) ->
  TS RNG A (bind node t k) mo Q.
Proof.
  intros X Y t. induction t as [r|n k0 IH]; intros k RNG A mo Q1 Q H HK; cbn in H.
  - destruct H as [HA H1]. cbn. apply HK; assumption.
  - destruct H as (HA & HS & HC). cbn. split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HC rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HK].
Qed.

(* [comment removed for export] *)
Definition EQ {X} (Q : postT X) : postT (exc X) :=
  fun r RNG A mo => match r with Unr => True | Ok x => Q x RNG A mo end.

#[using="Type"] Lemma TS_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) RNG A mo (Q1 : postT X) (Q : postT Y),
  TS RNG A t mo (EQ Q1) ->
  (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 x RNG' A' mo' -> TS RNG' A' (f x) mo' (EQ Q)) ->
  TS RNG A (ebind t f) mo (EQ Q).
Proof.
  intros X Y t f RNG A mo Q1 Q H HK. unfold ebind. eapply TS_bind; [exact H|].
  intros [|x] RNG' A' mo' HA H1; cbn in H1.
  - apply TS_ret; [exact HA| exact I].
  - apply HK; assumption.
Qed.

#[using="Type"] Lemma TS_ret_ok : forall {X} (x : X) RNG A mo (Q : postT X),
  acct_ok NMAX RNG A mo -> Q x RNG A mo -> TS RNG A (Ret (Ok x)) mo (EQ Q).
Proof. intros. apply TS_ret; assumption. Qed.

#[using="Type"] Lemma TS_ret_unr : forall {X} RNG A mo (Q : postT X), acct_ok NMAX RNG A mo -> TS RNG A (Ret Unr) mo (EQ Q).
Proof. intros. apply TS_ret; [assumption| exact I]. Qed.

#[using="Type"] Lemma TS_EQ_mono : forall {X} (t : itree node (exc X)) RNG A mo (Q Q' : postT X),
  TS RNG A t mo (EQ Q) -> (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q x RNG' A' mo' -> Q' x RNG' A' mo') ->
  TS RNG A t mo (EQ Q').
Proof. intros X t RNG A mo Q Q' H HQ. eapply TS_mono; [exact H|]. intros [|x] RNG' A' mo' HA H1; cbn in *; [exact I| apply HQ; assumption]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma acct_ok_vm : forall RNG A mo mo',
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
  acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
  intros RNG A mo mo' E1 E2 E3 (F & L & R). unfold acct_ok. rewrite E2, E1.
  split; [exact F|]. split; [exact L|]. unfold nonlazy_bytes in *. rewrite E1, E2. exact R.
Qed.

#[using="Type"] Lemma acct_ok_with_fds : forall RNG A f mo, acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A (with_fds f mo).
Proof. intros. eapply acct_ok_vm; [ | | | eassumption]; reflexivity. Qed.
#[using="Type"] Lemma acct_ok_with_tid : forall RNG A t mo, acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A (with_tid t mo).
Proof. intros. eapply acct_ok_vm; [ | | | eassumption]; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma acct_ok_vmst : forall RNG A mo mo', m_vm mo' = m_vm mo -> acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
  intros RNG A mo mo' E H. apply (acct_ok_vm RNG A mo mo'); [| | | exact H]; unfold m_vmmaps, m_vm_lazy, m_vm_materialized; rewrite E; reflexivity.
Qed.

Definition vmfree_node (n : node) : Prop := fsnode n \/ exists a, n = NPeek a.

#[using="Type"] Lemma acct_ok_io : forall n mo eff mo' evs RNG A,
  vmfree_node n -> nstep n mo eff mo' evs -> acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
  intros n mo eff mo' evs RNG A [Hfs|(a & ->)] Hst HA.
  - eapply acct_ok_vmst; [| exact HA]. eapply nstep_vm_same; eassumption.
  - cbn [nstep] in Hst. destruct Hst as (-> & _). exact HA.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TS_io : forall {R} n (k : resp -> itree node R) RNG A mo (Q : postT R),
  vmfree_node n -> nsafe n mo -> acct_ok NMAX RNG A mo ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> acct_ok NMAX RNG A mo' -> TS RNG A (k rsp) mo' Q) ->
  TS RNG A (Vis n k) mo Q.
Proof.
  intros R n k RNG A mo Q Hio Hns HA HK. cbn. split; [exact HA|]. split.
  { split; [exact Hns|]. split; destruct Hio as [Hfs|(a & ->)]; try (destruct n; cbn in Hfs |- *; try contradiction; exact I); exact I. }
  intros rsp mo' evs Hst. unfold nstepA in Hst.
  exists RNG, A. split; [apply fstepS_id; destruct Hio as [Hfs|(a & ->)]; [destruct n; cbn in Hfs |- *; try contradiction; exact I| exact I]|].
  split; [apply alw_le_refl|]. apply (HK rsp mo' evs); [exact Hst| eapply (acct_ok_io n mo rsp mo' evs); eauto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Triples.
Context {St : Type}.

Definition preT : Type := footprint -> alw -> St -> Model -> Prop.
Definition postM (X : Type) : Type := X -> footprint -> alw -> St -> Model -> Prop.

(* [comment removed for export] *)
Definition MQ {X} (Q : postM X) : postT (exc (X * St)) := EQ (fun p RNG A mo => Q (fst p) RNG A (snd p) mo).

Definition TSM {X} (P : preT) (m : M St X) (Q : postM X) : Prop :=
  forall RNG A s mo, P RNG A s mo -> TS RNG A (m s) mo (MQ Q).

#[using="Type"] Lemma TSM_conseq : forall {X} (P P' : preT) (m : M St X) (Q Q' : postM X),
  TSM P m Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) ->
  (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> TSM P' m Q'.
Proof.
  intros X P P' m Q Q' H HP HQ RNG A s mo Hp. eapply TS_EQ_mono; [apply H; apply HP; exact Hp|].
  intros [x s'] RNG' A' mo' HA H1. cbn in *. apply HQ; assumption.
Qed.
#[using="Type"] Lemma TSM_pre : forall {X} (P P' : preT) (m : M St X) (Q : postM X),
  TSM P m Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) -> TSM P' m Q.
Proof. intros. eapply TSM_conseq; eauto. Qed.
#[using="Type"] Lemma TSM_post : forall {X} (P : preT) (m : M St X) (Q Q' : postM X),
  TSM P m Q -> (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> TSM P m Q'.
Proof. intros. eapply TSM_conseq; eauto. Qed.

#[using="Type"] Lemma TSM_ret : forall {X} (x : X) (P : preT) (Q : postM X),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo /\ Q x RNG A s mo) -> TSM P (mret x) Q.
Proof. intros X x P Q H RNG A s mo Hp. destruct (H _ _ _ _ Hp) as [HA HQ]. apply TS_ret_ok; [exact HA| exact HQ]. Qed.

#[using="Type"] Lemma TSM_munr : forall {X} (P : preT) (Q : postM X),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) -> TSM P (munr (A:=X)) Q.
Proof. intros X P Q H RNG A s mo Hp. apply TS_ret_unr. apply (H _ _ _ _ Hp). Qed.

#[using="Type"] Lemma TSM_bind : forall {X Y} (P : preT) (m : M St X) (f : X -> M St Y) (Q1 : postM X) (Q : postM Y),
  TSM P m Q1 -> (forall x, TSM (fun RNG A s mo => acct_ok NMAX RNG A mo /\ Q1 x RNG A s mo) (f x) Q) -> TSM P (mbind m f) Q.
Proof.
  intros X Y P m f Q1 Q Hm Hf RNG A s mo Hp. unfold mbind. eapply TS_ebind; [apply Hm; exact Hp|].
  intros [x s'] RNG' A' mo' HA H1. cbn in H1. apply Hf. split; assumption.
Qed.

#[using="Type"] Lemma TSM_get : forall (P : preT),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  TSM P mget (fun s' RNG A s mo => s' = s /\ P RNG A s mo).
Proof. intros P H RNG A s mo Hp. apply TS_ret_ok; [apply (H _ _ _ _ Hp)|]. cbn. auto. Qed.

#[using="Type"] Lemma TSM_upd : forall (f : St -> St) (P : preT),
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  TSM P (mupd f) (fun _ RNG A s' mo => exists s, s' = f s /\ P RNG A s mo).
Proof. intros f P H RNG A s mo Hp. apply TS_ret_ok; [apply (H _ _ _ _ Hp)|]. cbn. eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TSM_bind_get : forall {X} (P : preT) (k : St -> M St X) (Q : postM X),
  (forall s0, TSM (fun RNG A s mo => s = s0 /\ P RNG A s mo) (k s0) Q) ->
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  TSM P (mbind mget k) Q.
Proof.
  intros X P k Q Hk HA RNG A s mo Hp. unfold mbind, mget. cbn. apply Hk. auto.
Qed.

#[using="Type"] Lemma TSM_if : forall {X} (b : bool) (P : preT) (m1 m2 : M St X) (Q : postM X),
  (b = true -> TSM P m1 Q) -> (b = false -> TSM P m2 Q) -> TSM P (if b then m1 else m2) Q.
Proof. intros X [|] P m1 m2 Q H1 H2; [apply H1| apply H2]; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TSM_pure : forall {X} (P : preT) (phi : Prop) (m : M St X) (Q : postM X),
  (forall RNG A s mo, P RNG A s mo -> phi) -> (phi -> TSM P m Q) -> TSM P m Q.
Proof. intros X P phi m Q Hphi H RNG A s mo Hp. apply (H (Hphi _ _ _ _ Hp)). exact Hp. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TSM_exI : forall {X T} (P : T -> preT) (m : M St X) (Q : postM X),
  (forall x, TSM (P x) m Q) -> TSM (fun RNG A s mo => exists x, P x RNG A s mo) m Q.
Proof. intros X T P m Q H RNG A s mo (x & Hp). apply (H x). exact Hp. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TSM_loop : forall {X R} (I : X -> preT) (Q : postM R) (body : X -> M St (X + R)),
  (forall x, TSM (I x) (body x) (fun r RNG A s mo => match r with inl x' => I x' RNG A s mo | inr r => Q r RNG A s mo end)) ->
  (forall x RNG A s mo, I x RNG A s mo -> acct_ok NMAX RNG A mo) ->
  forall fuel x, TSM (I x) (mloop fuel body x) Q.
Proof.
  intros X R I Q body HB HA fuel. induction fuel as [|fuel IH]; intros x.
  - cbn. apply TSM_munr. apply HA.
  - cbn [mloop]. eapply TSM_bind; [apply HB|]. intros [x'|r].
    + eapply TSM_pre; [apply IH|]. cbv beta. intros RNG A s mo [_ H]; exact H.
    + apply TSM_ret. cbv beta. intros RNG A s mo [H1 H2]. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma TSM_msys_io : forall {X} n (dec : resp -> option X) (P : preT) (Q : postM X),
  vmfree_node n ->
  (forall RNG A s mo, P RNG A s mo -> nsafe n mo) ->
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
  (forall RNG A s mo rsp mo' evs x, P RNG A s mo -> nstep n mo rsp mo' evs -> dec rsp = Some x -> Q x RNG A s mo') ->
  TSM P (msys n dec) Q.
Proof.
  intros X n dec P Q Hio HS HA HQ RNG A s mo Hp. unfold msys, enode.
  apply TS_io; [exact Hio| apply (HS _ _ _ _ Hp)| apply (HA _ _ _ _ Hp)|].
  intros rsp mo' evs Hst HA'. destruct (dec rsp) as [x|] eqn:E.
  - apply TS_ret_ok; [exact HA'|]. cbn. eapply HQ; eauto.
  - apply TS_ret_unr. exact HA'.
Qed.
End Triples.
End Core.

End CANSEC1.
Arguments TS NMAX SHM {R} RNG A t mo Q.
Arguments TSM NMAX SHM {St X} P m Q.
Arguments MQ {St X} Q.
Arguments EQ {X} Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition abud (A : alw) (k : Z) : Prop :=
  exists L : list word, List.NoDup L /\ Z.of_nat (length L) <= k /\ forall p, A p -> In p L.

#[using="Type"] Lemma abud_mono : forall A k k', abud A k -> k <= k' -> abud A k'.
Proof. intros A k k' (L & N & Hl & HL) Hk. exists L. split; [exact N|]. split; [lia| exact HL]. Qed.

#[using="Type"] Lemma abud_le : forall (A B : alw) k, abud B k -> alw_le A B -> abud A k.
Proof. intros A B k (L & N & Hl & HL) HAB. exists L. split; [exact N|]. split; [exact Hl|]. intros p Hp. apply HL, HAB, Hp. Qed.

(* [comment removed for export] *)
Definition aunion (A : alw) (ps : list word) : alw := fun p => A p \/ In p ps.

#[using="Type"] Lemma aunion_le : forall A ps, alw_le A (aunion A ps).
Proof. intros A ps p H. left; exact H. Qed.
#[using="Type"] Lemma aunion_in : forall A ps p, In p ps -> aunion A ps p.
Proof. intros A ps p H. right; exact H. Qed.

#[using="Type"] Lemma nodup_extend : forall (L ps : list word), List.NoDup L ->
  exists L', List.NoDup L' /\ (length L' <= length L + length ps)%nat /\ (forall p, In p L \/ In p ps -> In p L').
Proof.
  intros L ps N. induction ps as [|q ps IH].
  - exists L. split; [exact N|]. split; [cbn; lia|]. intros p [H|[]]; exact H.
  - destruct IH as (L' & N' & Hlen & HL').
    destruct (in_dec (fun x y => bv_eq_dec _ x y) q L') as [Hin|Hnin].
    + exists L'. split; [exact N'|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [apply HL'; left; exact H| exact Hin| apply HL'; right; exact H].
    + exists (q :: L'). split; [constructor; [exact Hnin| exact N']|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [right; apply HL'; left; exact H| left; reflexivity| right; apply HL'; right; exact H].
Qed.

#[using="Type"] Lemma abud_union : forall A k ps, abud A k -> abud (aunion A ps) (k + Z.of_nat (length ps)).
Proof.
  intros A k ps (L & N & Hl & HL). destruct (nodup_extend L ps N) as (L' & N' & Hlen & HL').
  exists L'. split; [exact N'|]. split; [lia|]. intros p [H|H]; apply HL'; [left; apply HL; exact H| right; exact H].
Qed.

(* [comment removed for export] *)
Fixpoint pages_from (p0 : Z) (n : nat) : list word :=
  match n with O => [] | S n' => Z_to_bv 64 p0 :: pages_from (p0 + 4096) n' end.

#[using="Type"] Lemma pages_from_length : forall p0 n, length (pages_from p0 n) = n.
Proof. intros p0 n. revert p0. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

#[using="Type"] Lemma pages_from_in : forall p0 n (i : nat), (i < n)%nat -> In (Z_to_bv 64 (p0 + 4096 * Z.of_nat i)) (pages_from p0 n).
Proof.
  intros p0 n. revert p0. induction n as [|n IH]; intros p0 i Hi; [lia|]. cbn. destruct i as [|i].
  - left. f_equal. lia.
  - right. replace (p0 + 4096 * Z.of_nat (S i)) with (p0 + 4096 + 4096 * Z.of_nat i) by lia. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition range_pages (lo len : Z) : list word :=
  pages_from (lo / 4096 * 4096) (Z.to_nat ((lo + len - 1) / 4096 - lo / 4096 + 1)).

#[using="Type"] Lemma range_pages_length : forall lo len, 0 <= lo -> 0 < len ->
  Z.of_nat (length (range_pages lo len)) <= len / 4096 + 2.
Proof.
  intros lo len Hlo Hlen. unfold range_pages. rewrite pages_from_length.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod len 4096 ltac:(lia)). pose proof (Z.mod_pos_bound len 4096 ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma range_pages_spec : forall lo len z, 0 <= lo -> lo <= z < lo + len ->
  In (page_base_of z) (range_pages lo len).
Proof.
  intros lo len z Hlo Hz. unfold range_pages, page_base_of, page_size.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod z 4096 ltac:(lia)). pose proof (Z.mod_pos_bound z 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  assert (D1 : lo / 4096 <= z / 4096) by (apply Z.div_le_mono; lia).
  assert (D2 : z / 4096 <= (lo + len - 1) / 4096) by (apply Z.div_le_mono; lia).
  replace (z / 4096 * 4096) with (lo / 4096 * 4096 + 4096 * Z.of_nat (Z.to_nat (z / 4096 - lo / 4096))) by lia.
  apply pages_from_in. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rng_fp_ok_union : forall lz A lo len ps,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> In (page_base_of z) ps) ->
  rng (fp_ok lz (aunion A ps)) lo len.
Proof.
  intros lz A lo len ps Hlo Hhi H. apply rng_fp_ok; [exact Hlo| exact Hhi|]. intros z Hz. right. right. apply H. exact Hz.
Qed.

#[using="Type"] Lemma rng_fp_ok_range : forall lz A lo len, 0 <= lo -> lo + len <= 2^64 ->
  rng (fp_ok lz (aunion A (range_pages lo len))) lo len.
Proof. intros. apply rng_fp_ok_union; auto. intros z Hz. apply range_pages_spec; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rng_fp_ok_allowed : forall lz (A : alw) lo len,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> A (page_base_of z)) -> rng (fp_ok lz A) lo len.
Proof. intros lz A lo len Hlo Hhi H. apply rng_fp_ok; auto. intros z Hz. right. apply H. exact Hz. Qed.
End CANSEC2.
