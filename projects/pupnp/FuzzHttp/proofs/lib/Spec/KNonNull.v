(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KStepK JLedger MBound EquivK EquivAlloc EquivMR.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import KRemapDef.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require KRemap KStepC.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require DriverSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ClfIx Require Import PathX.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MNonNull.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Fixpoint tfol {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> tfol (k rsp) mo' P
  end.

Lemma tfol_mono {R} : forall (t : itree node R) mo (P P' : R -> Model -> Prop),
  tfol t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> tfol t mo P'.
Proof.
  induction t as [r|n k IH]; intros mo P P' H HP; cbn in *; [apply HP; exact H|].
  intros rsp mo' evs ST. eapply IH; [eapply H; exact ST| exact HP].
Qed.

Lemma tfol_bind {A B} : forall (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  tfol t mo (fun a mo1 => tfol (f a) mo1 P) -> tfol (ITree.bind node t f) mo P.
Proof.
  induction t as [r|n k IH]; intros f mo P H; cbn in *; [exact H|].
  intros rsp mo' evs ST. apply IH. eapply H; exact ST.
Qed.

Lemma twf_tfol_conj {R} : forall (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf t mo P -> tfol t mo Q -> twf t mo (fun r mo1 => P r mo1 /\ Q r mo1).
Proof.
  induction t as [r|n k IH]; intros mo P Q HW HF; cbn in *; [split; assumption|].
  destruct HW as [HS HK]. split; [exact HS|]. intros rsp mo' evs ST. apply IH; [eapply HK; exact ST| eapply HF; exact ST].
Qed.

Definition etfol {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  tfol t mo (fun r mo1 => match r with Unr => True | Ok a => Q a mo1 end).

Lemma etfol_ebind {A B} : forall (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etfol t mo (fun a mo1 => etfol (f a) mo1 Q) -> etfol (ebind t f) mo Q.
Proof.
  intros t f mo Q H. unfold etfol, ebind. apply tfol_bind. eapply tfol_mono; [exact H|].
  intros [|a] mo1 Hr; cbn; [exact I| exact Hr].
Qed.

Section MFol.
Context {St : Type}.

Definition mfol {A} (P : assn St) (m : Monad.M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etfol (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

#[using="Type"] Lemma mfol_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mfol P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

#[using="Type"] Lemma mfol_bind {A B} (m : Monad.M St A) (f : A -> Monad.M St B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
  mfol P m Q1 -> (forall a, mfol (Q1 a) (f a) Q) -> mfol P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etfol_ebind. unfold mfol, etfol in Hm.
  eapply tfol_mono; [exact (Hm s mo HP)|]. intros [|[a s1]] mo1 H; cbn in *; [exact I|]. apply Hf. exact H.
Qed.

#[using="Type"] Lemma mfol_conseq {A} (m : Monad.M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mfol P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mfol P' m Q'.
Proof.
  intros H HP HQ s mo HP'. unfold mfol, etfol in H. eapply tfol_mono; [exact (H s mo (HP _ _ HP'))|].
  intros [|[a s1]] mo1 Hr; cbn in *; [exact I| apply HQ; exact Hr].
Qed.

#[using="Type"] Lemma mfol_pre {A} (m : Monad.M St A) (P P' : assn St) (Q : A -> assn St) :
  mfol P m Q -> (forall s mo, P' s mo -> P s mo) -> mfol P' m Q.
Proof. intros; eapply mfol_conseq; eauto. Qed.

#[using="Type"] Lemma mfol_get (P : assn St) : mfol P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

#[using="Type"] Lemma mfol_upd (P : assn St) (f : St -> St) : mfol P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mfol_munr {A} (P : assn St) (Q : A -> assn St) : mfol P munr Q.
Proof. intros s mo _. exact I. Qed.

#[using="Type"] Lemma mfol_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo rsp mo' evs a, P s mo -> nstep n mo rsp mo' evs -> dec rsp = Some a -> Q a s mo') ->
  mfol P (msys n dec) Q.
Proof.
  intros H s mo HP. unfold msys, enode. cbn. intros rsp mo' evs ST.
  destruct (dec rsp) as [a|] eqn:D; cbn; [| exact I]. eapply H; eauto.
Qed.

#[using="Type"] Lemma mfol_pointwise {A} (P : assn St) (m : Monad.M St A) (Q : A -> assn St) :
  (forall s0 mo0, P s0 mo0 -> mfol (fun s mo => s = s0 /\ mo = mo0) m Q) -> mfol P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

#[using="Type"] Lemma mfol_exI {A X} (P : X -> assn St) (m : Monad.M St A) (Q : A -> assn St) :
  (forall x, mfol (P x) m Q) -> mfol (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

#[using="Type"] Lemma mspec_mfol_conj {A} (P1 P2 : assn St) (m : Monad.M St A) (Q1 Q2 : A -> assn St) :
  mspec P1 m Q1 -> mfol P2 m Q2 ->
  mspec (fun s mo => P1 s mo /\ P2 s mo) m (fun a s mo => Q1 a s mo /\ Q2 a s mo).
Proof.
  intros H1 H2 s mo [HP1 HP2]. unfold etwf. eapply twf_mono; [apply twf_tfol_conj; [exact (H1 s mo HP1)| exact (H2 s mo HP2)]|].
  intros [|[a s1]] mo1 [X Y]; cbn in *; [exact X| split; assumption].
Qed.
End MFol.

Definition PKc (e : ev) (wb wm wp : Z) (mo : Model) : Prop :=
  let '(cb, cm, cp) := ecost e in PK false (wb - cb) (wm - cm) (wp - cp) mo.

Definition FP (L : mled) (wb wm wp : Z) (s0 : PState) : assn PState :=
  fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ PK false wb wm wp mo.

Lemma fol_mmap L len prot wb wm wp s0 :
  (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len <= LMAX -> round_up_pg len <= wb -> 1 <= wm ->
  mfol (FP L wb wm wp s0) (ev_step (EMmap 0 len prot MAPF))
       (fun z s mo => is_err z = false /\ PK false (wb - round_up_pg len) (wm - 1) wp mo).
Proof.
  intros Hp Hl Wb Wm. unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
  set (dec := if prot =? PROT_NONE then dec_mmap_none len [] else dec_mmap len []).
  assert (E : (if prot =? 0 then a <- msys (NMmap 0 len prot MAPF) (dec_mmap_none len []);; mret match a with MmErr e => neg_errno e | MmOk x => x end
               else a <- msys (NMmap 0 len prot MAPF) (dec_mmap len []);; mret match a with MmErr e => neg_errno e | MmOk x => x end)
              = (a <- msys (NMmap 0 len prot MAPF) dec ;; mret (mval a) : Monad.M PState Z)).
  { subst dec. change PROT_NONE with 0. destruct (prot =? 0); reflexivity. }
  rewrite E. clear E.
  eapply mfol_bind with (Q1 := fun a s mo => (exists x, a = MmOk x /\ 0 < x /\ x + mmap_len len <= alloc_ceiling_max) /\
                                             PK false (wb - round_up_pg len) (wm - 1) wp mo).
  - apply mfol_sys. intros s mo rsp mo' evs a (-> & K & P) ST D.
    pose proof (PK_mmap false wb wm wp mo rsp mo' evs L _ len prot K P Hl Hp Wb Wm ltac:(intros; discriminate) ST) as P'.
    split; [| exact P'].
    pose proof (mmap_len_bound len ltac:(lia)) as LB. assert (L64 : mmap_len len < 2^64) by (unfold LMAX in Hl; lia).
    destruct Hp as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb] in dec; subst dec.
    + destruct (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) L64 ltac:(constructor) ST) as (_ & _ & x1 & D1 & X1).
      rewrite D1 in D. injection D as <-. destruct x1 as [e1|a1].
      * exfalso. destruct (dec_mmap_none_Some _ _ _ _ D1) as [Hs He].
        exact (PK_mmap_not_refused false wb wm wp mo L _ len PROT_NONE _ _ _ _ K P Hl ltac:(left; reflexivity) Wb ST Hs He).
      * destruct X1 as (AOK & _). apply mmap_addr_ok_true in AOK as [(A1 & A2 & A3) _]. exists a1. auto.
    + destruct (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) L64 ltac:(constructor) ST) as (_ & _ & x1 & D1 & X1).
      rewrite D1 in D. injection D as <-. destruct x1 as [e1|a1].
      * exfalso. destruct (dec_mmap_Some _ _ _ _ D1) as [Hs He].
        exact (PK_mmap_not_refused false wb wm wp mo L _ len PROT_RW _ _ _ _ K P Hl ltac:(right; reflexivity) Wb ST Hs He).
      * destruct X1 as (AOK & _). apply mmap_addr_ok_true in AOK as [(A1 & A2 & A3) _]. exists a1. auto.
  - intros a. apply mfol_ret. intros s mo ((x & -> & X1 & X2) & P). split; [| exact P].
    cbn [mval]. pose proof (mmap_len_bound len ltac:(lia)). apply is_err_small; lia.
Qed.

Lemma fol_brk0 L wb wm wp s0 :
  mfol (FP L wb wm wp s0) (ev_step (EBrk 0)) (fun _ s mo => PK false wb wm wp mo).
Proof.
  unfold ev_step. cbn [Z.eqb].
  eapply mfol_bind with (Q1 := fun (_ : Z) s mo => PK false wb wm wp mo).
  - apply mfol_sys. intros s mo rsp mo' evs a (-> & K & P) ST _. eapply PK_brk_query; [exact P| exact ST].
  - intros a. eapply mfol_bind with (Q1 := fun _ s mo => PK false wb wm wp mo).
    + eapply mfol_conseq; [apply mfol_upd| intros s mo H; exact H| intros ? s mo (s1 & _ & H); exact H].
    + intros []. apply mfol_ret. intros; assumption.
Qed.

Lemma fol_brk_grow L req wb wm wp s0 :
  event_pre L (EBrk req) -> req <> 0 -> 2 * PGSZ <= wb -> 1 <= wm -> 2 <= wp ->
  mfol (FP L wb wm wp s0) (ev_step (EBrk req)) (fun _ s mo => PK false (wb - 2 * PGSZ) (wm - 1) (wp - 2) mo).
Proof.
  intros PRE NZ Wb Wm Wp. unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NZ).
  eapply mfol_bind; [apply mfol_get|]. intros s1. cbn beta.
  eapply mfol_bind with (Q1 := fun (_ : brk_ans) s mo => PK false (wb - 2 * PGSZ) (wm - 1) (wp - 2) mo).
  - apply mfol_sys. intros s mo rsp mo' evs a (-> & -> & K & P) ST _.
    destruct (brk_grow_facts _ _ _ _ K PRE NZ) as (B1 & A1 & _ & S1 & R1 & T1).
    assert (H1 : bv_unsigned (vm_brk (m_vmmaps mo)) < req <= bv_unsigned (vm_brk (m_vmmaps mo)) + 2 * PGSZ) by (unfold PGSZ in *; lia).
    exact (PK_brk_grow false wb wm wp mo _ _ _ req B1 S1 H1 Wb Wm Wp P ST).
  - intros [|].
    + eapply mfol_bind with (Q1 := fun _ s mo => PK false (wb - 2 * PGSZ) (wm - 1) (wp - 2) mo).
      * eapply mfol_conseq; [apply mfol_upd| intros s mo H; exact H| intros ? s mo (s2 & _ & H); exact H].
      * intros []. apply mfol_ret. intros; assumption.
    + apply mfol_ret. intros; assumption.
Qed.

Lemma fol_fixed L a wb wm wp s0 :
  mfol (fun s mo => FP L wb wm wp s0 s mo /\ a = bv_unsigned (vm_start_brk (m_vmmaps mo)))
       (ev_step (EMmap a PGSZ PROT_NONE MAPFX))
       (fun z s mo => is_err z = false /\ PK false wb wm wp mo).
Proof.
  unfold ev_step. change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true. cbv iota.
  eapply mfol_bind with (Q1 := fun (x : fixed_ans) s mo => (x = FxDone /\ a <= SBMAX) /\ PK false wb wm wp mo).
  - apply mfol_sys. intros s mo rsp mo' evs x ((-> & K & P) & Ha) ST D.
    split; [| exact (PK_mmap_fixed false wb wm wp mo rsp mo' evs L _ a K P Ha ST)].
    pose proof (pk_sb _ _ _ _ _ P) as SB. split; [| lia].
    pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as AR.
    assert (B1 : 0 <= a <= 2^64 - 4096) by (unfold SBMAX in SB; unfold bv_modulus in AR; lia).
    destruct (nstep_mmap_fixed_cases a mo rsp mo' evs ST) as (_ & Hs & _).
    pose proof (dec_mmap_fixed_cases a rsp FxDone B1 Hs) as D1. rewrite D1 in D. injection D as <-. reflexivity.
  - intros x. apply mfol_ret. intros s mo ((-> & Ha) & P). split; [| exact P].
    unfold is_err, TWO64, SBMAX in *. apply Z.ltb_ge. lia.
Qed.

Lemma fol_munmap L a len wb wm wp s0 :
  mfol (FP L wb wm wp s0) (ev_step (EMunmap a len)) (fun _ s mo => PK false wb wm wp mo).
Proof.
  unfold ev_step.
  eapply mfol_bind with (Q1 := fun (_ : range_ans) s mo => PK false wb wm wp mo).
  - apply mfol_sys. intros s mo rsp mo' evs x (-> & K & P) ST _. eapply PK_munmap; [exact P| exact ST].
  - intros x. apply mfol_ret. intros; assumption.
Qed.

Lemma fol_mprotect L a wb wm wp s0 :
  event_pre L (EMprotect a PGSZ PROT_RW) -> PGSZ <= wb ->
  mfol (FP L wb wm wp s0) (ev_step (EMprotect a PGSZ PROT_RW)) (fun z s mo => z = 0 /\ PK false (wb - PGSZ) wm wp mo).
Proof.
  intros PRE Wb. unfold ev_step.
  eapply mfol_bind with (Q1 := fun (x : range_ans) s mo => x = RgDone true /\ PK false (wb - PGSZ) wm wp mo).
  - apply mfol_sys. intros s mo rsp mo' evs x (-> & K & P) ST D. pose proof (pk_W _ _ _ _ _ P) as (W1 & _). assert (PG : PGSZ = 4096) by reflexivity.
    split; [| exact (PK_mprotect false wb wm wp (wb - PGSZ) mo rsp mo' evs a PGSZ PROT_RW P ltac:(lia) ST)].
    pose proof (mprotect_facts _ _ _ _ K PRE) as A1.
    destruct (nstep_dec_mprotect a PGSZ PROT_RW mo rsp mo' evs A1 ltac:(lia) ST) as (_ & _ & x1 & D1 & X1).
    destruct x1 as [e1|[|]]; [| | destruct X1].
    + exfalso. destruct (dec_mprotect_Some _ _ _ _ D1) as [Hs He]. exact (PK_mprotect_not_refused false wb wm wp mo L _ a PGSZ PROT_RW _ _ _ _ K P ST Hs He).
    + unfold dec_mprotect_rw in D. rewrite D1 in D. injection D as <-. reflexivity.
  - intros x. apply mfol_ret. intros s mo [-> P]. split; [reflexivity| exact P].
Qed.

Lemma ev_step_fol L e wb wm wp s0 :
  event_pre L e -> (let '(cb, cm, cp) := ecost e in cb <= wb /\ cm <= wm /\ cp <= wp) -> elen_ok e ->
  mfol (FP L wb wm wp s0) (ev_step e) (fun z s mo => good e z = true /\ PKc e wb wm wp mo).
Proof.
  intros PRE COST LEN. assert (PG : PGSZ = 4096) by reflexivity. unfold PKc.
  destruct e as [req|a len prot flags|a len|a len prot|? ? ?|?]; cbn [event_pre] in PRE; try contradiction; cbn [ecost good] in *.
  -
    destruct (Z.eqb_spec req 0) as [->|NZ].
    + eapply mfol_conseq; [apply (fol_brk0 L wb wm wp s0)| intros s mo HH; exact HH|].
      cbn beta. intros _ s mo P. rewrite !Z.sub_0_r. split; [reflexivity| exact P].
    + destruct COST as (C1 & C2 & C3).
      eapply mfol_conseq; [apply (fol_brk_grow L req wb wm wp s0 PRE NZ C1 C2 C3)| intros s mo HH; exact HH|].
      cbn beta. intros _ s mo P. split; [reflexivity| exact P].
  -
    destruct PRE as [(Q & -> & -> & Hp & Hl)|(cur & Hph & -> & -> & -> & ->)].
    + change (Z.land MAPF MAP_FIXED =? 0) with true in *. cbv iota in COST. destruct COST as (C1 & C2 & C3).
      destruct (LEN eq_refl) as [L1 L2]. pose proof (MBound.round_up_pg_ge len) as RG. rewrite Z.max_r in C1 |- * by lia.
      eapply mfol_conseq; [apply (fol_mmap L len prot wb wm wp s0 Hp L1 C1 C2)| intros s mo HH; exact HH|].
      cbn beta. intros z s mo [-> P]. rewrite Z.sub_0_r. split; [reflexivity| exact P].
    + change (Z.land MAPFX MAP_FIXED =? 0) with false in *. cbv iota.
      eapply mfol_conseq; [apply (fol_fixed L (round_up_pg cur) wb wm wp s0)| |].
      * intros s mo (-> & K & P). split; [split; [reflexivity| split; [exact K| exact P]]|].
        pose proof (kl_phase _ _ _ K) as PH. rewrite Hph in PH. destruct PH as (Ecur & _).
        pose proof (kl_start _ _ _ K) as (_ & SA & _). rewrite round_up_pg_aligned by (rewrite Ecur; exact SA). exact Ecur.
      * cbn beta. intros z s mo [-> P]. rewrite !Z.sub_0_r. split; [reflexivity| exact P].
  -
    eapply mfol_conseq; [apply (fol_munmap L a len wb wm wp s0)| intros s mo HH; exact HH|].
    cbn beta. intros _ s mo P. rewrite !Z.sub_0_r. split; [reflexivity| exact P].
  -
    destruct PRE as (Q & El & Ep & REST). subst len prot. destruct COST as (C1 & _).
    eapply mfol_conseq; [apply (fol_mprotect L a wb wm wp s0); [cbn [event_pre]; auto| exact C1]| intros s mo HH; exact HH|].
    cbn beta. intros z s mo [-> P]. rewrite !Z.sub_0_r. split; [reflexivity| exact P].
Qed.

Lemma membed_gspec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L wb wm wp rb rm rp QM s0,
  frame_ok G -> ctree_ok L t Post -> BT wb wm wp t QM -> 0 <= rb -> 0 <= rm -> 0 <= rp -> 0 <= wb -> 0 <= wm -> 0 <= wp ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo /\ PK false (wb + rb) (wm + rm) (wp + rp) mo) (membed t)
        (fun r s mo => exists L' wb' wm' wp', cpath L t L' r /\ Post L' r /\ gpath t r /\ QM r /\ KL L' (ps_brk s) mo /\ G s mo
              /\ 0 <= wb' /\ 0 <= wm' /\ 0 <= wp' /\ PK false (wb' + rb) (wm' + rm) (wp' + rp) mo /\ frames s0 s).
Proof.
  induction t as [x|e k IH]; intros Post G L wb wm wp rb rm rp QM s0 HG CT BTt Hrb Hrm Hrp W1 W2 W3.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & K & HGs & P). cbn in CT.
    exists L, wb, wm, wp. split; [constructor|]. split; [exact CT|]. split; [constructor|]. split; [exact BTt|].
    split; [exact K|]. split; [exact HGs|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact P| apply frames_refl].
  - cbn in CT. destruct CT as [PRE HK]. cbn [membed].
    assert (COST : let '(cb, cm, cp) := ecost e in cb <= wb /\ cm <= wm /\ cp <= wp /\ elen_ok e /\ forall z, BT (wb - cb) (wm - cm) (wp - cp) (k z) QM).
    { destruct e; cbn in BTt; try exact BTt; destruct PRE. }
    clear BTt. destruct (ecost e) as [[cb cm] cp] eqn:EC. destruct COST as (C1 & C2 & C3 & LEN & BK).
    pose proof (ecost_nonneg e) as NN. rewrite EC in NN.
    eapply mspec_bind.
    + eapply mspec_pre.
      * apply (mspec_mfol_conj _ _ _ _ _ (ev_step_spec L e G s0 HG PRE) (ev_step_fol L e (wb + rb) (wm + rm) (wp + rp) s0 PRE ltac:(rewrite EC; lia) LEN)).
      * intros s mo (-> & K & HGs & P). split; [split; [reflexivity| split; [exact K| exact HGs]]|]. split; [reflexivity|]. split; [exact K| exact P].
    + intros z. cbn beta. unfold ev_step_post, PKc. rewrite EC.
      apply mspec_pointwise. intros s1 mo1 ((Hans & HK1 & HG1 & Hm & Hfa & Hso) & Hg & HP1).
      eapply mspec_conseq; [apply (IH z Post G (event_post L e z) (wb - cb) (wm - cm) (wp - cp) rb rm rp QM s1 HG (HK z Hans) (BK z) Hrb Hrm Hrp
                                     ltac:(lia) ltac:(lia) ltac:(lia))| |].
      * intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK1|]. split; [exact HG1|].
        replace (wb - cb + rb) with (wb + rb - cb) by lia. replace (wm - cm + rm) with (wm + rm - cm) by lia.
        replace (wp - cp + rp) with (wp + rp - cp) by lia. exact HP1.
      * cbn beta. intros r s mo (L' & wb' & wm' & wp' & CP & HP & GP & HQ & HK' & HG' & V1 & V2 & V3 & PK' & FR).
        exists L', wb', wm', wp'. split; [econstructor; [exact Hans| exact CP]|]. split; [exact HP|].
        split; [econstructor; [exact Hg| exact GP]|]. split; [exact HQ|]. split; [exact HK'|]. split; [exact HG'|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact PK'|].
        eapply frames_trans; [| exact FR]. split; [exact Hm| split; [exact Hfa| exact Hso]].
Qed.

Definition GT : PState -> Model -> Prop := fun _ _ => True.

Definition PI (k : nat) (X : list bptr) (s : PState) (mo : Model) : Prop :=
  OWN X GT s mo /\ PK false (Wb k) (Wm k) (Wp k) mo /\ PHM k (ps_m s).

Lemma PI_mo k X s mo : PI k X s mo -> minv mo /\ m_halted mo = None.
Proof. intros (((L & _ & K & _) & _) & _). split; [exact (kl_minv _ _ _ K)| exact (kl_halt _ _ _ K)]. Qed.

Lemma PI_soupd k X s mo so : PI k X s mo -> PI k X (set_so_ps so s) mo.
Proof.
  intros (O & P & H). split; [| split; [exact P| destruct s; exact H]].
  eapply OWN_other; [exact O| destruct s; reflexivity| destruct s; reflexivity| exact I].
Qed.

Lemma PI_fdupd k X s mo mo' : PI k X s mo -> (mo' = mo \/ exists f, mo' = with_fds f mo) -> minv mo' -> m_halted mo' = None -> PI k X s mo'.
Proof.
  intros PI0 U MI HH. destruct U as [->|(f & ->)]; [exact PI0|]. destruct PI0 as (((L & C & K & I) & ND & _) & P & H).
  split; [| split; [apply PK_with_fds; exact P| exact H]].
  split; [| split; [exact ND| exact Logic.I]]. exists L. split; [exact C|]. split; [apply KL_with_fds; assumption| exact I].
Qed.

Lemma PI_perm k X Y s mo : Permutation X Y -> PI k X s mo -> PI k Y s mo.
Proof. intros HP (O & P & H). split; [eapply OWN_perm; [exact HP| exact O]| auto]. Qed.

Lemma PI_weaken k X s mo : PI (S k) X s mo -> PI k X s mo.
Proof. intros (O & P & H). split; [exact O|]. split; [apply PK_weaken_k; exact P| apply PHM_weaken; exact H]. Qed.

Definition GF (fds : list (word * FdEntry)) (fs : Fs) : PState -> Model -> Prop := fun _ mo => m_fds mo = fds /\ m_fs mo = fs.
Lemma GF_frame_ok fds fs : frame_ok (GF fds fs).
Proof. intros s s' mo mo' _ _ MF [A B]. apply mm_frame_fds_fs in MF as [C D]. split; congruence. Qed.

Definition NMAX : Z := MBound.NMAX.

Theorem raw_malloc_gspec k X n s1 mo1 : 0 <= n <= NMAX -> PI (S k) X s1 mo1 ->
  mspec (fun s mo => s = s1 /\ mo = mo1) (raw_malloc n)
        (fun r s mo => exists p, r = Some p /\ PI k (p :: X) s mo /\ ps_so s = ps_so s1 /\ m_fds mo = m_fds mo1 /\ m_fs mo = m_fs mo1).
Proof.
  intros Hn (((L & Hc & HK & Hi) & Hnd & _) & P & PH). unfold raw_malloc. pose proof (Wsucc k) as (E1 & E2 & E3).
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s mo (-> & -> & ->).
  eapply mspec_bind.
  { eapply mspec_pre.
    - apply (membed_gspec (cmalloc (ps_m s1) n) _ (GF (m_fds mo1) (m_fs mo1)) L BB BM BP (Wb k) (Wm k) (Wp k) (fun x => PHM k (fst x)) s1 (GF_frame_ok _ _)
               (KRemap.cmalloc_contract_proof2 _ _ _ Hc (proj1 Hn)) (cmalloc_BT _ _ _ Hn PH));
        unfold Wb, Wm, Wp, BB, BM, BP; lia.
    - intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [split; reflexivity|]. rewrite <- E1, <- E2, <- E3. exact P. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & wb' & wm' & wp' & Hp & HPost & GP & QM & HK' & HG' & V1 & V2 & V3 & PK' & (Fm & Ffa & Fso)).
  destruct (gpath_cmalloc _ _ _ (size_overflows_small n ltac:(unfold NMAX, MBound.NMAX in Hn; lia)) GP) as [c Ec]. cbn [snd] in Ec. subst p.
  cbn [fst snd] in HPost, QM. pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  eexists. split; [reflexivity|]. split; [| split; [exact Fso| exact HG']].
  split; [| split; [eapply PK_weaken; [exact PK'| | |]; unfold Wb, Wm, Wp, BB, BM, BP; lia| exact QM]].
  split; [| split; [| exact Logic.I]].
  - exists (set_live (c :: ld_live L') L'). split; [exact (c2_malloc _ _ _ _ _ _ Hc (proj1 Hn) Hp)|].
    split; [apply KL_set_live; exact HK'|].
    cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
  - cbn. constructor; [| exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
Qed.

Theorem raw_free_gspec k X p s1 mo1 : PI k (p :: X) s1 mo1 ->
  mspec (fun s mo => s = s1 /\ mo = mo1) (raw_free p)
        (fun _ s mo => PI k X s mo /\ ps_so s = ps_so s1 /\ m_fds mo = m_fds mo1 /\ m_fs mo = m_fs mo1).
Proof.
  intros (((L & Hc & HK & Hi) & Hnd & _) & P & PH). unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s mo (-> & -> & ->).
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  eapply mspec_bind.
  { eapply mspec_pre.
    - apply (membed_gspec (cfree (ps_m s1) (Some (fst p))) _ (GF (m_fds mo1) (m_fs mo1)) L 0 0 0 (Wb k) (Wm k) (Wp k) (PHM k) s1 (GF_frame_ok _ _)
               (KRemap.cfree_contract_proof2 _ _ _ Hc Hin) (cfree_BT _ _ _ PH)); lia.
    - intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [split; reflexivity|]. cbn [Z.add]. exact P. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & wb' & wm' & wp' & Hp & _ & _ & QM & HK' & HG' & V1 & V2 & V3 & PK' & (Fm & Ffa & Fso)).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->]. split; [| split; [exact Fso| exact HG']].
  split; [| split; [eapply PK_weaken; [exact PK'| | |]; lia| exact QM]].
  cbn in Hnd. inversion Hnd; subst.
  split; [| split; [assumption| exact Logic.I]].
  exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact (c2_free _ _ _ _ _ Hc Hin Hp)|].
  split; [apply KL_set_live; exact HK'|].
  cbn. intros x Hx. rewrite Hlive. apply in_ap_remove; [apply Hi; right; exact Hx|].
  intros ->. match goal with H : ~ In (fst p) (map fst X) |- _ => apply H; exact Hx end.
Qed.

Lemma twf_tpaths {R} : forall (t : itree node R) mo (P : R -> Model -> Prop) tr r mo',
  twf t mo P -> tpaths t mo tr r mo' -> P r mo'.
Proof.
  induction t as [r0|n k IH]; intros mo P tr r mo' HW HP; cbn in HW, HP.
  - destruct HP as (<- & -> & _). exact HW.
  - destruct HW as [_ HK]. destruct HP as (_ & _ & rsp & mo1 & evs & tr' & ST & HP' & _). eapply IH; [eapply HK; exact ST| exact HP'].
Qed.

Lemma twf_msys_nsafe {A B} n (dec : resp -> option A) (f : A -> Monad.M PState B) s mo P :
  twf (mbind (msys n dec) f s) mo P -> nsafe n mo.
Proof. intros H. hnf in H. exact (proj1 H). Qed.

Lemma tpaths_msys_bind {A B} n (dec : resp -> option A) (f : A -> Monad.M PState B) s mo rsp mo1 a r mo2 :
  match n with NExit _ => False | _ => True end -> nsafe n mo -> nstep n mo rsp mo1 [] -> dec rsp = Some a ->
  tpaths (f a s) mo1 [] r mo2 -> tpaths (mbind (msys n dec) f s) mo [] r mo2.
Proof. intros Hne Hs ST D TP. eapply tpaths_mbind; [eapply tpaths_msys; eauto| exact TP]. Qed.

Lemma nstep_mmap_grant_exists wb wm wp mo L pbrk len prot :
  KL L pbrk mo -> PK false wb wm wp mo -> 0 < len <= LMAX -> (prot = PROT_NONE \/ prot = PROT_RW) -> round_up_pg len <= wb ->
  exists rsp mo', nstep (NMmap 0 len prot MAPF) mo rsp mo' [].
Proof.
  intros K P Hl Hp Wb. pose proof (PK_not_forced_mmap false wb wm wp mo L pbrk len prot K P Hl Hp Wb) as NF.
  pose proof (minv_alloc_top mo (kl_minv _ _ _ K)) as [_ TOP].
  unfold nmmap_refusable in NF.
  set (nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in *. set (n := Z_to_bv 64 nZ). set (h := m_vmmaps mo).
  destruct Hp as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false in NF.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true in NF. cbv iota in NF.
    destruct (mmap_reserve_unforced _ _ NF) as (a & Q1 & Q2 & Q3 & Q4).
    eexists (mkEffectU a [] [] [(a, n)] [] []), _. cbn [nstep]. split; [reflexivity|]. right; right; left.
    split; [reflexivity|]. split; [reflexivity|]. exists a.
    split; [split; [exact Q1| split; [exact Q2| split; [cbv delta [nZ] in Q3; lia| split; [exact Q4| exact Q3]]]]|].
    rewrite strip_mk. split; reflexivity.
  - change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true in NF. cbv iota in NF.
    destruct (mmap_grant_unforced _ _ _ NF) as (HB & a & Q1 & Q2 & Q3 & Q4).
    eexists (mkEffect a [] [(a, n)]), _. cbn [nstep]. split; [reflexivity|]. right; left. split; [reflexivity|].
    exists a. split; [split; [exact Q1| split; [exact Q2| split; [cbv delta [nZ] in Q3; lia| split; [exact Q4| exact Q3]]]]|].
    split; [exact HB|]. split; reflexivity.
Qed.

Lemma ev_step_px L e wb wm wp s mo P :
  event_pre L e -> (let '(cb, cm, cp) := ecost e in cb <= wb /\ cm <= wm /\ cp <= wp) -> elen_ok e ->
  KL L (ps_brk s) mo -> PK false wb wm wp mo -> twf (ev_step e s) mo P ->
  exists z s1 mo1, tpaths (ev_step e s) mo [] (Ok (z, s1)) mo1.
Proof.
  intros PRE COST LEN K PK0 TW. assert (PG : PGSZ = 4096) by reflexivity. pose proof (pk_W _ _ _ _ _ PK0) as (W1 & W2 & W3).
  destruct e as [req|a len prot flags|a len|a len prot|? ? ?|?]; cbn [event_pre] in PRE; try contradiction; cbn [ecost] in COST.
  -
    clear TW. unfold ev_step. destruct (Z.eqb_spec req 0) as [->|NZ].
    + cbn [Z.eqb]. pose proof (nstep_brk_intro 0 mo _ (brk_r_ok_refuse mo (Z_to_bv 64 0)) ltac:(apply brk_ns_of_nonrefusal; apply brk_query_nonrefusal)) as ST.
      destruct (nstep_dec_brk0 _ _ _ _ ST) as (_ & D & _).
      eexists _, _, _. eapply tpaths_msys_bind; [exact Logic.I| exact Logic.I| exact ST| exact D|].
      eapply tpaths_mbind; [apply tpaths_ret| apply tpaths_ret].
    + destruct COST as (C1 & C2 & C3).
      destruct (brk_grow_facts _ _ _ _ K PRE NZ) as (B1 & A1 & Epb & S1 & R1 & T1).
      destruct (nstep_brk_exists req mo) as (rspX & moX & ST).
      destruct (nstep_dec_brk req mo _ _ _ B1 S1 ltac:(lia) ST) as (_ & _ & x & D & X). rewrite <- Epb in D.
      destruct x.
      * eexists _, _, _. eapply tpaths_mbind; [apply tpaths_ret|]. cbn beta.
        eapply tpaths_msys_bind; [exact Logic.I| exact Logic.I| exact ST| exact D|]. cbn iota.
        eapply tpaths_mbind; [apply tpaths_ret| apply tpaths_ret].
      * eexists _, _, _. eapply tpaths_mbind; [apply tpaths_ret|]. cbn beta.
        eapply tpaths_msys_bind; [exact Logic.I| exact Logic.I| exact ST| exact D|]. cbn iota. apply tpaths_ret.
  -
    destruct PRE as [(Q & -> & -> & Hp & Hl)|(cur & Hph & -> & -> & -> & ->)].
    + clear TW. change (Z.land MAPF MAP_FIXED =? 0) with true in *. cbv iota in COST. destruct COST as (C1 & C2 & C3).
      destruct (LEN eq_refl) as [L1 L2]. pose proof (MBound.round_up_pg_ge len) as RG. rewrite Z.max_r in C1 by lia.
      destruct (nstep_mmap_grant_exists wb wm wp mo L _ len prot K PK0 L1 Hp C1) as (rsp & mo' & ST).
      pose proof (mmap_len_bound len ltac:(lia)) as LB. assert (L64 : mmap_len len < 2^64) by (unfold LMAX in L1; lia).
      unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
      destruct Hp as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
      * assert (NS : nsafe (NMmap 0 len PROT_NONE MAPF) mo). { cbn [nsafe]. intros HX. exfalso. revert HX. vm_compute. discriminate. }
        destruct (nstep_dec_mmap_none len [] mo rsp mo' [] ltac:(lia) L64 ltac:(constructor) ST) as (_ & _ & x1 & D1 & _).
        eexists _, _, _. eapply tpaths_msys_bind; [exact Logic.I| exact NS| exact ST| exact D1| apply tpaths_ret].
      * assert (NS : nsafe (NMmap 0 len PROT_RW MAPF) mo). { cbn [nsafe]. intros HX. exfalso. revert HX. vm_compute. discriminate. }
        destruct (nstep_dec_mmap len [] mo rsp mo' [] ltac:(lia) L64 ltac:(constructor) ST) as (_ & _ & x1 & D1 & _).
        eexists _, _, _. eapply tpaths_msys_bind; [exact Logic.I| exact NS| exact ST| exact D1| apply tpaths_ret].
    + unfold ev_step in *. change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbv iota in TW. cbv iota.
      pose proof (twf_msys_nsafe _ _ _ _ _ _ TW) as NS.
      set (a := round_up_pg cur) in *.
      pose proof (kl_phase _ _ _ K) as PH. rewrite Hph in PH. destruct PH as (Ecur & _).
      pose proof (kl_start _ _ _ K) as (_ & SA & _ & SB').
      assert (Ha : a = bv_unsigned (vm_start_brk (m_vmmaps mo))) by (subst a; rewrite round_up_pg_aligned by (rewrite Ecur; exact SA); exact Ecur).
      pose proof (pk_sb _ _ _ _ _ PK0) as SB. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as AR.
      assert (B1 : 0 <= a <= 2^64 - 4096) by (unfold SBMAX in SB; unfold bv_modulus in AR; lia).
      pose proof (nstep_mmap_fixed_done_intro a mo) as ST. cbv zeta in ST.
      eexists _, _, _. eapply tpaths_msys_bind; [exact Logic.I| exact NS| exact ST| | apply tpaths_ret].
      apply (dec_mmap_fixed_cases a _ FxDone B1). rewrite strip_mk. reflexivity.
  -
    unfold ev_step in *. pose proof (twf_msys_nsafe _ _ _ _ _ _ TW) as NS.
    destruct (munmap_facts _ _ _ _ _ K PRE) as [A1 L1].
    pose proof (nstep_munmap_intro a len mo) as ST. cbv zeta in ST.
    destruct (nstep_dec_munmap a len mo _ _ _ A1 L1 ST) as (_ & _ & D & _).
    eexists _, _, _. eapply tpaths_msys_bind; [exact Logic.I| exact NS| exact ST| exact D| apply tpaths_ret].
  -
    destruct PRE as (Q & -> & -> & REST). unfold ev_step in *. pose proof (twf_msys_nsafe _ _ _ _ _ _ TW) as NS.
    pose proof (nstep_mprotect_ok_intro false wb wm wp L _ a PGSZ PROT_RW mo K PK0) as ST. cbv zeta in ST.
    eexists _, _, _. eapply tpaths_msys_bind; [exact Logic.I| exact NS| exact ST| apply dec_mprotect_rw_ok| apply tpaths_ret].
Qed.

Lemma membed_px {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) L wb wm wp rb rm rp QM s mo,
  ctree_ok L t Post -> BT wb wm wp t QM -> 0 <= rb -> 0 <= rm -> 0 <= rp -> 0 <= wb -> 0 <= wm -> 0 <= wp ->
  KL L (ps_brk s) mo -> PK false (wb + rb) (wm + rm) (wp + rp) mo ->
  exists r s' mo', tpaths (membed t s) mo [] (Ok (r, s')) mo'.
Proof.
  induction t as [x|e k IH]; intros Post L wb wm wp rb rm rp QM s mo CT BTt Hrb Hrm Hrp W1 W2 W3 K P.
  - cbn [membed]. eexists _, _, _. apply tpaths_ret.
  - cbn in CT. destruct CT as [PRE HK]. cbn [membed].
    assert (COST : let '(cb, cm, cp) := ecost e in cb <= wb /\ cm <= wm /\ cp <= wp /\ elen_ok e /\ forall z, BT (wb - cb) (wm - cm) (wp - cp) (k z) QM).
    { destruct e; cbn in BTt; try exact BTt; destruct PRE. }
    clear BTt. destruct (ecost e) as [[cb cm] cp] eqn:EC. destruct COST as (C1 & C2 & C3 & LEN & BK).
    pose proof (ecost_nonneg e) as NN. rewrite EC in NN.
    pose proof (mspec_mfol_conj _ _ _ _ _ (ev_step_spec L e GT s frame_ok_true PRE) (ev_step_fol L e (wb + rb) (wm + rm) (wp + rp) s PRE ltac:(rewrite EC; lia) LEN)
                  s mo ltac:(split; [split; [reflexivity| split; [exact K| exact Logic.I]]| split; [reflexivity| split; [exact K| exact P]]])) as TW.
    unfold etwf in TW.
    destruct (ev_step_px L e (wb + rb) (wm + rm) (wp + rp) s mo _ PRE ltac:(rewrite EC; lia) LEN K P TW) as (z & s1 & mo1 & TP).
    pose proof (twf_tpaths _ _ _ _ _ _ TW TP) as POST. cbn [fst snd] in POST. unfold ev_step_post, PKc in POST. rewrite EC in POST.
    destruct POST as ((Hans & HK1 & _ & Hm & Hfa & Hso) & Hg & HP1).
    destruct (IH z Post (event_post L e z) (wb - cb) (wm - cm) (wp - cp) rb rm rp QM s1 mo1 (HK z Hans) (BK z) Hrb Hrm Hrp
                 ltac:(lia) ltac:(lia) ltac:(lia) HK1
                 ltac:(replace (wb - cb + rb) with (wb + rb - cb) by lia; replace (wm - cm + rm) with (wm + rm - cm) by lia;
                       replace (wp - cp + rp) with (wp + rp - cp) by lia; exact HP1)) as (r & s' & mo' & TP').
    exists r, s', mo'. eapply tpaths_mbind; [exact TP| exact TP'].
Qed.

Theorem raw_malloc_px k X n s mo : 0 <= n <= NMAX -> PI (S k) X s mo ->
  exists p s' mo', tpaths (raw_malloc n s) mo [] (Ok (Some p, s')) mo'.
Proof.
  intros Hn PI0. pose proof PI0 as (((L & Hc & HK & Hi) & Hnd & _) & P & PH). pose proof (Wsucc k) as (E1 & E2 & E3).
  rewrite E1, E2, E3 in P.
  destruct (membed_px (cmalloc (ps_m s) n) _ L BB BM BP (Wb k) (Wm k) (Wp k) (fun x => PHM k (fst x)) s mo
              (KRemap.cmalloc_contract_proof2 _ _ _ Hc (proj1 Hn)) (cmalloc_BT _ _ _ Hn PH)) as ([st' p] & s' & mo' & TP);
    try (unfold Wb, Wm, Wp, BB, BM, BP; lia); [exact HK| exact P|].
  assert (TPM : tpaths (raw_malloc n s) mo [] (Ok (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end, set_m st' s')) mo').
  { unfold raw_malloc. eapply tpaths_mbind; [apply tpaths_ret|]. cbn beta.
    eapply tpaths_mbind; [exact TP|]. cbn beta iota. eapply tpaths_mbind; [apply tpaths_ret| apply tpaths_ret]. }
  pose proof (twf_tpaths _ _ _ _ _ _ (raw_malloc_gspec k X n s mo Hn PI0 s mo (conj eq_refl eq_refl)) TPM) as (q & Eq & _).
  cbn [fst] in Eq. destruct p as [slot|]; [| discriminate Eq]. eexists _, _, _. exact TPM.
Qed.

Theorem raw_free_px k X p s mo : PI k (p :: X) s mo -> exists s' mo', tpaths (raw_free p s) mo [] (Ok (tt, s')) mo'.
Proof.
  intros PI0. pose proof PI0 as (((L & Hc & HK & Hi) & Hnd & _) & P & PH). pose proof (pk_W _ _ _ _ _ P) as (W1 & W2 & W3).
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  destruct (membed_px (cfree (ps_m s) (Some (fst p))) _ L 0 0 0 (Wb k) (Wm k) (Wp k) (PHM k) s mo
              (KRemap.cfree_contract_proof2 _ _ _ Hc Hin) (cfree_BT _ _ _ PH)) as (st' & s' & mo' & TP); try lia; [exact HK| cbn [Z.add]; exact P|].
  eexists _, _. unfold raw_free. eapply tpaths_mbind; [apply tpaths_ret|]. cbn beta.
  eapply tpaths_mbind; [exact TP|]. cbn beta. apply tpaths_ret.
Qed.

Theorem raw_malloc_stwf k X n s mo : 0 <= n <= NMAX -> PI (S k) X s mo ->
  stwf node nstep nexit nsafe (raw_malloc n s) mo
       (fun r mo' => exists p s', r = Ok (Some p, s') /\ PI k (p :: X) s' mo' /\ ps_so s' = ps_so s
                                  /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Hn PI0. pose proof (raw_malloc_gspec k X n s mo Hn PI0 s mo (conj eq_refl eq_refl)) as TW. unfold etwf in TW.
  eapply stwf_mono; [apply (twf_mm_stwf _ _ _ TW (raw_malloc_mm n s))|].
  intros [|[r s']] mo' H; cbn in H; [destruct H|]. destruct H as (p & -> & H). exists p, s'. split; [reflexivity| exact H].
Qed.

Theorem raw_free_stwf k X p s mo : PI k (p :: X) s mo ->
  stwf node nstep nexit nsafe (raw_free p s) mo
       (fun r mo' => exists s', r = Ok (tt, s') /\ PI k X s' mo' /\ ps_so s' = ps_so s
                                /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros PI0. pose proof (raw_free_gspec k X p s mo PI0 s mo (conj eq_refl eq_refl)) as TW. unfold etwf in TW.
  eapply stwf_mono; [apply (twf_mm_stwf _ _ _ TW (raw_free_mm p s))|].
  intros [|[[] s']] mo' H; cbn in H; [destruct H|]. exists s'. split; [reflexivity| exact H].
Qed.

Lemma reserved_top_ehi : forall r e, In e r -> ehi e <= reserved_top r.
Proof.
  induction r as [|[a sz] r IH]; intros e H; [destruct H|].
  destruct H as [<-|H]; cbn [reserved_top]; unfold ehi; cbn [fst snd]; [lia|].
  specialize (IH e H). unfold ehi in IH. lia.
Qed.

Lemma PHM_init k resv ceil : (k <= KTOP)%nat -> PHM k (strip (minit 0 resv ceil)).
Proof.
  intros Hk. unfold PHM. apply (VI_mono 0); [unfold CM; lia|].
  unfold VI, VIv, cview. cbn -[Z.le Z.mul Z.add Vs]. unfold Vs, NSLOTS. cbn. lia.
Qed.

Theorem PI_init (CP : HasCeiling) (sp brk mb : word) (inp : ProcInput) (t : Z) (k : nat) :
  valid_input inp -> valid_sp sp -> valid_brk P0.Segs.rsegs brk -> valid_mmap_base mb ->
  @alloc_ceiling CP = bv_unsigned sp - stack_max_size -> 0 < t < PID_MAX_ENVELOPE -> (k <= KTOP)%nat ->
  PI k [] (ps_init (reservedZ P0.Segs.rsegs) (@alloc_ceiling CP))
     (with_tid (Z_to_bv 64 t) (init_model (segments_reserved P0.Segs.rsegs) brk mb sp source_alloc_limit inp)).
Proof.
  intros _ (SP1 & SP2 & _) (LO & HI & AL) (MB & _ & _) EC Ht Hk.
  assert (TOP : reserved_top (segments_reserved P0.Segs.rsegs) = 0x5c000) by (vm_compute; reflexivity). rewrite TOP in LO, HI.
  assert (BAM : brk_aslr_max = 1073741824) by (vm_compute; reflexivity).
  assert (PG : page_size = PGSZ) by (vm_compute; reflexivity). rewrite PG in AL.
  assert (PE : PID_MAX_ENVELOPE = 4194304) by reflexivity.
  assert (Ht' : 0 < bv_unsigned (Z_to_bv 64 t) < PID_MAX_ENVELOPE) by (rewrite unsigned_lit by lia; lia).
  assert (RZ : reservedZ P0.Segs.rsegs = map wwZ (segments_reserved P0.Segs.rsegs)) by reflexivity. rewrite RZ, EC.
  split; [| split].
  - split; [| split; [constructor| exact Logic.I]].
    exists (led_init (map wwZ (segments_reserved P0.Segs.rsegs)) (bv_unsigned sp - stack_max_size)). split; [| split; [| intros x []]].
    + unfold ps_init. cbn [ps_m]. apply c2_init. unfold alloc_ceiling_max, sp_window_hi, stack_max_size in *. lia.
    + unfold ps_init. cbn [ps_brk]. apply KL_with_tid; [| exact Ht'].
      apply KL_init; [| lia| exact AL| unfold sp_window_lo, stack_max_size, PGSZ in *; lia| lia].
      intros e He. pose proof (reserved_top_ehi _ _ He) as H. rewrite TOP in H. lia.
  - apply PK_with_tid. eapply PK_weaken; [apply PK_init| | |].
    + vm_compute. cbn. lia.
    + unfold SBMAX. lia.
    + unfold BACKTOP, source_alloc_limit. cbn. lia.
    + exact MB.
    + unfold Wb, BB, KTOP in *. lia.
    + unfold Wm, BM, KTOP in *. lia.
    + unfold Wp, BP, KTOP in *. lia.
  - unfold ps_init. cbn [ps_m]. apply PHM_init. exact Hk.
Qed.

Theorem P0_drv_nonnull :
  exists (PI : nat -> list bptr -> PState -> Model -> Prop) (NMAX : Z),
    2^26 <= NMAX
    /\ (forall k X s mo, PI k X s mo -> minv mo /\ m_halted mo = None)
    /\ (forall k X s mo so, PI k X s mo -> PI k X (set_so_ps so s) mo)
    /\ (forall k X s mo mo', PI k X s mo -> (mo' = mo \/ exists f, mo' = with_fds f mo) -> minv mo' -> m_halted mo' = None -> PI k X s mo')
    /\ (forall k X Y s mo, Permutation X Y -> PI k X s mo -> PI k Y s mo)
    /\ (forall k X s mo, PI (S k) X s mo -> PI k X s mo)
    /\ (forall k X n s mo, 0 <= n <= NMAX -> PI (S k) X s mo ->
          stwf node nstep nexit nsafe (raw_malloc n s) mo
            (fun r mo' => exists p s', r = Ok (Some p, s') /\ PI k (p :: X) s' mo' /\ ps_so s' = ps_so s
                                       /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo))
    /\ (forall k X n s mo, 0 <= n <= NMAX -> PI (S k) X s mo ->
          exists p s' mo', tpaths (raw_malloc n s) mo [] (Ok (Some p, s')) mo')
    /\ (forall k X p s mo, PI k (p :: X) s mo ->
          stwf node nstep nexit nsafe (raw_free p s) mo
            (fun r mo' => exists s', r = Ok (tt, s') /\ PI k X s' mo' /\ ps_so s' = ps_so s
                                     /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo))
    /\ (forall k X p s mo, PI k (p :: X) s mo -> exists s' mo', tpaths (raw_free p s) mo [] (Ok (tt, s')) mo')
    /\ (forall (CP : HasCeiling) (sp brk mb : word) (inp : ProcInput) (t : Z),
          valid_input inp -> valid_sp sp -> valid_brk P0.Segs.rsegs brk -> valid_mmap_base mb ->
          @alloc_ceiling CP = bv_unsigned sp - stack_max_size ->
          0 < t < PID_MAX_ENVELOPE ->
          PI (DriverSim.DRV_BUDGET 0) [] (ps_init (reservedZ P0.Segs.rsegs) (@alloc_ceiling CP))
             (with_tid (Z_to_bv 64 t) (init_model (segments_reserved P0.Segs.rsegs) brk mb sp source_alloc_limit inp))).
Proof.
  exists PI, NMAX. split; [unfold NMAX, MBound.NMAX; apply Z.pow_le_mono_r; lia|].
  split; [exact PI_mo|]. split; [exact PI_soupd|]. split; [exact PI_fdupd|]. split; [exact PI_perm|]. split; [exact PI_weaken|].
  split; [exact raw_malloc_stwf|]. split; [exact raw_malloc_px|]. split; [exact raw_free_stwf|]. split; [exact raw_free_px|].
  intros CP sp brk mb inp t VI VS VB VM EC Ht. apply (PI_init CP sp brk mb inp t _ VI VS VB VM EC Ht).
  unfold DriverSim.DRV_BUDGET, KTOP. cbn. lia.
Qed.
