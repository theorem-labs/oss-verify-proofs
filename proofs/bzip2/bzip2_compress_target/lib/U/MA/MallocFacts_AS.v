(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep MallocTree MallocFacts_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module MallocNat.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma steq_trans {E A R} (t1 t2 t3 : stree E A R) : steq t1 t2 -> steq t2 t3 -> steq t1 t3.
Proof.
  intros H1 H2. apply strel_eq_steq. apply strel_eq_steq in H1. apply strel_eq_steq in H2.
  eapply strel_trans_eq; [exact H1| exact H2].
Qed.

Lemma steq_sbind {E A R S} (t1 t2 : stree E A R) (f1 f2 : R -> stree E A S) :
  steq t1 t2 -> (forall r, steq (f1 r) (f2 r)) -> steq (sbind t1 f1) (sbind t2 f2).
Proof.
  intros Ht Hf. apply strel_eq_steq. eapply (strel_sbind (RR := eq)); [apply strel_eq_steq; exact Ht|].
  intros r1 r2 ->. apply strel_eq_steq. apply Hf.
Qed.

Lemma eruns_steq {E A O R} (sel : O -> E -> option A) (upd : O -> E -> A -> O) (t1 t2 : stree E A R) :
  steq t1 t2 -> forall o, steq (eruns sel upd o t1) (eruns sel upd o t2).
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros o; cbn [eruns].
  - constructor.
  - destruct (sel o e) as [a|]; [apply IH|]. constructor. intros a. apply IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kS {X Y : Type} : X -> Y -> Malloc.M (option (X * Y)) := fun x y => SRet (Some (x, y)).
Definition bS {T : Type} : Malloc.M (option T) := SRet None.
Definition KF {X Y R : Type} (k : X -> Y -> Malloc.M R) (bail : Malloc.M R) (r : option (X * Y)) : Malloc.M R :=
  match r with Some (x, y) => k x y | None => bail end.
(* [comment removed for export] *)
Definition kS1 {X : Type} : X -> Malloc.M (option X) := fun x => SRet (Some x).
Definition KF1 {X R : Type} (k : X -> Malloc.M R) (bail : Malloc.M R) (r : option X) : Malloc.M R :=
  match r with Some x => k x | None => bail end.
End ACeilS1.


(* [comment removed for export] *)
Ltac nat_leaf := cbn [sbind KF KF1 kS kS1 bS]; apply steq_refl.
Ltac nat_vis := cbn [sbind]; apply steq_vis; intros ?.
Ltac nat_case :=
  lazymatch goal with
  | |- steq _ (sbind (match ?c with _ => _ end) _) => destruct c
  end.

(* [comment removed for export] *)
Ltac nat_call NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [[? ?]|]; cbn [KF sbind].
Ltac nat_call1 NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [?|]; cbn [KF1 sbind].
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma guard_nat {X Y R} tag c (K : Malloc.M R) (K' : Malloc.M (option (X * Y))) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

Lemma guard_nat1 {X R} tag c (K : Malloc.M R) (K' : Malloc.M (option X)) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

Lemma queue_nat {R} h m st (k : mstate -> Malloc.M R) bail :
  steq (queue h m st k bail) (sbind (queue h m st kS1 bS) (KF1 k bail)).
Proof.
  unfold queue. apply guard_nat1; [|nat_leaf]. apply guard_nat1; [|nat_leaf].
  nat_case; cbv zeta; [destruct (m_prev _)|]; nat_leaf.
Qed.

Lemma free_meta_nat {R} m st (k : mstate -> Malloc.M R) bail :
  steq (free_meta m st k bail) (sbind (free_meta m st kS1 bS) (KF1 k bail)).
Proof. unfold free_meta. apply queue_nat. Qed.

Lemma activate_group_nat {R} m st (k : mstate -> Z -> Malloc.M R) bail :
  steq (activate_group m st k bail) (sbind (activate_group m st kS bS) (KF k bail)).
Proof. unfold activate_group. apply guard_nat; [|nat_leaf]. cbv zeta. nat_leaf. Qed.
End ACeilS2.


(* [comment removed for export] *)
Ltac nat_auto cal :=
  first [ nat_leaf
        | cal
        | nat_vis; nat_auto cal
        | nat_case; nat_auto cal
        | progress (cbv zeta); nat_auto cal ].
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma am_take_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_take st k bail) (sbind (am_take st kS bS) (KF k bail)).
Proof. unfold am_take. nat_auto fail. Qed.

Lemma am_carve_nat {R} st p (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_carve st p k bail) (sbind (am_carve st p kS bS) (KF k bail)).
Proof. unfold am_carve. cbv zeta. apply am_take_nat. Qed.

Lemma am_finish_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_finish st nu k bail) (sbind (am_finish st nu kS bS) (KF k bail)).
Proof. unfold am_finish, bad_answer. nat_auto ltac:(apply am_carve_nat). Qed.

Lemma am_after_brk_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_after_brk st nu k bail) (sbind (am_after_brk st nu kS bS) (KF k bail)).
Proof. unfold am_after_brk, bad_answer. nat_auto ltac:(apply am_finish_nat). Qed.

Lemma alloc_meta_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_meta st k bail) (sbind (alloc_meta st kS bS) (KF k bail)).
Proof.
  unfold alloc_meta, bad_answer. nat_auto ltac:(first [apply am_take_nat | apply am_after_brk_nat]).
Qed.

Lemma ta_fin_nat {R} st m mask (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) :
  steq (ta_fin st m mask k) (sbind (ta_fin st m mask kS) (KF k bail)).
Proof. unfold ta_fin. cbv zeta. nat_leaf. Qed.

Lemma try_avail_nat {R} sc st (k : mstate -> Z -> Malloc.M R) bail :
  steq (try_avail sc st k bail) (sbind (try_avail sc st kS bS) (KF k bail)).
Proof.
  unfold try_avail. nat_case; [|nat_leaf]. cbv zeta. nat_case; [apply ta_fin_nat|].
  nat_case.
  - destruct p as [st1 m1]. nat_case. destruct p as [st2 m2]. nat_case.
    eapply steq_trans; [apply activate_group_nat|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply activate_group_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st4 mask]|]; cbn [KF sbind]; [|nat_leaf].
    apply guard_nat; [apply ta_fin_nat| nat_leaf].
  - nat_case; [nat_leaf|]. nat_vis. nat_leaf.
Qed.

Lemma ag_tail_nat {R} lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) :
  steq (ag_tail lay st sc m p cnt ai k) (sbind (ag_tail lay st sc m p cnt ai kS) (KF k bail)).
Proof. unfold ag_tail. cbv zeta. nat_leaf. Qed.

Section AG.
Variable lay : layout_hook.
Variable rec : forall R, mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis rec_nat : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (rec R st sc req k bail) (sbind (rec _ st sc req kS bS) (KF k bail)).

Lemma alloc_group_nat {R} st sc req (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_group R lay (rec R) st sc req k bail)
       (sbind (alloc_group _ lay (rec _) st sc req kS bS) (KF k bail)).
Proof.
  unfold alloc_group, bad_answer. cbv zeta. nat_call (@alloc_meta_nat); [|nat_leaf].
  nat_case; [|nat_leaf]. nat_case.
  - (* [comment removed for export] *)
    match goal with |- steq _ (sbind (let '(_, _) := ?p in _) _) => destruct p as [cnt' needed] end.
    nat_vis. nat_case; [nat_vis; nat_leaf|]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case. cbv zeta. apply ag_tail_nat.
  - (* [comment removed for export] *)
    nat_call rec_nat; [|nat_leaf]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case; [|nat_vis; nat_leaf]. cbv zeta. apply ag_tail_nat.
Qed.
End AG.

Lemma alloc_slot_nat lay fuel : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (alloc_slot lay fuel st sc req k bail) (sbind (alloc_slot lay fuel st sc req kS bS) (KF k bail)).
Proof.
  induction fuel as [|f IH]; intros R st sc req k bail.
  - cbn [alloc_slot]. nat_vis. nat_leaf.
  - cbn [alloc_slot]. nat_call (@try_avail_nat); [|nat_leaf]. nat_case; [nat_leaf|].
    eapply steq_trans; [apply (alloc_group_nat lay (fun R => @alloc_slot _ R lay f) IH)|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply (alloc_group_nat lay (fun R => @alloc_slot _ R lay f) IH)| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st2 go]|]; cbn [KF sbind]; [|nat_leaf].
    nat_case; [|nat_leaf]. cbv zeta. nat_call1 (@queue_nat); nat_leaf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS3.
End MallocNat.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ta_fail (sc : Z) (st st1 : mstate) : Prop :=
  try_avail sc st kS bS = SRet (Some (st1, 0)).

(* [comment removed for export] *)
Definition req_ok (sc req : Z) : Prop := 0 <= req /\ req + IB <= UNIT * size_class sc.

(* [comment removed for export] *)
Inductive IST (st0 : mstate) : mstate -> Prop :=
| ist_top : forall t, (s_tick st0 < t)%N -> IST st0 (set_tick t st0)
| ist_am : forall o st sc st1 st2 m,
    IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
    leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
    IST st0 st2.

(* [comment removed for export] *)
Definition ISTR (st0 st3 : mstate) : Prop :=
  exists o st f sc req idx,
    IST st0 st /\ 0 <= sc < 48 /\ req_ok sc req /\
    leaf_of o (alloc_slot full_lay f st sc req kS bS) (Some (st3, idx)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lmem (cs : mstate) (g : aptr) : Prop :=
  m_mem (get_meta_rec cs g) <> None /\ m_next (get_meta_rec cs g) <> None /\ m_prev (get_meta_rec cs g) <> None.

Definition fact_lists (cs : mstate) : Prop :=
  (forall sc g, active cs sc = Some g -> lmem cs g)
  /\ (forall g n, m_mem (get_meta_rec cs g) <> None -> m_next (get_meta_rec cs g) = Some n ->
        lmem cs n /\ m_sizeclass (get_meta_rec cs n) = m_sizeclass (get_meta_rec cs g))
  /\ (forall g p, m_mem (get_meta_rec cs g) <> None -> m_prev (get_meta_rec cs g) = Some p ->
        lmem cs p /\ m_sizeclass (get_meta_rec cs p) = m_sizeclass (get_meta_rec cs g)).

Definition fact_freelist (cs : mstate) : Prop :=
  forall h, c_free_meta_head (ctx cs) = Some h ->
    meta_slot cs h /\ m_mem (get_meta_rec cs h) = None /\ m_next (get_meta_rec cs h) <> None
    /\ exists p, m_prev (get_meta_rec cs h) = Some p /\ meta_slot cs p /\ m_mem (get_meta_rec cs p) = None
                 /\ m_next (get_meta_rec cs p) <> None.

Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Definition fact_mw (cs : mstate) : Prop :=
  forall g, mw_ok (get_meta_rec cs g) /\ 0 <= m_avail (get_meta_rec cs g) < 2^32 /\ 0 <= m_freed (get_meta_rec cs g) < 2^32.

Definition fact_host_stride (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b -> 0 <= m_sizeclass (get_meta_rec cs g) <= 27 ->
    get_stride (get_meta_rec cs g) = UNIT * size_class (m_sizeclass (get_meta_rec cs g)).

(* [comment removed for export] *)
Definition fact_links (cs : mstate) : Prop :=
  forall g, lmem cs g ->
    (forall n, m_next (get_meta_rec cs g) = Some n -> m_prev (get_meta_rec cs n) = Some g)
    /\ (forall p, m_prev (get_meta_rec cs g) = Some p -> m_next (get_meta_rec cs p) = Some g).

Definition fact_sc0_full (cs : mstate) : Prop :=
  forall g b gh, m_mem (get_meta_rec cs g) = Some b -> (s_groups cs) !! b = Some gh ->
    m_sizeclass (get_meta_rec cs g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec cs g).

Definition fact_ghdr_unk (st : mstate) : Prop :=
  forall b gh o, (s_groups st) !! b = Some gh -> 0 <= o < 9 ->
    exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h.

(* [comment removed for export] *)
Definition fact_bit_stride (cs : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i ->
    Z.testbit (m_avail (get_meta_rec cs g)) i || Z.testbit (m_freed (get_meta_rec cs g)) i = true ->
    m_sizeclass (get_meta_rec cs g) < 48 ->
    UNIT * size_class (m_sizeclass (get_meta_rec cs g)) <= get_stride (get_meta_rec cs g).

Record LFACTS (cs : mstate) : Prop := mkLF {
  lf_lists : fact_lists cs;
  lf_freelist : fact_freelist cs;
  lf_mw : fact_mw cs;
  lf_host_stride : fact_host_stride cs;
  lf_links : fact_links cs;
  lf_sc0_full : fact_sc0_full cs;
  lf_bit_stride : fact_bit_stride cs
}.

(* [comment removed for export] *)
Record ISTF_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkISTF {
  isf_mf : @MFACTS_g resv st LB;
  isf_lf : LFACTS (strip st);
  isf_ghdr : fact_ghdr_unk st
}.
End ACeilS1.


(* [comment removed for export] *)
Notation ISTF := (@ISTF_g agent_reserved).
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nest_ok (m : aptr) (st3 : mstate) : Prop :=
  get_meta_rec st3 m = meta0
  /\ forall h, c_free_meta_head (ctx st3) = Some h -> h <> m /\ m_prev (get_meta_rec st3 h) <> Some m.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMP_AS_g (resv : list (Z * Z)) (am_pre : mstate -> Prop) : Prop :=
  forall st0 LB st sc st1, AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 -> am_pre st1.
End ACeilS2.

Notation AMP_AS := (AMP_AS_g agent_reserved).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
