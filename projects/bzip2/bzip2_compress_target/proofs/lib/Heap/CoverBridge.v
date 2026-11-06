(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg MmapSim RefNodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep MmFacts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require KStepC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require KStepC MI_Inv MI_Kit MI_Ledger MI_Contracts MTight.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prelim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MSafe OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStep OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MmFacts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC.KLink OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ledger OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MTight.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import TreeBridge TightBridge.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_leaves_cover {A} : forall (t : itree node (exc A)) MD (f : A -> bool) (Tf Tt : TSet),
  (exists a MD', tpath nstep t MD [] (Ok a) MD' /\ f a = true) ->
  (forall tr, Tf tr -> Tt tr) ->
  t_eq (t_leaves t MD (fun a _ => if f a then Tt else Tf)) Tt.
Proof.
  (intros t MD f Tf Tt; cps_intros (a1 & M1 & P1 & F1); intros INCL tr). unfold t_leaves. split.
  - cps_intros (a & MD' & Hp & HT). destruct (f a); [exact HT| exact (INCL _ HT)].
  - intros HT. exists a1, M1. rewrite F1. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma t_leaves_cover_pair {B C} : forall (t : itree node (exc (option B * C))) MD (Tf Tt : TSet),
  (exists b c MD', tpath nstep t MD [] (Ok (Some b, c)) MD') ->
  (forall tr, Tf tr -> Tt tr) ->
  t_eq (t_leaves t MD (fun r _ => match fst r with Some _ => Tt | None => Tf end)) Tt.
Proof.
  (intros t MD Tf Tt; cps_intros (b & c & MD' & Hp); intros INCL).
  pose proof (t_leaves_cover t MD (fun r => match fst r with Some _ => true | None => false end) Tf Tt) as X.
  assert (E : forall r : option B * C, (if match fst r with Some _ => true | None => false end then Tt else Tf)
                                       = match fst r with Some _ => Tt | None => Tf end)
    by (intros [[?|] ?]; reflexivity).
  intros tr. specialize (X ltac:(exists (Some b, c), MD'; split; [exact Hp| reflexivity]) INCL tr).
  unfold t_leaves in *. cbn [fst] in *.
  split.
  - cps_intros (a & M & P & HT). apply (proj1 X). exists a, M. split; [exact P|]. rewrite E. exact HT.
  - intros HT. cps_destruct (proj2 X HT) as (a & M & P & HT'). exists a, M. split; [exact P|]. rewrite E in HT'. exact HT'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma raw_malloc_pure_path : forall (s : PState) (MD : Model) (n : Z) cs' c tr r s' MD',
  cmalloc (ps_m s) n = SRet (cs', Some c) ->
  tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' ->
  tr = [] /\ MD' = MD /\ s' = set_m cs' s /\ r = Some (c, fresh_off cs' c n).
Proof.
  intros s MD n cs' c tr r s' MD' E Hp.
  unfold raw_malloc, mbind, mget in Hp.
  tp_bind Hp. cps_destruct Hp as (tr1 & [s0 s0'] & mo1 & tr2 & H1 & H2 & ->).
  apply tpath_ret_inv in H1 as (E1 & -> & ->). injection E1 as <- <-. cbn [fst snd] in H2.
  tp_bind H2. cps_destruct H2 as (tr3 & [[st' p] s1] & mo2 & tr4 & H3 & H4 & ->).
  rewrite E in H3. cbn [membed] in H3. apply tpath_ret_inv in H3 as (E3 & -> & ->). injection E3 as E3a E3b E3c. subst st' p s1.
  cbn [fst snd] in H4. unfold mupd, mret in H4. tp_bind H4. cps_destruct H4 as (tr5 & [u s4] & mo3 & tr6 & H5 & H6 & ->).
  apply tpath_ret_inv in H5 as (E5 & -> & ->). injection E5 as E5a E5b. subst u s4.
  apply tpath_ret_inv in H6 as (E6 & -> & ->). injection E6 as E6a E6b. subst r s'. auto.
Qed.

Lemma raw_malloc_pure_exists : forall (s : PState) (MD : Model) (n : Z) cs' c,
  cmalloc (ps_m s) n = SRet (cs', Some c) ->
  tpath nstep (raw_malloc n s) MD [] (Ok (Some (c, fresh_off cs' c n), set_m cs' s)) MD.
Proof.
  intros s MD n cs' c E.
  unfold raw_malloc, mbind, mget. apply <- tpath_ebind. right. exists [], (s, s), MD, []. split; [cbn; auto|]. split; [| reflexivity].
  cbn [fst snd]. apply <- tpath_ebind. right. exists [], ((cs', Some c), s), MD, []. split; [rewrite E; cbn; auto|]. split; [| reflexivity].
  unfold mupd, mret. apply <- tpath_ebind. right. exists [], (tt, set_m cs' s), MD, []. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OKX.
Variables (X : list bptr) (G : PState -> Model -> Prop) (s : PState) (MD : Model) (n : Z).
Variables (QF : Malloc.M (mstate * option cptr) -> Prop) (QS : Z -> Malloc.M (mstate * option cptr) -> Prop).
Variables (PS : Z -> mstate * option cptr -> Prop).
Hypothesis HO : OWNX X G s MD.
Hypothesis Hn : 0 <= n.
Hypothesis MM : MMAP1 (live_ranges (ps_m s)) (cmalloc (ps_m s) n) QF QS.
Hypothesis HS : forall z t, QS z t -> exists x, t = SRet x /\ PS z x.
Hypothesis HLEN : forall len K, cmalloc (ps_m s) n = SVis (EMmap 0 len PROT_RW MAPF) K -> len <= 2^27 - 4096.

Lemma raw_malloc_ok_exists27 :
  (forall z x, PS z x -> exists c, snd x = Some c) ->
  Forall (fun p => bv_unsigned (snd p) <= 2^35) (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD))) <= 1000 ->
  vm_backing_used MD + 2^27 <= vm_limit (m_vmmaps MD) ->
  exists p s' MD', tpath nstep (raw_malloc n s) MD [] (Ok (Some p, s')) MD'.
Proof.
  intros HPS SZ CNT BUD.
  cps_destruct MM as (len & K & E & Hlen & KF & KS).
  pose proof (HLEN len K E) as L27.
  destruct HO as [(L & SR & HK & Hincl) [Hnd HG]].
  pose proof (cmalloc_contract_sim (ps_m s) L n SR Hn) as CT. rewrite E in CT. cbn [ctree_ok] in CT. destruct CT as [PRE _].
  cbn [event_pre] in PRE.
  assert (QUIET : brk_quiet L /\ 0 < len < LEN_MAX).
  { destruct PRE as [(Q & _ & _ & _ & B)|(cur & _ & _ & _ & _ & AB)]; [auto|]. exfalso. unfold MAPF, MAPFX in AB. cbv in AB. lia. }
  destruct QUIET as [QUIET LENMAX].
  pose proof (mmap_len_ge len ltac:(lia)) as ML.
  assert (ML2 : mmap_len len <= 2^27) by lia.
  destruct (grant_exists_big (Z_to_bv 64 0) MD (mmap_len len) (kl_atop _ _ _ HK) ltac:(lia) SZ CNT ltac:(lia)) as [a GA].
  pose proof (nstep_mmap_grant len MD a ltac:(lia) GA) as NS.
  set (mo4 := with_vmmaps _ MD) in NS.
  cps_pose (nstep_dec_mmap len [] MD _ mo4 [] (kl_atop _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(constructor) NS) as (_ & VO & LZ & x & DX & CX).
  destruct x as [e|z].
  { exfalso. revert DX. cbn -[mmap_addr_ok mmap_len bv_eqb]. rewrite !bv_eqb_refl. cbn [andb]. destruct (mmap_addr_ok _ _ _); discriminate. }
  cps_destruct CX as (AOK & RF & VM4).
  assert (KLh : m_halted MD = None /\ m_vm_lazy MD = []) by (split; [exact (kl_halt _ _ _ HK)| exact (kl_lazy _ _ _ HK)]).
  assert (Hh4 : m_halted mo4 = None) by (rewrite (vm_only_halted _ _ VO); exact (proj1 KLh)).
  assert (Hl4 : m_vm_lazy mo4 = []) by (apply LZ; exact (proj2 KLh)).
  cps_pose (KL_mmap_new L (ps_brk s) MD mo4 z len false HK QUIET LENMAX AOK RF Hl4 Hh4 VM4) as (_ & AOK2 & NERR).
  cps_destruct SR as (st & BL & LS & Est & INV & _).
  rewrite (mmap_answer_ok_eq x0 st L (proj1 INV)) in AOK2. rewrite <- Est, live_ranges_strip in KS.
  cps_destruct (HS _ _ (KS _ AOK2 NERR)) as ([xst xp] & EK & HPSx). destruct (HPS _ _ HPSx) as [c Hc]. cbn in Hc. subst xp.
  exists (c, fresh_off xst c n), (set_m xst s), mo4.
  unfold raw_malloc, mbind, mget. apply <- tpath_ebind. right. exists [], (s, s), MD, []. split; [cbn; auto|]. split; [| reflexivity].
  cbn [fst snd]. apply <- tpath_ebind. right. exists [], ((xst, Some c), s), mo4, []. split.
  - rewrite E. cbn [membed]. unfold mbind. apply <- tpath_ebind. right. exists [], (z, s), mo4, []. split.
    + unfold ev_step. cbn -[msys mret mbind Z.to_nat neg_errno]. unfold mbind. apply <- tpath_ebind. right.
      exists [], (MmOk z, s), mo4, []. split; [| split; [cbn; auto| reflexivity]].
      unfold msys. apply <- tpath_enode. eexists. split; [exact NS|]. rewrite DX. reflexivity.
    + split; [| reflexivity]. rewrite EK. cbn. auto.
  - split; [| reflexivity]. unfold mupd, mret. apply <- tpath_ebind. right. exists [], (tt, set_m xst s), mo4, []. cbn. repeat split; reflexivity.
Qed.
End OKX.

End ACeilS1.
