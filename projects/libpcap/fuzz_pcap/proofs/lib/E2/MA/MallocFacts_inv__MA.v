(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WSlot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocCls__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MallocFacts_inv.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.MI_Realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.LB_WRealloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocCls__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocCls__MA.MallocReS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof.
  intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

#[using="Type"] Lemma conc_aadd st p d : (exists r, s_regions st !! fst p = Some r) -> conc st (aadd p d) = conc st p + d.
Proof. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.

#[using="Type"] Lemma conc_same st st' p : (exists r, s_regions st !! fst p = Some r /\ s_regions st' !! fst p = Some r) -> conc st' p = conc st p.
Proof. intros (r & H1 & H2). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.

#[using="Type"] Lemma event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w|oa ol nl]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
  - destruct (is_err z); reflexivity.
Qed.
#[using="Type"] Lemma cpath_resv {R} L (t : M R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_resv. Qed.

#[using="Type"] Lemma Forall2_In_l {A B} (P : A -> B -> Prop) l1 l2 a : Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists y; split; [left; reflexivity| exact Hxy]|].
  destruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
Qed.

#[using="Type"] Lemma Forall2_impl_in {A B} (P Q : A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros HPQ; constructor.
  - apply HPQ; [left; reflexivity| left; reflexivity| exact Hxy].
  - apply IH. intros a b Ha Hb. apply HPQ; right; assumption.
Qed.

#[using="Type"] Lemma Forall2_filter {A B} (P : A -> B -> Prop) (p : A -> bool) (q : B -> bool) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> p a = q b) -> Forall2 P (filter p l1) (filter q l2).
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros E; cbn; [constructor|].
  rewrite (E _ _ Hxy). destruct (q y); [constructor; [exact Hxy| apply IH; exact E]| apply IH; exact E].
Qed.

#[using="Type"] Lemma Forall2_map_eq {A B C} (P : A -> B -> Prop) (f : A -> C) (g : B -> C) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> f a = g b) -> map f l1 = map g l2.
Proof. induction 1; intros E; cbn; [reflexivity|]. rewrite (E _ _ H). f_equal. apply IHForall2. exact E. Qed.

#[using="Type"] Lemma filter_id {A} (p : A -> bool) l : (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

#[using="Type"] Lemma bl_remove_filter c BL : NoDup (map bslot BL) ->
  bl_remove c BL = filter (fun k => negb (aptr_eqb (bslot k) c)) BL.
Proof.
  induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
  cbn in ND. apply NoDup_cons in ND as [NI ND].
  destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
  - symmetry. apply filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
    exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
  - f_equal. apply IH. exact ND.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem areach_inv resv st LB : AREACH_from resv st LB ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = msecret /\ CORR st LB BL.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma areach_malloc_some {resv} : forall st LB n (o o' : list Z) ans st' (pf : aptr) cst (c : cptr) (off : Z),
    AREACH_from resv st LB -> 0 <= n ->
    follow (lrun o (malloc st n)) ans = Some (o', (st', Some pf)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    pf = aadd c (UNIT * off) ->
    AREACH_from resv st' (((c, off), conc st' pf, n) :: LB).
Proof.
  intros st LB n o o' ans st' pf cst c off (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hn FF FC Epf.
    destruct (malloc_sim pans_l pupd_l pans_l_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
    unfold lrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc.
    destruct RES as (off' & LS' & Epf' & Hoff & INV' & NI).
    assert (Eoff : off = off').
    { rewrite Epf in Epf'. unfold aadd in Epf'. apply (f_equal snd) in Epf'. cbn [snd] in Epf'. unfold UNIT in Epf'. lia. }
    subst off'.
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr blk_id bslot boff fst snd]. split; [|reflexivity]. rewrite Epf. apply conc_aadd.
      destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _). exists r. exact Hr.
    + eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [|exact C4]. rewrite C3.
      rewrite (conc_same st st' (bslot k)); [reflexivity|].
      destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

#[using="Type"] Lemma areach_malloc_none {resv} : forall st LB n (o o' : list Z) ans st',
    AREACH_from resv st LB -> 0 <= n ->
    follow (lrun o (malloc st n)) ans = Some (o', (st', None)) ->
    AREACH_from resv st' LB.
Proof.
  intros st LB n o o' ans st' (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hn FF.
    destruct (malloc_sim pans_l pupd_l pans_l_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
    destruct rc as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot BL) L'), LS', BL.
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    eapply Forall2_impl_in; [exact CR|]. intros bb k Hb Hk (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [|exact C4]. rewrite C3.
    rewrite (conc_same st st' (bslot k)); [reflexivity|].
    destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

#[using="Type"] Lemma areach_free {resv} : forall st LB (b : block) (o o' : list Z) ans st',
    AREACH_from resv st LB -> In b LB ->
    follow (lrun o (free st (Some (blk_ptr b)))) ans = Some (o', st') ->
    AREACH_from resv st' (filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
Proof.
  intros st LB b o o' ans st' (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hb FF.
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3 & C4)).
    destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3, C4.
    destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
    assert (Epf : blk_ptr b = aadd c (UNIT * off)).
    { unfold blk_ptr. rewrite C1, C4. reflexivity. }
    rewrite Epf in FF.
    destruct (free_sim pans_l pupd_l pans_l_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV').
    destruct (free_leaf_facts pans_l pupd_l st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
    set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
    exists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    rewrite C1.
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                  ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3 & D4). split; [exact D1|]. split; [exact D2|]. split; [|exact D4]. rewrite D3.
    rewrite (conc_same st st' (bslot k')); [reflexivity|].
    rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
    destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma areach_realloc {resv} : forall st LB (b : block) n' (o o' : list Z) ans st' (r : optr),
    AREACH_from resv st LB -> In b LB -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX ->
    follow (lrun o (realloc st (Some (blk_ptr b)) n')) ans = Some (o', (st', r)) ->
    match r with
    | None => AREACH_from resv st' LB
    | Some q => exists (c' : cptr) (off' : Z), q = aadd c' (UNIT * off') /\ 0 <= off' <= 255
                /\ (c' = blk_slot b \/ forall b', In b' LB -> c' <> blk_slot b')
                /\ AREACH_from resv st' (((c', off'), conc st' q, n') :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB)
    end.
Proof.
  intros st LB b n' o o' ans st' r (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hb Hn' Hov Hnx FF.
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3 & C4)).
  destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3, C4.
  assert (Epf : blk_ptr b = aadd c (UNIT * off)).
  { unfold blk_ptr. rewrite C1, C4. reflexivity. }
  rewrite Epf in FF.
  pose proof (ftree_prun pans_l pupd_l pans_l_range (realloc st (Some (aadd c (UNIT * off))) n') L _ o
                (realloc_ftS st L BL LS c off n n' INV Hk Hn' Hov Hnx)) as PT.
  unfold lrun in FF. destruct (ptree_follow_lafter _ L _ ans PT FF) as [CP POST]. cbn [fst snd] in POST.
  destruct POST as (RP & CS & SEC'). unfold realloc_post in RP. cbn [fst snd] in RP, CS, SEC'.
  set (L' := lafter L _ ans) in *.
  pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND.
  destruct r as [q|].
  - destruct RP as (c' & off' & LS' & Eq & Hoff & INV' & Hc').
    exists c', off'. split; [exact Eq|]. split; [exact Hoff|]. split.
    { destruct Hc' as [E|NI]; [left; rewrite C1; exact E| right]. intros b' Hb' E'.
      destruct (Forall2_In_l _ _ _ _ CR Hb') as (k' & Hk' & (D1 & _)). apply NI. rewrite E', D1. apply in_map. exact Hk'. }
    exists (set_live (map bslot (((c', off'), n') :: bl_remove c BL)) L'), LS', (((c', off'), n') :: bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr blk_id bslot boff fst snd]. split; [|reflexivity]. rewrite Eq.
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable.conc_aadd. unfold get_region.
      destruct (blk_region _ _ _ _ _ ((c', off'), n') INV' ltac:(left; reflexivity)) as (rg & Hr & _). cbn [bslot fst snd] in Hr. rewrite Hr.
      unfold conc, get_region. rewrite Hr. lia.
    + rewrite (bl_remove_filter c BL ND). rewrite C1.
      pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                    ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
      eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3 & D4). split; [exact D1|]. split; [exact D2|]. split; [|exact D4]. rewrite D3.
      rewrite <- (bl_remove_filter c BL ND) in Hk'.
      pose proof (CS k' 0 Hk') as E0. unfold aadd in E0. rewrite Z.add_0_r in E0. rewrite <- surjective_pairing in E0. rewrite E0. reflexivity.
  - destruct RP as (LS' & INV').
    exists (set_live (map bslot BL) L'), LS', BL.
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    eapply Forall2_impl_in; [exact CR|]. intros b' k' Hb' Hk' (D1 & D2 & D3 & D4). split; [exact D1|]. split; [exact D2|]. split; [|exact D4]. rewrite D3.
    pose proof (CS k' 0 Hk') as E0. unfold aadd in E0. rewrite Z.add_0_r in E0. rewrite <- surjective_pairing in E0. rewrite E0. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_l pupd_l st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
  intros resv st LB blk off AR Hb Ho Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3 & C4)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3, C4. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off.
  exact (INVL_hdr_ok pans_l pupd_l st L BL LS c bo n INV Hk).
Qed.

End PORT.

End WithCeil.
End MallocFacts_inv.

(* [comment removed for export] *)
Module MallocFacts_inv2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma NoDup_map_on {A B} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  induction l as [|a l IH]; intros Hinj ND; cbn; [constructor|].
  inversion ND; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy).
    rewrite (Hinj a y ltac:(now left) ltac:(now right) (eq_sym Ey)) in H1. exact (H1 Hy).
  - apply IH; [| assumption]. intros x y Hx Hy. apply Hinj; now right.
Qed.

#[using="Type"] Lemma NoDup_Z_length (l : list Z) (N : Z) : 0 <= N -> List.NoDup l -> (forall x, In x l -> 0 <= x < N) -> Z.of_nat (length l) <= N.
Proof.
  intros Hn ND HB.
  assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat N)))).
  { intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (HB x Hx). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length ND INCL) as Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

#[using="Type"] Lemma zsum_bound (l : list Z) (K : Z) : (forall x, In x l -> 0 <= x <= K) -> 0 <= zsum l <= K * Z.of_nat (length l).
Proof.
  induction l as [|a l IH]; intros HB; cbn -[Z.of_nat]; [lia|].
  pose proof (HB a ltac:(now left)). specialize (IH ltac:(intros x Hx; apply HB; now right)).
  unfold zsum in IH. rewrite Nat2Z.inj_succ. lia.
Qed.

Section MF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
#[using="CEILV X L BL LS INV ZB IM"] Lemma mem_hosts g b : m_mem (MR st g) = Some b -> hosts st b g.
Proof. intros H. destruct (im_group _ _ _ IM g b H) as [Hh|Hz]; [exact Hh|]. rewrite ZB in Hz. destruct Hz. Qed.

#[using="CEILV L BL INV IG"] Lemma hosts_GO b g : hosts st b g -> exists ai, s_groups st !! b = Some (mkGhdr (Some g) ai) /\ group_ok X st LS g b ai.
Proof. intros H. exact (hosts_ok _ _ _ IG _ _ H). Qed.

#[using="Type"] Lemma sstart_of_eq r i : sstart_of r i = sstart r i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="CEILV X L BL LS INV IM IG IS"] Lemma group_in_region b m : hosts st b m ->
  exists r, s_regions st !! fst b = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ gend (MR st m) <= round_up_pg (r_len r).
Proof.
  intros Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Z0|NZ].
  - destruct (top_chain _ _ _ _ IM IG IS m b Hm Z0) as (t & i & c & bt & Ha & Ht & Htl & Hf).
    destruct (anc_box _ _ _ _ IM IG IS m t i c b Ha Hm) as (B1 & B2 & B3).
    destruct (anc_facts _ _ _ _ IM IG IS m t i c Ha) as (bm & bp & Hm' & Hp' & _ & Hi & _).
    pose proof (hosts_inj _ _ _ IM _ _ _ Ht Hp'); subst bp.
    destruct (hosts_GO _ _ Ht) as (ait & Hbt & GOt).
    destruct (g_top _ _ _ _ _ _ GOt Htl) as (S0 & r & Hr & Kr & ML & GE).
    rewrite <- Hf. exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|].
    pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st t) + 1) Ht ltac:(lia)) as SM. rewrite <- gend_eq in SM. lia.
  - destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE). exists r. repeat split; auto. lia.
Qed.

#[using="CEILV X L BL LS INV IM IG IS"] Lemma conc_group b m : hosts st b m -> exists r, s_regions st !! fst b = Some r /\ r_kind r = RKGroup /\
  conc st b = r_base r + snd b /\ r_base r <= conc st b /\ conc st b + 32 <= r_base r + round_up_pg (r_len r).
Proof.
  intros Hm. destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). pose proof (gend_ge _ _ _ IM IG _ _ Hm) as G32.
  exists r. unfold conc, get_region. rewrite Hr. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="CEILV X L BL LS INV IA"] Lemma f_ctx : fact_ctx (strip st).
Proof.
  pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
  unfold fact_ctx. rewrite ctx_strip. unfold ctx.
  split; [exact C1|]. split; [destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia|].
  split; [destruct S2 as [(E & _)|[E _]]; rewrite E; auto|]. split; [exact C2|].
  split.
  - intros i. unfold bounces, ctx. cbn. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)).
  - intros i. unfold unmap_seq, ctx. cbn. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)).
Qed.

#[using="CEILV X L BL LS INV IM IL"] Lemma f_active : fact_active (strip st).
Proof.
  intros sc g H. rewrite active_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
  pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
  destruct (il_active _ _ IL sc g Hin) as (Hsc & [b Hb] & Esc). split; [exact Hsc|]. split; [exact Esc|].
  rewrite (hosts_mem _ _ _ IM _ _ Hb). discriminate.
Qed.

#[using="CEILV X L BL LS INV ZB IM IG"] Lemma f_masks : fact_masks (strip st).
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
  destruct (hosts_GO _ _ (mem_hosts _ _ H)) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  split; [intros i Hi Ha; pose proof (M3 i Hi Ha); lia|]. split; [exact M4|].
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.testbit (m_avail (MR st g)) i) eqn:Ea; destruct (Z.testbit (m_freed (MR st g)) i) eqn:Ef; try reflexivity.
  exfalso. exact (M5 i Hi Ea Ef).
Qed.

#[using="CEILV X L BL LS INV ZB IR IM IG"] Lemma f_maplen : fact_maplen (strip st).
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
  destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
  destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE).
  destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). ceil_facts. lia.
Qed.

#[using="CEILV X L BL LS INV IM IS"] Lemma f_slots : fact_slots (strip st).
Proof.
  intros p g idx H. rewrite s_slots_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
  destruct (is_valid _ _ _ IS _ _ _ H) as ([b Hb] & Hi & Ep). exists b. split; [exact (hosts_mem _ _ _ IM _ _ Hb)|].
  rewrite (slot_start'_eq _ _ _ IM _ _ idx Hb) in Ep. rewrite Ep. cbn. rewrite sstart_of_eq. auto.
Qed.

#[using="CEILV X L BL LS INV ZB IM IS"] Lemma f_slots_complete : fact_slots_complete (strip st).
Proof.
  intros g b i H Hi. rewrite s_slots_strip. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_hosts _ _ H) as Hm. rewrite sstart_of_eq, <- (slot_start'_eq _ _ _ IM _ _ i Hm). exact (is_total _ _ _ IS _ _ _ Hm Hi).
Qed.

#[using="CEILV X L BL LS INV ZB IM ISH"] Lemma f_hdr0 : fact_hdr0 st.
Proof.
  intros g b i H Hi. fold (MR st g) in *. rewrite sstart_of_eq. exact (ish_hdr0 _ _ ISH b g i (mem_hosts _ _ H) ltac:(unfold cnt_of; lia)).
Qed.

#[using="CEILV X L BL LS INV ISH"] Lemma f_cell_ticks : fact_cell_ticks st.
Proof. intros rid sh o v t Hs Hc. exact (proj2 (proj1 (ish_ticks _ _ ISH rid sh Hs) o v t Hc)). Qed.

#[using="CEILV X L BL LS INV ISH"] Lemma f_ticks : ticks_ok st.
Proof.
  split.
  - intros rid sh u hl ch Hs Hu Hin. exact (proj1 (proj2 (ish_ticks _ _ ISH rid sh Hs)) u hl ch Hu Hin).
  - intros rid sh pg t Hs Hp. exact (proj2 (proj2 (ish_ticks _ _ ISH rid sh Hs)) pg t Hp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="CEILV X L BL LS INV ZB NFR IA IM IG IS"] Lemma f_gmeta : fact_gmeta (strip st).
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
  pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  assert (AV : m_avail (MR st g) < 2 ^ 32).
  { apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
  assert (FR : m_freed (MR st g) < 2 ^ 32).
  { apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
  split.
  { (* [comment removed for export] *) pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
    destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). exists a, ar, ka. rewrite s_areas_strip. split; [exact Ha|]. split; [exact Hka|]. exact Emk. }
  split; [lia|]. split; [lia|]. split; [exact LI|]. split; [exact (g_freeable _ _ _ _ _ _ GO)|].
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
  split. { destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia]. }
  split; [exact ML|].
  split. { exists ai. rewrite s_groups_strip. split; [exact Hb|]. split; [exact AI|]. exact M3. }
  split. { destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). exists r. rewrite s_regions_strip.
           pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|]. rewrite sstart_of_eq. rewrite gend_eq in GE. exact GE. }
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
  split; [exact SG|]. split; [exact SM|].
  pose proof (g_stride _ _ _ _ _ _ GO) as GS.
  split. { intros Hsc. destruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. nia. }
  split. { intros Hsc i Hi Ht. destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| lia].
           exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 _]. rewrite A0 in Ht. rewrite Z.bits_0 in Ht. discriminate. }
  intros Hsc. destruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. lia.
Qed.

(* [comment removed for export] *)
#[using="CEILV X L LS INV IM IS"] Lemma bit_slot_nonH g b ai i : s_groups st !! b = Some (mkGhdr (Some g) ai) -> 0 <= i <= m_last_idx (MR st g) ->
  (Z.testbit (m_avail (MR st g)) i = true \/ Z.testbit (m_freed (MR st g)) i = true) ->
  s_groups st !! (fst b, sstart (MR st g) i) = None /\ ~ In (fst b, sstart (MR st g) i) (map bslot BL).
Proof.
  intros Hb Hil Hbits. assert (Hm : hosts st b g) by (exists ai; exact Hb).
  pose proof (is_part _ _ _ IS b g ai i Hb Hil) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm) in P.
  unfold one5, tbit in P. destruct P as (_ & nAB & nAC & nAD & _ & nBC & nBD & _).
  split.
  - destruct (s_groups st !! (fst b, sstart (MR st g) i)) eqn:E; [| reflexivity]. exfalso.
    destruct Hbits as [A|F]; [apply nAD| apply nBD]; split; auto; intros Y; rewrite Y in E; discriminate E.
  - intros C. destruct Hbits as [A|F]; [apply nAC| apply nBC]; split; auto.
Qed.

#[using="CEILV X L BL LS INV IM"] Lemma hdr_hosts b gh : s_groups st !! b = Some gh -> exists m, hosts st b m.
Proof.
  intros Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _). exists m. destruct gh as [gm gai]; cbn in Eg; subst gm. exists gai. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable LB : list block.
Hypothesis CR : CORR st LB BL.

#[using="CR"] Lemma LB_blk blk : In blk LB -> exists c off n, In ((c, off), n) BL /\ blk_slot blk = c /\ blk_size blk = n /\ blk_addr blk = conc st c + UNIT * off.
Proof.
  intros Hb. destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3 & C4)). destruct k as [[c off] n].
  exists c, off, n. cbn [bslot boff bsize fst snd] in C1, C2, C3. auto.
Qed.

(* [comment removed for export] *)
#[using="CEILV X L LS INV IG CR"] Lemma LB_geo blk : In blk LB -> exists c off n m bm i r,
  In ((c, off), n) BL /\ blk_slot blk = c /\ blk_size blk = n /\
  hosts st bm m /\ 0 <= i <= m_last_idx (MR st m) /\ c = (fst bm, sstart (MR st m) i) /\ s_groups st !! c = None /\
  s_regions st !! (fst bm) = Some r /\ r_kind r = RKGroup /\
  blk_addr blk = r_base r + sstart (MR st m) i + UNIT * off /\ 0 <= off /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB.
Proof.
  intros Hb. destruct (LB_blk _ Hb) as (c & off & n & Hk & C1 & C2 & C3).
  destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh. assert (Hm : hosts st bm m) by (exists ai; exact Hh).
  destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr).
  exists c, off, n, m, bm, i, r.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as Hf.
  repeat split; auto; try lia.
  rewrite C3, Ec. unfold conc, get_region. cbn [fst snd]. rewrite Hr. lia.
Qed.

#[using="CEILV X L BL LS INV ZB IM IG IS CR"] Lemma f_free_clear : fact_free_clear (strip st) LB.
Proof.
  change (fact_free_clear st LB). intros g b i H Hi Hbits. fold (MR st g) in *. cbn zeta. rewrite !sstart_of_eq.
  pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hil : 0 <= i <= m_last_idx (MR st g)). { destruct Hbits as [A|F]; [pose proof (M3 i Hi A); lia | pose proof (M4 i Hi F); lia]. }
  destruct (bit_slot_nonH _ _ _ _ Hb Hil Hbits) as [NH NB].
  pose proof (sstart_succ st g i) as SS.
  split.
  - intros b' gh Hb' Hf. destruct (hdr_hosts _ _ Hb') as [m' Hm'].
    destruct (sep_ghdr _ _ _ _ IM IG IS g b i Hm Hil NH m' b' Hm' Hf) as [A|A]; unfold IB; lia.
  - intros blk Hblk Hf. destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr & Kr & Ea & Ho & Hn & Fit).
    rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr. exists r. split; [reflexivity|].
    rewrite Ea, C2. pose proof (sstart_succ st m2 i2) as SS2.
    assert (NE : m2 <> g \/ i2 <> i). { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NB. rewrite <- Hf, <- Ec, <- C1.
      destruct (Forall2_In_l _ _ _ _ CR Hblk) as (k & HkB & (Ek & _)). rewrite Ek. apply in_map. exact HkB. }
    destruct (sep_ext _ _ _ _ IM IG IS g b i Hm Hil NH m2 b2 i2 Hm2 Hf Hi2 NE ltac:(rewrite Ec in NH2; exact NH2)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

#[using="CEILV X L BL LS INV ZB IM IG IS CR"] Lemma f_avail_clear : fact_avail_clear (strip st) LB.
Proof. intros g b i H Hi Ha. exact (f_free_clear g b i H Hi (or_introl Ha)). Qed.

#[using="CEILV X L BL LS INV IM IG IS CR"] Lemma f_hdr_clear : fact_hdr_clear (strip st) LB.
Proof.
  change (fact_hdr_clear st LB). intros b gh blk r Hb Hblk Hf Hr.
  destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r' & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr' & Kr & Ea & Ho & Hn & Fit).
  rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr' in Hr. inversion Hr; subst r'.
  destruct (hdr_hosts _ _ Hb) as [m' Hm']. rewrite Ea, C2. pose proof (sstart_succ st m2 i2).
  rewrite Ec in NH2. destruct (sep_ghdr _ _ _ _ IM IG IS m2 b2 i2 Hm2 Hi2 NH2 m' b Hm' (eq_sym Hf)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

#[using="CEILV X L BL LS INV IS ISH CR"] Lemma f_blk_unknown : fact_blk_unknown st LB.
Proof.
  intros blk r Hblk Hr a Ha. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
  destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & _). cbn [bslot fst snd] in Hs.
  pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (_ & _ & _ & _ & _ & _ & _ & U). cbn [bslot boff bsize fst snd] in U.
  rewrite C1 in Hr |- *. rewrite C3, C2 in Ha. unfold conc, get_region in Ha. rewrite Hr in Ha.
  destruct (U (a - r_base r) ltac:(lia)) as [h Hh]. exists h. exact Hh.
Qed.

#[using="CEILV X L BL LS INV IM IG IS CR"] Lemma f_blocks_disjoint : fact_blocks_disjoint st LB.
Proof.
  intros b1 b2 H1 H2 Hf NE.
  destruct (LB_geo _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1).
  destruct (LB_geo _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
  rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
  rewrite A1, A2, S1, S2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
  assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
  rewrite E1 in N1. rewrite E2 in N2.
  destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

#[using="CEILV X L BL LS INV IG CR"] Lemma LB_blocks_ok : Forall (block_ok st) LB.
Proof.
  apply List.Forall_forall. intros blk Hblk. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
  destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh.
  constructor.
  - exists m, i. rewrite C1. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. fold (MR st m).
    split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|].
    split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|].
    exists off. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). rewrite C2, C3. repeat split; lia.
  - rewrite C1. destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr). rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [fst]. exists r. auto.
  - rewrite C2. exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
Qed.

#[using="CEILV X st L BL LS INV IS CR"] Lemma LB_nodup : List.NoDup (map blk_slot LB).
Proof.
  rewrite (Forall2_map_eq (corr1 st) blk_slot bslot LB BL CR ltac:(intros a b (E & _); exact E)).
  apply NoDup_ListNoDup. exact (is_nodup _ _ _ IS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="CEILV X L BL LS INV IR"] Lemma region_rid rid r : s_regions st !! rid = Some r -> (rid < s_next_rid st)%N.
Proof. exact (ir_ids _ _ _ IR rid r). Qed.
#[using="CEILV X L BL LS INV IR IA"] Lemma area_rid a ar : s_areas st !! a = Some ar -> (fst a < s_next_rid st)%N.
Proof. intros Ha. destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & _) & _). exact (region_rid _ _ Hr). Qed.
#[using="CEILV X L BL LS INV IR IA"] Lemma area_rid' a : s_areas st !! a <> None -> (fst a < s_next_rid st)%N.
Proof. intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [exact (area_rid _ _ E)| congruence]. Qed.
#[using="CEILV X L BL LS INV IR IA"] Lemma present_rid m : s_metas st !! m <> None -> (fst m < s_next_rid st)%N.
Proof.
  intros Hm. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
  destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). unfold mslot, aadd. cbn [fst]. exact (area_rid _ _ Ha).
Qed.
#[using="Type"] Lemma nonzero_present m : MR st m <> meta0 -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; congruence. Qed.
#[using="CEILV X L BL INV IR IA"] Lemma listed_rid m h : In m (LS h) -> (fst m < s_next_rid st)%N.
Proof. intros H. apply present_rid. exact (listed_present _ _ _ _ _ INV m h H). Qed.
#[using="CEILV X L BL LS INV IR IG"] Lemma hosts_rid b m : hosts st b m -> (fst b < s_next_rid st)%N.
Proof. intros [ai Hb]. destruct (ig_region _ _ _ IG _ _ Hb) as (r & Hr & _). exact (region_rid _ _ Hr). Qed.

#[using="CEILV X L BL LS INV ZB IR IA IM IL IG ISH"] Lemma f_ptrs : fact_ptrs st.
Proof.
  split.
  - unfold ptrs_in. cbn zeta.
    assert (HD : forall h, optr_in (fun rid => (rid < s_next_rid st)%N) (get_head st h)).
    { intros h. destruct (get_head st h) as [a|] eqn:E; cbn; [| exact I]. exact (listed_rid _ _ (head_listed _ _ _ _ _ INV h a E)). }
    split; [exact (HD LFree)|].
    split. { destruct (c_avail_meta (ctx st)) as [q|] eqn:E; cbn; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & _). exact (region_rid _ _ Hr). }
    split. { destruct (c_meta_area_head (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_head _ IA q E)). }
    split. { destruct (c_meta_area_tail (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_tail _ IA q E)). }
    split. { destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:E; cbn; [| exact I].
             destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). destruct (CU rid off E) as (r & Hr & _). exact (region_rid _ _ Hr). }
    split; [intros sc; exact (HD (LActive sc))|].
    split. { pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (c_brk (s_ctx st)) as [| |rid off]; try exact I.
             destruct BR as (_ & r & Hr & _). exact (region_rid _ _ Hr). }
    split.
    { intros g. fold (MR st g). pose proof (il_link _ _ IL g) as [[L1 L2] L3].
      assert (NX : forall x, m_next (MR st g) = Some x -> (fst x < s_next_rid st)%N).
      { intros x Hx. destruct (L2 ltac:(rewrite Hx; discriminate)) as [h Hh]. exact (listed_rid _ _ (next_listed _ _ _ _ _ INV h g x Hh Hx)). }
      split. { destruct (m_prev (MR st g)) as [p|] eqn:Ep; cbn; [| exact I].
               destruct (m_next (MR st g)) as [x|] eqn:Ex; [| discriminate (L3 eq_refl)].
               destruct (L2 ltac:(discriminate)) as [h Hh]. exact (listed_rid _ _ (prev_listed _ _ _ _ _ INV h g p Hh Ep)). }
      split. { destruct (m_next (MR st g)) as [x|] eqn:Ex; cbn; [| exact I]. exact (NX x eq_refl). }
      destruct (m_mem (MR st g)) as [b|] eqn:Eb; cbn; [| exact I]. exact (hosts_rid _ _ (mem_hosts _ _ Eb)). }
    split.
    { intros a ar Ha. split; [exact (area_rid _ _ Ha)|]. destruct (a_next ar) as [a'|] eqn:E; cbn; [| exact I].
      destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_rid' _ (NXT a' E)). }
    intros b gh Hb. destruct (hdr_hosts _ _ Hb) as [m Hm]. split; [exact (hosts_rid _ _ Hm)|].
    destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _). rewrite Eg. cbn. apply present_rid. apply nonzero_present. intros E. rewrite E in Hmem. cbn in Hmem. discriminate.
  - intros rid Hrid. split.
    + destruct (s_regions st !! rid) as [r|] eqn:E; [| reflexivity]. pose proof (region_rid _ _ E). lia.
    + destruct (s_shadow st !! rid) as [sh|] eqn:E; [| reflexivity]. destruct (ish_dom _ _ ISH _ _ E) as (r & Hr & _). pose proof (region_rid _ _ Hr). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="CEILV X L BL LS INV IR IM IG IS"] Lemma conc_group_inj b1 b2 m1 m2 : hosts st b1 m1 -> hosts st b2 m2 -> conc st b1 = conc st b2 -> b1 = b2.
Proof.
  intros H1 H2 E.
  destruct (conc_group _ _ H1) as (r1 & R1 & K1 & C1 & LO1 & HI1). destruct (conc_group _ _ H2) as (r2 & R2 & K2 & C2 & LO2 & HI2).
  destruct (N.eq_dec (fst b1) (fst b2)) as [Ef|NEf].
  - rewrite Ef, R2 in R1. inversion R1; subst r1. apply injective_projections; [exact Ef| lia].
  - exfalso. pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NEf) as D. unfold region_live_range in D. rewrite K1, K2 in D. lia.
Qed.

#[using="X L BL LS INV IR IM IG IS"] Lemma groups_count : Z.of_nat (length (map_to_list (s_groups st))) <= alloc_ceiling.
Proof.
  rewrite <- (length_map (fun bh : aptr * ghdr => conc st (fst bh))).
  assert (HIN : forall bh, In bh (map_to_list (s_groups st)) -> s_groups st !! (fst bh) = Some (snd bh)).
  { intros [b h] Hin. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  apply NoDup_Z_length; [ceil_facts; lia| |].
  - apply NoDup_map_on.
    + intros [b1 h1] [b2 h2] I1 I2 E. cbn in E. pose proof (HIN _ I1) as G1. pose proof (HIN _ I2) as G2. cbn in G1, G2.
      destruct (hdr_hosts _ _ G1) as [m1 Hm1]. destruct (hdr_hosts _ _ G2) as [m2 Hm2].
      pose proof (conc_group_inj _ _ _ _ Hm1 Hm2 E) as Eb. subst b2. rewrite G1 in G2. inversion G2. reflexivity.
    + pose proof (NoDup_fst_map_to_list (s_groups st)) as ND. apply NoDup_ListNoDup in ND.
      apply (NoDup_map_inv fst). exact ND.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as ([b h] & <- & Hin). cbn. pose proof (HIN _ Hin) as G. cbn in G.
    destruct (hdr_hosts _ _ G) as [m Hm]. destruct (conc_group _ _ Hm) as (r & Hr & Kr & C & LO & HI).
    destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CE & _). lia.
Qed.

#[using="CEILV X L BL LS INV ZB IR IM IG IS"] Lemma gcnt_bound sc : 0 <= gcnt st sc < 2 ^ 60.
Proof.
  unfold gcnt.
  pose proof (zsum_bound (map (fun bh : aptr * ghdr => match g_meta (snd bh) with
     | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0 | None => 0 end) (map_to_list (s_groups st))) 32) as ZS.
  rewrite length_map in ZS. pose proof groups_count as GC. ceil_facts.
  eassert (H : _); [| specialize (ZS H); lia].
  intros x Hx. apply in_map_iff in Hx. destruct Hx as ([b h] & <- & Hin). cbn.
  assert (G : s_groups st !! b = Some h). { apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  destruct (im_hdr _ _ _ IM _ _ G) as (m & Eg & Hmem & AI). rewrite Eg.
  destruct (hosts_GO _ _ (mem_hosts _ _ Hmem)) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of.
  destruct (m_sizeclass (MR st m) =? sc); lia.
Qed.

#[using="CEILV X L BL LS INV ZB IR IA IM IG IS"] Lemma f_usage : fact_usage (strip st).
Proof.
  intros i. rewrite usage_strip. destruct (c_usage (s_ctx st) !! i) as [v|] eqn:E.
  - pose proof (ia_usage_keys _ IA i v E) as Hi. rewrite (ia_usage _ IA i Hi). apply gcnt_bound.
  - unfold usage, ctx. rewrite E. cbn. lia.
Qed.
End MF.

(* [comment removed for export] *)
(* [comment removed for export] *)
End PORT.
End WithCeil.

Local Ltac inst f INV CR :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Theorem areach_facts_proof : forall {resv} st LB, AREACH_from resv st LB -> @MFACTS_g resv st LB.
Proof.
  intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  constructor.
  - inst LB_blocks_ok INV CR.
  - inst LB_nodup INV CR.
  - inst f_ticks INV CR.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - inst f_ctx INV CR.
  - inst f_active INV CR.
  - inst f_gmeta INV CR.
  - inst f_avail_clear INV CR.
  - inst f_hdr0 INV CR.
  - inst f_free_clear INV CR.
  - inst f_hdr_clear INV CR.
  - inst f_usage INV CR.
  - inst f_masks INV CR.
  - inst f_maplen INV CR.
  - inst f_slots INV CR.
  - inst f_slots_complete INV CR.
  - inst f_ptrs INV CR.
  - inst f_blk_unknown INV CR.
  - inst f_blocks_disjoint INV CR.
  - inst f_cell_ticks INV CR.
Qed.

End PORT.

End WithCeil.
End MallocFacts_inv2.

(* [comment removed for export] *)
Module F_malloc_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.AllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma follow_steq {R} (t1 t2 : Malloc.M R) : steq t1 t2 -> forall ans, follow t1 ans = follow t2 ans.
Proof.
  induction 1 as [r | e k1 k2 Hk IH]; intros ans; [reflexivity|].
  cbn. destruct e; try reflexivity; destruct ans; try reflexivity; apply IH.
Qed.

#[using="Type"] Lemma follow_sbind {R S} (t : Malloc.M R) (f : R -> Malloc.M S) :
  forall ans x y, follow t ans = Some x ->
  (forall ans', follow (f x) ans' = Some y) ->
  follow (sbind t f) ans = Some y.
Proof.
  induction t as [r | e k IH]; intros ans x y H Hf.
  - cbn in H. inversion H; subst. rewrite sbind_ret_l. apply Hf.
  - rewrite sbind_vis. cbn in H |- *. destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; eapply IH; eauto.
Qed.

#[using="Type"] Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 -> forall ans r1 r2, follow t1 ans = Some r1 -> follow t2 ans = Some r2 -> RR r1 r2.
Proof.
  induction 1 as [a b Hab | e k1 k2 Hk IH]; intros ans r1 r2 F1 F2.
  - cbn in F1, F2. inversion F1; inversion F2; subst. exact Hab.
  - cbn in F1, F2. destruct e; try discriminate; destruct ans as [|z ans]; try discriminate; eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mrun_enframe_full o st g b idx n ctr :
  m_mem (get_meta_rec st g) = Some b ->
  let stride := get_stride (get_meta_rec st g) in
  let off := fold_off (if rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) =? 0 then Z.land ctr 255
                       else Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2)
                                    + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
                      ((stride - IB - n) / UNIT) in
  mrun o (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p)))
  = SRet (o, (havoc (snd (enframe_at st g idx n off)) n (fst (enframe_at st g idx n off)), Some (snd (enframe_at st g idx n off)))).
Proof.
  intros Hmem stride off. unfold mrun, enframe_full, enframe_read_off.
  assert (Hp0 : slot_start' (get_meta_rec st g) idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd]. fold stride.
  rewrite (rd8_oracle pans_mem pans_mem_range).
  assert (OFFa : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = 0 -> fold_off (Z.land ctr 255) ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
  assert (OFFb : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) <> 0 ->
     fold_off (Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
              ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
  clearbody off.
  destruct (Z.eqb_spec (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3)) 0) as [E|NE]; cbn [negb].
  - rewrite (OFFa E). rewrite surj_pair_let. reflexivity.
  - rewrite (rd16_oracle pans_mem pans_mem_range). unfold aadd. cbn [fst snd].
    rewrite (OFFb NE). rewrite surj_pair_let. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma strip_eq_proj a b : strip a = strip b ->
  s_ctx a = s_ctx b /\ s_regions a = s_regions b /\ s_next_rid a = s_next_rid b /\ s_metas a = s_metas b
  /\ s_areas a = s_areas b /\ s_groups a = s_groups b /\ s_slots a = s_slots b /\ s_reserved a = s_reserved b.
Proof.
  intros E.
  pose proof (f_equal s_ctx E) as E1. pose proof (f_equal s_regions E) as E2. pose proof (f_equal s_next_rid E) as E3.
  pose proof (f_equal s_metas E) as E4. pose proof (f_equal s_areas E) as E5. pose proof (f_equal s_groups E) as E6.
  pose proof (f_equal s_slots E) as E7. pose proof (f_equal s_reserved E) as E8.
  cbn in E1, E2, E3, E4, E5, E6, E7, E8. repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mrun_fst {R} (t : Malloc.M R) : forall o ans o1 x, follow (mrun o t) ans = Some (o1, x) -> o1 = o.
Proof.
  unfold mrun, prun. induction t as [r | e k IH]; intros o ans o1 x H.
  - cbn in H. inversion H. reflexivity.
  - cbn [eruns] in H. destruct (psel pans_mem o e) as [a|] eqn:P.
    + unfold pupd_mem in H. eapply IH. exact H.
    + cbn in H. destruct e; try discriminate; destruct ans; try discriminate; unfold pupd_mem in H; eapply IH; exact H.
Qed.

#[using="Type"] Lemma mod16_slot (B s st k off : Z) : B mod 4096 = 0 -> s mod 16 = 0 -> st mod 16 = 0 -> 0 <= k ->
  (B + s + 16 + st * k + 16 * off) mod 16 = 0.
Proof.
  intros HB HS HT HK.
  destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
  assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
  set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
Qed.

End PORT.

End WithCeil.
End F_malloc_top.

(* [comment removed for export] *)
Module MallocFacts_inv3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Section CF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
#[using="Type"] Lemma hostsB b g : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.hosts st b g <-> hosts st b g.
Proof. reflexivity. Qed.
#[using="Type"] Lemma is_gmB g : is_gm st g <-> live_group st g.
Proof. reflexivity. Qed.

#[using="CEILV X L BL INV IA"] Lemma listed_meta_slot m h : In m (LS h) -> meta_slot st m.
Proof.
  intros H. pose proof (listed_present _ _ _ _ _ INV m h H) as P. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
  destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). exists a, ar, k. auto.
Qed.

#[using="CEILV X L BL INV IL"] Lemma in_list_of_next m : m_next (MR st m) <> None -> exists h, In m (LS h).
Proof. intros H. exact (proj2 (proj1 (il_link _ _ IL m)) H). Qed.

(* [comment removed for export] *)
#[using="CEILV X L BL LS INV IM IG IS"] Lemma sep_ghdr' m bm i m2 b2 : hosts st bm m -> 0 <= i <= m_last_idx (MR st m) ->
  s_groups st !! (fst bm, sstart (MR st m) i) = None ->
  hosts st b2 m2 -> fst b2 = fst bm ->
  snd b2 + 16 <= sstart (MR st m) i \/ sstart (MR st m) (i + 1) <= snd b2.
Proof.
  intros Hm Hi NH H2 Hf. pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (sst_lt _ _ _ IG _ _ i (i + 1) Hm ltac:(lia)) as L1. unfold UNIT in S0.
  destruct (aptr_eq_dec m2 m) as [->|NEm].
  - left. pose proof (hosts_inj _ _ _ IM _ _ _ Hm H2); subst b2. pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). lia.
  - pose proof (sstart0 _ _ _ IM _ _ H2) as S2. unfold UNIT in S2. pose proof (gend_ge _ _ _ IM IG _ _ H2) as G2.
    destruct (dichotomy _ _ _ _ IM IG IS _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
    + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ _ _ IM IG IS _ _ _ Hm NH _ _ Ha)|].
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha H2) as (A1 & A2 & A3).
      destruct (Z.lt_ge_cases j i).
      * left. pose proof (sstart_mono _ _ _ IG _ _ (j + 1) i Hm ltac:(lia)). lia.
      * right. pose proof (sstart_mono _ _ _ IG _ _ (i + 1) j Hm ltac:(lia)). lia.
    + left. destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
      pose proof (hosts_inj _ _ _ IM _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ IM _ _ _ H2 H2'); subst b2'.
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha Hm) as (A1 & A2 & A3).
      pose proof (sstart_mono _ _ _ IG _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). lia.
    + destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
      pose proof (hosts_inj _ _ _ IM _ _ _ Hm Hm'); subst bm'.
      destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
      pose proof (hosts_inj _ _ _ IM _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hp'); subst bp'.
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite (gend_eq st) in A2.
      pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)).
      destruct (Z.lt_ge_cases j1 j2).
      * right. pose proof (sstart_mono _ _ _ IG _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
      * left. pose proof (sstart_mono _ _ _ IG _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="CEILV X L BL LS INV IA IL"] Lemma c_links : ci_links_t st.
Proof.
  pose proof (old_lists _ _ _ _ _ INV) as LO.
  constructor.
  - intros m nx Hn. fold (MR st m) in Hn. fold (MR st nx). destruct (in_list_of_next m ltac:(rewrite Hn; discriminate)) as [h Hh].
    destruct (lists_next_in st LS LO h m Hh) as (y & Hy & Ey & Py). rewrite Hn in Ey. inversion Ey; subst y.
    split; [exact Py| exact (listed_meta_slot _ _ Hy)].
  - intros m pv Hp. fold (MR st m) in Hp. fold (MR st pv).
    destruct (m_next (MR st m)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL m) Ex) as P; rewrite Hp in P; discriminate].
    destruct (in_list_of_next m ltac:(rewrite Ex; discriminate)) as [h Hh].
    destruct (lists_prev_in st LS LO h m Hh) as (y & Hy & Ey & Ny). rewrite Hp in Ey. inversion Ey; subst y.
    split; [exact Ny| exact (listed_meta_slot _ _ Hy)].
  - intros m. fold (MR st m). split; [exact (proj2 (il_link _ _ IL m))|]. intros Hp.
    destruct (m_next (MR st m)) as [x|] eqn:Ex; [| reflexivity]. exfalso.
    destruct (in_list_of_next m ltac:(rewrite Ex; discriminate)) as [h Hh].
    destruct (lists_prev_in st LS LO h m Hh) as (y & _ & Ey & _). rewrite Hp in Ey. discriminate.
  - intros m Hn. fold (MR st m) in Hn. destruct (in_list_of_next m Hn) as [h Hh]. exact (listed_meta_slot _ _ Hh).
Qed.

#[using="CEILV X L BL LS INV IL"] Lemma c_heads : ci_heads_t st.
Proof.
  constructor.
  - intros h Hh. fold (MR st h). pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
    split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|]. pose proof (il_free _ _ IL h Hin) as E. rewrite E. reflexivity.
  - intros sc a Ha. fold (MR st a). pose proof (head_listed _ _ _ _ _ INV (LActive sc) a Ha) as Hin.
    destruct (il_active _ _ IL sc a Hin) as (Hsc & Hl & Esc). split; [exact Hsc|]. split; [exact (listed_next _ _ _ _ _ INV a _ Hin)|]. split; [exact Hl| exact Esc].
Qed.

#[using="CEILV X L BL LS INV IL"] Lemma c_homog : ci_homog st.
Proof.
  intros m nx Hn. fold (MR st m) in Hn. fold (MR st m) (MR st nx).
  destruct (in_list_of_next m ltac:(rewrite Hn; discriminate)) as [h Hh].
  pose proof (next_listed _ _ _ _ _ INV h m nx Hh Hn) as Hnx.
  destruct h as [sc|].
  - destruct (il_active _ _ IL sc m Hh) as (_ & Lm & Em). destruct (il_active _ _ IL sc nx Hnx) as (_ & Ln & En).
    split; [split; auto|]. intros _. rewrite Em, En. reflexivity.
  - pose proof (free_not_live _ _ _ _ _ INV m Hh) as Nm. pose proof (free_not_live _ _ _ _ _ INV nx Hnx) as Nn.
    split; [split; intros H'; exfalso; [exact (Nm H')| exact (Nn H')]|]. intros H'. exfalso. exact (Nm H').
Qed.

#[using="Type"] Lemma q_div b0 stride i off : stride mod 16 = 0 -> (b0 + 16 + stride * i + 16 * off - b0 - 16) / 16 * 16 = stride * i + 16 * off.
Proof.
  intros Hs. pose proof (Z.div_mod stride 16 ltac:(lia)) as E. rewrite Hs, Z.add_0_r in E.
  set (k := stride / 16) in *. clearbody k. subst stride.
  replace (b0 + 16 + 16 * k * i + 16 * off - b0 - 16) with ((k * i + off) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

#[using="Type"] Lemma mod16_addr a b st_ i off : a mod 4096 = 0 -> b mod 16 = 0 -> st_ mod 16 = 0 -> (a + (b + 16 + st_ * i) + 16 * off) mod 16 = 0.
Proof.
  intros Ha Hb Hs.
  pose proof (Z.div_mod a 4096 ltac:(lia)) as Ea. rewrite Ha, Z.add_0_r in Ea. set (a' := a / 4096) in *. clearbody a'.
  pose proof (Z.div_mod b 16 ltac:(lia)) as Eb. rewrite Hb, Z.add_0_r in Eb. set (b' := b / 16) in *. clearbody b'.
  pose proof (Z.div_mod st_ 16 ltac:(lia)) as Es. rewrite Hs, Z.add_0_r in Es. set (s' := st_ / 16) in *. clearbody s'.
  subst a b st_. replace (4096 * a' + (16 * b' + 16 + 16 * s' * i) + 16 * off) with ((256 * a' + b' + 1 + s' * i + off) * 16) by lia.
  apply Z_mod_mult.
Qed.

#[using="CEILV X L BL LS INV IR IA IM IG IS ISH"] Lemma c_gmeta : ci_gmeta st.
Proof.
  intros b g Hm. destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
  destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r & Hr & Kr & A0 & GE).
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
  constructor; try (fold (MR st g)).
  - pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
    destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). exists a, ar, ka. auto.
  - split; [exact M1|]. apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia.
  - split; [exact M2|]. apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia.
  - exact LI.
  - exact (g_freeable _ _ _ _ _ _ GO).
  - destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia].
  - split; [exact ML|]. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). ceil_facts.
    destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
    destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r' & Hr' & _ & E4 & _). rewrite Hr in Hr'. inversion Hr'; subst r'. lia.
  - intros i Hi. split; intros Ht; [pose proof (M3 i Hi Ht); lia| exact (M4 i Hi Ht)].
  - exact (hosts_mem _ _ _ IM _ _ Hm).
  - exists r. pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|].
    split; [unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.sstart_of; change (sstart (MR st g) (m_last_idx (MR st g) + 1) <= round_up_pg (r_len r)); rewrite <- (gend_eq st); exact GE|].
    intros NZ. destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r' & Hr' & _ & E4 & _). rewrite Hr in Hr'. inversion Hr'; subst r'. auto.
  - split; [exact SG| exact SM].
  - intros MZ. destruct (g_nest _ _ _ _ _ _ GO MZ) as (p & i & Hsl & Hfst & Hend & Hsc & Hstr).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([bp Hp] & Hi & Es).
    exists p, i, bp. split; [exact Hsl|]. split; [exact Hp|].
    rewrite (hosts_gbase _ _ _ IM _ _ Hp) in Hfst. split; [exact Hfst|]. split; [exact Es|]. split; [exact Hi|].
    pose proof Hp as [aip Hp']. pose proof (is_part _ _ _ IS bp p aip i Hp' Hi) as P. rewrite <- Es in P.
    unfold one5, tbit in P. destruct P as (_ & _ & _ & nAD & _ & _ & nBD & _).
    assert (D : s_groups st !! b <> None) by (rewrite Hb; discriminate).
    split. { intros [F|A]; [apply nBD| apply nAD]; split; auto. }
    fold (MR st p). split; [lia|].
    destruct (ish_nest _ _ ISH b g p i Hm MZ Hsl) as ((v3 & K3 & L3 & R3) & K2 & K1 & Q). rewrite (hosts_gbase _ _ _ IM _ _ Hp) in K2, K1, Q.
    exists v3, (byte_of ((snd b - snd bp - UNIT) / UNIT) 0), (byte_of ((snd b - snd bp - UNIT) / UNIT) 1).
    split; [exact K3|]. split; [exact L3|]. split; [exact K2|]. split; [exact K1|].
    rewrite u16_bytes by exact Q. rewrite (slot_start'_eq _ _ _ IM _ _ i Hp) in Es. rewrite Es. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hp).
    pose proof (stride_ge _ _ _ IG _ _ Hp) as [_ SMp]. unfold UNIT in *. pose proof (q_div (snd bp) (get_stride (MR st p)) i 0 SMp). lia.
Qed.

#[using="CEILV X L BL LS INV IM"] Lemma c_groups : ci_groups st.
Proof. intros b gh Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _ & AI). exists m. auto. Qed.

#[using="CEILV X L BL LS INV IM"] Lemma c_group_inj : ci_group_inj st.
Proof. intros b1 b2 g H1 H2. exact (hosts_inj _ _ _ IM _ _ _ H1 H2). Qed.

#[using="CEILV X L BL LS INV IS"] Lemma c_slots : ci_slots st.
Proof. intros s g i Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (A & B & C). split; [exact A|]. split; [exact C| exact B]. Qed.

#[using="CEILV X L BL LS INV IS"] Lemma c_slots_total : ci_slots_total st.
Proof. intros b g i Hb Hi. exact (is_total _ _ _ IS _ _ _ Hb Hi). Qed.

#[using="CEILV X L BL LS INV ISH"] Lemma c_ghdr_unk : ci_ghdr_unk st.
Proof. intros b gh o Hb Ho. destruct (hdr_hosts _ _ _ _ _ INV _ _ Hb) as [m Hm]. exact (ish_ghdr _ _ ISH b m o Hm Ho). Qed.

#[using="CEILV X L BL LS INV ISH"] Lemma c_hdr0 : ci_hdr0 st.
Proof. intros g b i Hm Hi. fold (MR st g) in *. exact (ish_hdr0 _ _ ISH b g i Hm ltac:(unfold cnt_of; lia)). Qed.

#[using="CEILV X L BL LS INV ZB IA"] Lemma c_ctx : ci_ctx st.
Proof.
  pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
  split; [exact C2|]. split.
  { intros i. unfold bounces, ctx. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)). }
  split. { intros i. unfold unmap_seq, ctx. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)). }
  split. { intros sc. pose proof (f_usage _ _ _ _ _ INV ZB sc) as U. rewrite usage_strip in U. lia. }
  unfold ctx. destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia.
Qed.

#[using="CEILV X L BL LS INV IR"] Lemma c_brk : ci_brk st.
Proof.
  intros rid off Hb. pose proof (ir_brk _ _ _ IR) as BR. unfold ctx in Hb. rewrite Hb in BR. destruct BR as (_ & r & Hr & Kr & _). exists r. auto.
Qed.

#[using="CEILV X L BL LS INV ZB"] Lemma c_mem_hosts : ci_mem_hosts st.
Proof. intros q b H. exact (mem_hosts _ _ _ _ _ INV ZB _ _ H). Qed.

#[using="Type"] Lemma metakind_ng r : is_metakind r -> r_kind r <> RKGroup.
Proof. intros [K|K]; rewrite K; discriminate. Qed.

#[using="CEILV X L BL LS INV IA"] Lemma area_ng a : s_areas st !! a <> None -> ng_ptr st (Some a).
Proof.
  intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [| congruence].
  destruct (ia_areas _ IA _ _ E) as ((r & Hr & MK & _) & _). exists r. split; [exact Hr| exact (metakind_ng _ MK)].
Qed.

#[using="CEILV X L BL LS INV IR IA"] Lemma c_mptrs : ci_mptrs st.
Proof.
  unfold ci_mptrs, ctx.
  split. { destruct (c_avail_meta (s_ctx st)) as [q|] eqn:E; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & MK). exists r. split; [exact Hr| exact (metakind_ng _ MK)]. }
  split. { destruct (c_meta_area_head (s_ctx st)) as [q|] eqn:E; [| exact I]. exact (area_ng _ (ia_head _ IA q E)). }
  split. { destruct (c_meta_area_tail (s_ctx st)) as [q|] eqn:E; [| exact I]. exact (area_ng _ (ia_tail _ IA q E)). }
  split. { destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:E; [| exact I].
           destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). destruct (CU rid off E) as (r & Hr & MK & _). exists r. split; [exact Hr| exact (metakind_ng _ MK)]. }
  intros a ar Ha. destruct (a_next ar) as [a'|] eqn:E; [| exact I]. destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_ng _ (NXT a' E)).
Qed.

(* [comment removed for export] *)
Variable LB : list block.
Hypothesis CR : CORR st LB BL.

#[using="CEILV X L BL LS INV IM IG IS ISH CR"] Lemma LB_blk_ok : Forall (blk_ok st) LB.
Proof.
  apply List.Forall_forall. intros blk Hblk.
  destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  destruct (is_blocks _ _ _ IS _ Hk) as (m' & i' & Hs & Hoff & _). cbn [bslot boff fst snd] in Hs, Hoff.
  pose proof (is_total _ _ _ IS _ _ _ Hm Hi) as Hs'. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm), <- Ec, Hs in Hs'. inversion Hs'; subst m' i'.
  constructor.
  - exists m, i, bm. rewrite C1. split; [exact Hs|]. split; [exact Hm|]. split; [rewrite Ec; reflexivity|]. split; [exact Hi|]. fold (MR st m).
    pose proof Hm as [ai Hb]. pose proof (is_part _ _ _ IS bm m ai i Hb Hi) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm), <- Ec in P.
    unfold one5, tbit in P. destruct P as (_ & _ & nAC & _ & _ & nBC & _).
    assert (C : In c (map bslot BL)) by (apply (in_map bslot _ _ Hk)).
    split. { intros [F|A]; [apply nBC| apply nAC]; split; auto. }
    exists off. split; [exact Ho|]. split; [rewrite Ea, Ec; unfold conc, get_region; cbn [fst snd]; rewrite Hr; lia|]. split; [rewrite C2; exact Fit|].
    pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (K4 & K3 & K2 & K1 & Q & _). cbn [bslot boff bsize fst snd] in K4, K3, K2, K1, Q.
    unfold known, SHd in K4, K3, K2, K1. rewrite (hosts_gbase _ _ _ IM _ _ Hm) in K2, K1, Q.
    split; [unfold IB; replace (snd c + UNIT * off - 4) with (snd c + UNIT * off - 4) by lia; exact K4|].
    eexists _, _, _. unfold aadd; cbn [fst snd]. split; [exact K3|].
    split; [apply land31_idx; [destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai' & _ & GO'); pose proof (g_li _ _ _ _ _ _ GO'); lia| lia]|].
    split; [exact K2|]. split; [exact K1|].
    rewrite u16_bytes by exact Q. rewrite Ec. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm).
    pose proof (stride_ge _ _ _ IG _ _ Hm) as [_ SMm]. unfold UNIT in *. pose proof (q_div (snd bm) (get_stride (MR st m)) i off SMm). lia.
  - rewrite C1. exact NH.
  - rewrite C2. exact Hn.
Qed.

#[using="CEILV X L BL LS INV IR IM IG IS CR"] Lemma LB_blk_clear : Forall (blk_clear st LB) LB.
Proof.
  apply List.Forall_forall. intros blk Hblk.
  destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  pose proof (sstart_succ st m i) as SS. pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)) as SM0.
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SMm].
  destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r' & Hr' & _ & A0 & GE). rewrite Hr in Hr'. inversion Hr'; subst r'.
  pose proof (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16].
  constructor.
  - exists r. rewrite C1, Ec. cbn [fst]. split; [exact Hr|]. split; [exact Kr|].
    split; [unfold UNIT in *; lia|].
    split. { rewrite C2. rewrite (gend_eq st) in GE. pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)). unfold UNIT, IB in *. lia. }
    split. { rewrite Ea. destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & PG & _). unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm). unfold UNIT, PGSZ in *.
             exact (mod16_addr _ _ _ _ _ PG A16 SMm). }
    intros a Ha. pose proof (f_blk_unknown _ _ _ _ _ INV _ CR blk r Hblk ltac:(rewrite C1, Ec; exact Hr) a Ha) as U. rewrite C1, Ec in U. exact U.
  - intros b gh Hgh Hf. rewrite C1, Ec in Hf. cbn [fst] in Hf. destruct (hdr_hosts _ _ _ _ _ INV _ _ Hgh) as [m2 Hm2].
    unfold conc, get_region. rewrite Hf, Hr. rewrite Ea, C2.
    destruct (sep_ghdr' m bm i m2 b Hm Hi ltac:(rewrite Ec in NH; exact NH) Hm2 Hf) as [A|A]; unfold UNIT, IB in *; lia.
  - intros blk' Hblk' NE Hf.
    destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk') as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & D1 & D2 & Hm2 & Hi2 & Ec2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
    rewrite C1, D1, Ec, Ec2 in Hf. cbn [fst] in Hf. rewrite Hf, Hr in R2. inversion R2; subst r2.
    rewrite A2, Ea, D2, C2. pose proof (sstart_succ st m2 i2).
    assert (NE' : m2 <> m \/ i2 <> i). { destruct (aptr_eq_dec m2 m) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, D1, Ec, Ec2, Hf. reflexivity. }
    rewrite Ec in NH. rewrite Ec2 in N2.
    destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 bm2 i2 Hm2 Hf Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
End CF.

(* [comment removed for export] *)
(* [comment removed for export] *)
End PORT.
End WithCeil.

Local Ltac inst f INV CR :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Theorem areach_cinv_proof : forall {resv} st LB, AREACH_from resv st LB -> CINV st LB.
Proof.
  intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  constructor.
  - inst c_links INV CR.
  - inst c_heads INV CR.
  - inst c_homog INV CR.
  - inst c_gmeta INV CR.
  - inst c_groups INV CR.
  - inst c_group_inj INV CR.
  - inst c_slots INV CR.
  - inst c_slots_total INV CR.
  - inst c_ghdr_unk INV CR.
  - inst c_hdr0 INV CR.
  - inst LB_blk_ok INV CR.
  - inst LB_nodup INV CR.
  - inst c_ctx INV CR.
  - inst c_brk INV CR.
  - inst f_ticks INV CR.
  - inst c_mem_hosts INV CR.
  - inst c_mptrs INV CR.
  - inst LB_blk_clear INV CR.
Qed.

End PORT.

End WithCeil.
End MallocFacts_inv3.

(* [comment removed for export] *)
Module MallocFacts_inv4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup MI_TF2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WTry2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Fuel.

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocNat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Section GF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="CEILV X L BL INV IM"] Lemma lmem_listed m h : In m (LS h) -> live_group st m -> lmem (strip st) m.
Proof.
  intros Hin [b Hb]. unfold lmem. rewrite !get_meta_rec_strip. fold (MR st m).
  split; [rewrite (hosts_mem _ _ _ IM _ _ Hb); discriminate|].
  split; [exact (listed_next _ _ _ _ _ INV m h Hin)|].
  destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) h m Hin) as (y & _ & E & _). rewrite E. discriminate.
Qed.
(* [comment removed for export] *)
#[using="CEILV X L BL LS INV ZB"] Lemma mem_live g b : m_mem (MR st g) = Some b -> hosts st b g.
Proof. intros H. exact (mem_hosts X st L BL LS INV ZB g b H). Qed.

#[using="CEILV X L BL INV ZB IL"] Lemma linked_group_listed g b : m_mem (MR st g) = Some b -> m_next (MR st g) <> None ->
  In g (LS (LActive (m_sizeclass (MR st g)))).
Proof.
  intros Hb Hn. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
  destruct h as [sc|].
  - destruct (il_active _ _ IL sc g Hh) as (_ & _ & <-). exact Hh.
  - exfalso. apply (free_not_live _ _ _ _ _ INV g Hh). exists b. exact (mem_live _ _ Hb).
Qed.

#[using="CEILV X L BL LS INV ZB IM IL"] Lemma l_lists : fact_lists (strip st).
Proof.
  split; [| split].
  - intros sc g H. rewrite active_strip in H. pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
    destruct (il_active _ _ IL sc g Hin) as (_ & Hl & _). exact (lmem_listed _ _ Hin Hl).
  - intros g n Hm Hn. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st n) in *.
    destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
    pose proof (linked_group_listed _ _ Hb ltac:(rewrite Hn; discriminate)) as Hg.
    pose proof (next_listed _ _ _ _ _ INV _ g n Hg Hn) as Hn'.
    destruct (il_active _ _ IL _ n Hn') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hn' Hl)| exact Esc].
  - intros g p Hm Hp. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st p) in *.
    destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
    destruct (m_next (MR st g)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL g) Ex) as P; rewrite Hp in P; discriminate].
    pose proof (linked_group_listed _ _ Hb ltac:(rewrite Ex; discriminate)) as Hg.
    pose proof (prev_listed _ _ _ _ _ INV _ g p Hg Hp) as Hp'.
    destruct (il_active _ _ IL _ p Hp') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hp' Hl)| exact Esc].
Qed.

#[using="CEILV X L BL LS INV IL"] Lemma l_freelist : fact_freelist (strip st).
Proof.
  intros h Hh. rewrite ctx_strip in Hh. rewrite !get_meta_rec_strip. fold (MR st h).
  pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
  assert (MS : forall m, In m (LS LFree) -> meta_slot (strip st) m).
  { intros m Hm. destruct (listed_meta_slot X st L BL LS INV m LFree Hm) as (a & ar & k & Ha & Hk & E). exists a, ar, k. auto. }
  split; [exact (MS h Hin)|].
  pose proof (il_free _ _ IL h Hin) as E. split; [rewrite E; reflexivity|].
  split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|].
  destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) LFree h Hin) as (p & Hp & Ep & Np).
  exists p. split; [exact Ep|]. split; [exact (MS p Hp)|]. rewrite !get_meta_rec_strip. fold (MR st p).
  pose proof (il_free _ _ IL p Hp) as Ep'. split; [rewrite Ep'; reflexivity|]. rewrite Np. discriminate.
Qed.
#[using="CEILV X L BL LS INV ZB IR IM IG"] Lemma l_mw : fact_mw (strip st).
Proof.
  intros g. rewrite !get_meta_rec_strip. fold (MR st g).
  destruct (m_mem (MR st g)) as [b|] eqn:Hb.
  - destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
    pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
    pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
    assert (AV : m_avail (MR st g) < 2 ^ 32).
    { apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
    assert (FR : m_freed (MR st g) < 2 ^ 32).
    { apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
    assert (MLB : m_maplen (MR st g) < 2 ^ 52).
    { destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
      destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r & Hr & _ & E & _).
      destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & LT & _). pose proof (round_up_pg_spec (r_len r)). unfold LEN_MAX in LT. lia. }
    split; [| lia]. unfold mw_ok. split; [exact LI|]. split; [rewrite (g_freeable _ _ _ _ _ _ GO); lia|].
    split; [| lia]. destruct (g_sc _ _ _ _ _ _ GO) as [[S1 _]|(S1 & _)]; lia.
  - rewrite (im_zero _ _ _ IM g Hb). cbn. unfold mw_ok. cbn. lia.
Qed.

#[using="CEILV X L BL LS INV ZB IG"] Lemma l_host_stride : fact_host_stride (strip st).
Proof.
  intros g b Hb Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
  destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
  unfold get_stride in *. destruct (m_last_idx (MR st g) =? 0) eqn:E0; [| reflexivity].
  destruct (m_maplen (MR st g) =? 0) eqn:EM; cbn [andb negb] in *; [reflexivity|].
  apply Z.eqb_eq in E0. apply Z.eqb_neq in EM. destruct (S2 E0) as [_ S27].
  assert (Esc : m_sizeclass (MR st g) = 27) by lia. rewrite Esc in *. change (size_class 27) with 255 in *.
  destruct S1 as [S1|S1]; [| lia].
  pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT in *. lia.
Qed.

#[using="CEILV X L BL LS INV"] Lemma l_links : fact_links (strip st).
Proof.
  intros g Hg. unfold lmem in Hg. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. destruct Hg as (Hm & Hn & Hp).
  destruct (c_links X st L BL LS INV) as [CN CP _ _].
  split.
  - intros n E. rewrite get_meta_rec_strip. exact (proj1 (CN g n E)).
  - intros p E. rewrite get_meta_rec_strip. exact (proj1 (CP g p E)).
Qed.

#[using="CEILV X L BL LS INV ZB IG"] Lemma l_sc0_full : fact_sc0_full (strip st).
Proof.
  intros g b gh Hb Hgh Hsc. rewrite s_groups_strip in Hgh. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_live _ _ Hb) as Hh. destruct (hosts_ok _ _ _ IG _ _ Hh) as (ai & Hg & GO).
  rewrite Hg in Hgh. inversion Hgh; subst gh. cbn. exact (g_full0 _ _ _ _ _ _ GO Hsc).
Qed.

#[using="CEILV X L BL LS INV ZB NFR IG"] Lemma l_bit_stride : fact_bit_stride (strip st).
Proof.
  intros g b i Hb Hi Hbits Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
  destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| exact GE].
  exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 F0].
  rewrite A0, F0, !Z.bits_0 in Hbits. discriminate Hbits.
Qed.

#[using="CEILV X L BL LS INV ZB NFR IR IM IL IG"] Lemma inv_lfacts : LFACTS (strip st).
Proof. constructor; [exact l_lists| exact l_freelist| exact l_mw| exact l_host_stride| exact l_links| exact l_sc0_full| exact l_bit_stride]. Qed.

#[using="CEILV X L BL LS INV ISH"] Lemma inv_ghdr_unk : fact_ghdr_unk st.
Proof.
  intros b gh o Hb Ho. destruct (hdr_hosts X st L BL LS INV b gh Hb) as [m Hm].
  exact (ish_ghdr _ _ ISH b m o Hm ltac:(lia)).
Qed.

(* [comment removed for export] *)
Variable resv : list (Z * Z).
Variable LB : list block.
Hypothesis CR : CORR st LB BL.
Hypothesis RESV : ld_resv L = resv.

Local Ltac inst f :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV ZB) | exact (f _ _ _ _ _ INV ZB NFR)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV ZB _ CR) | exact (f _ _ _ _ _ INV ZB NFR _ CR) ].

#[using="CEILV X L BL LS INV ZB NFR IR CR RESV"] Lemma inv_mfacts : @MFACTS_g resv st LB.
Proof.
  constructor.
  - inst LB_blocks_ok.
  - inst LB_nodup.
  - inst f_ticks.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - inst f_ctx.
  - inst f_active.
  - inst f_gmeta.
  - inst f_avail_clear.
  - inst f_hdr0.
  - inst f_free_clear.
  - inst f_hdr_clear.
  - inst f_usage.
  - inst f_masks.
  - inst f_maplen.
  - inst f_slots.
  - inst f_slots_complete.
  - inst f_ptrs.
  - inst f_blk_unknown.
  - inst f_blocks_disjoint.
  - inst f_cell_ticks.
Qed.

#[using="CEILV X L BL LS INV ZB NFR IR IM IL IG ISH CR RESV"] Lemma inv_istf : @ISTF_g resv st LB.
Proof. constructor; [exact inv_mfacts| exact inv_lfacts| exact inv_ghdr_unk]. Qed.

(* [comment removed for export] *)
#[using="CEILV X L BL LS INV IA"] Lemma frontier_fresh rid r o : s_regions st !! rid = Some r -> frontier st rid r <= o -> fresh_above st rid o.
Proof.
  intros Hr Ho q Hq Hoq. split.
  - exact (proj1 (above_frontier X st L BL LS rid r q INV Hr Hq ltac:(lia))).
  - destruct (s_metas st !! q) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & Em).
    pose proof (proj2 (above_frontier X st L BL LS rid r a INV Hr ltac:(rewrite Em in Hq; exact Hq)
                  ltac:(rewrite Em in Hoq; unfold mslot, aadd in Hoq; cbn in Hoq; unfold AREA_HDR, META_SIZE, NSLOTS in *;
                        destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _);
                        rewrite Em in Hq; unfold mslot, aadd in Hq; cbn in Hq; rewrite Hq, Hr in Hr'; inversion Hr'; subst r'; rewrite Hq in F; unfold PGSZ in F; lia)) k Hk) as N.
    rewrite <- Em, E in N. discriminate N.
Qed.

Hypothesis SEC : s_secret st = msecret.

#[using="CEILV X L BL LS INV ZB IR IA IM IL RESV SEC"] Lemma inv_ampre : AMpre_g (resv:=resv) st.
Proof.
  pose proof (ia_secret _ IA) as [S0 SD]. pose proof (ia_avail _ IA) as [AC AV]. pose proof (ir_cursor _ _ _ IR) as (C1 & C2 & C3).
  assert (RB : forall rid r, s_regions st !! rid = Some r -> 0 < r_len r < 2 ^ 47).
  { intros rid r Hr. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & L0 & _ & CE & _). pose proof (round_up_ge (r_len r)). ceil_facts. lia. }
  constructor.
  - (* [comment removed for export] *) unfold ctx. destruct SD as [(_ & E & _)|[_ E]]; rewrite E; lia.
  - unfold ctx. destruct SD as [(E & _)|[E _]]; rewrite E; auto.
  - exact SEC.
  - unfold ctx. exact AC.
  - unfold ctx. split; [exact C1|]. destruct (Z.eq_dec (c_avail_meta_area_count (s_ctx st)) 0) as [E|NE]; [rewrite E; lia|].
    destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
    destruct (C3 rid off eq_refl) as (r & Hr & _ & P1 & _ & E & _). pose proof (RB _ _ Hr). unfold PGSZ in *. nia.
  - unfold ctx. destruct (ir_shift _ _ _ IR) as [SH0 [E|(rid & r & Hr & _ & E)]]; [lia|].
    pose proof (RB _ _ Hr) as [_ LT]. rewrite E in LT. unfold PGSZ in LT. change 4096 with (2 ^ 12) in LT.
    split; [exact SH0|]. destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 38) as [|GT]; [assumption|]. exfalso.
    assert (2 ^ 39 <= 2 ^ c_meta_alloc_shift (s_ctx st)) by (apply Z.pow_le_mono_r; lia). nia.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - exact (c_links X st L BL LS INV).
  - intros h Hh. exact (ch_free _ (c_heads X st L BL LS INV) h Hh).
  - intros g Hm Hn. fold (MR st g) in *. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
    destruct h as [sc|].
    { exfalso. destruct (il_active _ _ IL sc g Hh) as (_ & [b Hb] & _). rewrite (hosts_mem _ _ _ IM _ _ Hb) in Hm. discriminate Hm. }
    pose proof (il_free _ _ IL g Hh) as E. split; [rewrite E; reflexivity|]. split.
    + intros nx Hnx. fold (MR st nx). pose proof (il_free _ _ IL nx (next_listed _ _ _ _ _ INV LFree g nx Hh Hnx)) as E'. rewrite E'. reflexivity.
    + intros pv Hpv. fold (MR st pv). pose proof (il_free _ _ IL pv (prev_listed _ _ _ _ _ INV LFree g pv Hh Hpv)) as E'. rewrite E'. reflexivity.
  - intros q mr Hq. destruct (ia_metas _ IA _ _ Hq) as (a & ar & k & Ha & Hk & Em). exists a, ar, k. auto.
  - unfold ctx. intros NE. destruct (AV ltac:(lia)) as (a & Ht & Hav & FR).
    pose proof (ia_tail _ IA a Ht) as Ha. destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
    exists a, ar, (NSLOTS - c_avail_meta_count (s_ctx st)). split; [exact Ea|]. split; [exact Hav|]. split; [lia|]. split; [lia|].
    apply FR. lia.
  - unfold ctx. intros tl Ht. pose proof (ia_tail _ IA tl Ht) as Ha. destruct (s_areas st !! tl) as [ar|]; [eexists; reflexivity| congruence].
  - unfold ctx. intros NE. destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
    destruct (C3 rid off eq_refl) as (r & Hr & MK & P1 & P2 & E & _).
    exists (rid, off), r. cbn [fst snd]. split; [reflexivity|]. split; [exact Hr|].
    split; [destruct MK as [K|K]; rewrite K; discriminate|]. split; [exact P2|]. split; [unfold PGSZ in P1; lia|].
    split; [unfold lr_lo; destruct (r_kind r); unfold PGSZ in P1; lia|].
    split; [pose proof (round_up_ge (r_len r)); lia|].
    apply (frontier_fresh rid r off Hr). unfold frontier. rewrite EC, N.eqb_refl. lia.
  - intros q rq Hq. destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & L0 & _). exact L0.
  - pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (Malloc.c_brk (s_ctx st)) as [| |rid off]; [exact I| exact I|].
    destruct BR as [_ (r & Hr & K & Elen)]. exists r. split; [exact Hr|]. split; [exact K|]. split; [exact Elen|].
    destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & _ & _ & MK). destruct (MK ltac:(left; exact K)) as [M1 M2].
    split; [rewrite <- Elen; exact M1|]. split; [rewrite <- Elen; unfold PGSZ in *; lia|].
    split; [apply (frontier_fresh rid r off Hr); rewrite (ir_brkfront _ _ _ IR _ _ Hr K); lia|].
    intros q rq Hq Kq. exact (ir_brk1 _ _ _ IR _ _ _ _ Hq Hr Kq K).
  - exact (f_ptrs X st L BL LS INV ZB).
Qed.
End GF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma CORR_GP X st st' L BL LS LB : INVL X st L BL LS -> GP st st' -> CORR st LB BL -> CORR st' LB BL.
Proof.
  intros INV [GPR _] CR. eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3 & C4).
  split; [exact C1|]. split; [exact C2|]. split; [| exact C4]. rewrite C3. rewrite (conc_same st st' (bslot k)); [reflexivity|].
  destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

(* [comment removed for export] *)
Definition JINVi (resv : list (Z * Z)) (idle : list aptr) (st : mstate) (LB : list block) : Prop :=
  exists L LS BL, INVL (X_as idle) st L BL LS /\ NoDup idle /\ TF0 st /\ ld_resv L = resv /\ s_secret st = msecret /\ CORR st LB BL.
Definition JINV (resv : list (Z * Z)) (st : mstate) (LB : list block) : Prop := exists idle, JINVi resv idle st LB.

#[using="Type"] Lemma jinv_top resv st0 LB t : AREACH_from resv st0 LB -> (s_tick st0 < t)%N -> JINV resv (set_tick t st0) LB.
Proof.
  intros AR Ht. destruct (areach_inv resv st0 LB AR) as (L & LS & BL & INV & _ & RESV & SEC & CR).
  exists [], L, LS, BL. split; [apply INVL_set_tick; [lia| exact INV]|].
  split; [apply NoDup_nil; exact I|| constructor|]. split; [apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| exact Ht]|].
  split; [exact RESV|]. split; [exact SEC|]. exact CR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma jinv_ta resv idle st LB sc st1 :
  JINVi resv idle st LB -> 0 <= sc < 48 -> ta_fail sc st st1 -> JINVi resv idle st1 LB /\ active st1 sc = None.
Proof.
  intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc TA.
  destruct (try_avail_ok (option (mstate * Z)) (X_as idle) L BL sc kS bS eq_refl eq_refl Hsc st LS INV) as (st1' & first & LS1 & E & TAF & RES).
  unfold ta_fail in TA. rewrite E in TA. unfold kS in TA. inversion TA. subst st1' first.
  destruct RES as [(_ & HA & INV1)|(g & bg & ai & idx & NZ & _)]; [| exfalso; exact (NZ eq_refl)].
  split; [| exact HA]. exists L, LS1, BL. split; [exact INV1|]. split; [exact ND|].
  split; [exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF)|]. split; [exact RESV|].
  split; [rewrite (taf_ssec _ _ _ TAF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_taf _ _ _ TAF) CR).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma jinv_am resv idle st1 LB o st2 m :
  JINVi resv idle st1 LB -> leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) -> JINVi resv (m :: idle) st2 LB.
Proof.
  intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) (l0 & ans & o' & FL).
  set (Post := fun (L' : mled) (r : option (mstate * optr)) =>
     match r with
     | Some (s2, Some m') => exists LS', INVL (X_as (m' :: idle)) s2 L' BL LS' /\ ~ In m' idle /\ AM_frame st1 s2 /\ L_frame L L'
     | _ => True
     end).
  assert (FT : ftree L (alloc_meta st1 kS bS) Post).
  { apply (alloc_meta_ft _ BL Post kS bS (X_as idle) st1 L) with (LS := LS); [| | exact INV| apply amf_refl| apply lf_refl].
    - intros s1 L1 LS1 _ _ _. exact I.
    - intros s1 L1 LS1 m' INV1 NI AF LF. cbn. exists LS1. split; [exact INV1|]. split; [exact NI|]. split; [exact AF| exact LF]. }
  pose proof (ftree_prun pans_l pupd_l pans_l_range (alloc_meta st1 kS bS) L Post l0 FT) as PT.
  unfold lrun in FL. destruct (ptree_follow _ L _ ans PT FL) as (L' & CP & POST). cbn in POST.
  destruct POST as (LS' & INV2 & NI & AF & LF).
  exists L', LS', BL. split; [exact INV2|].
  split; [apply NoDup_cons; split; [intros Hin; apply NI; apply list_elem_of_In; exact Hin| exact ND]|].
  split; [exact (TF0_ctrl st1 st2 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF)|].
  split; [rewrite (lf_resv _ _ LF); exact RESV|].
  split; [rewrite (amf_ssec _ _ AF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_amf _ _ AF) CR).
Qed.

#[using="Type"] Lemma ist_jinv resv st0 LB st : AREACH_from resv st0 LB -> IST st0 st -> JINV resv st LB.
Proof.
  intros AR. induction 1 as [t Ht|o st sc st1 st2 m _ IH Hsc TA AM].
  - exact (jinv_top resv st0 LB t AR Ht).
  - destruct IH as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. exists (m :: idle). exact (jinv_am _ _ _ _ _ _ _ J1 AM).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma jinv_slot resv idle st LB o f sc req st3 idx :
  JINVi resv idle st LB -> 0 <= sc < 48 -> req_ok sc req ->
  leaf_of o (alloc_slot full_lay f st sc req kS bS) (Some (st3, idx)) ->
  exists L LS BL L3 LS3, INVL (X_as idle) st L BL LS /\ SLOT_POST idle sc req st L BL st3 idx L3 LS3
    /\ ld_resv L3 = resv /\ s_secret st3 = msecret /\ CORR st3 LB BL.
Proof.
  intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc [Hreq Hfit] (l0 & ans & o' & FL).
  unfold lrun in FL. apply (@alloc_slot_follow_mono _ _ pans_l pupd_l full_lay f (f + 49)) in FL; [| lia].
  set (Post := fun (L' : mled) (r : option (mstate * Z)) =>
     match r with Some (s3, i) => exists LS3, SLOT_POST idle sc req st L BL s3 i L' LS3 | None => True end).
  assert (FT : ftree L (alloc_slot full_lay (f + 49) st sc req kS bS) Post).
  { apply (alloc_slot_ft _ Post (f + 49)%nat sc idle st L BL LS req kS bS ltac:(lia) INV TF ND Hsc Hreq Hfit).
    intros st1 i L1 LS1 SP. cbn. exists LS1. exact SP. }
  pose proof (ftree_prun pans_l pupd_l pans_l_range _ L Post l0 FT) as PT.
  destruct (ptree_follow _ L _ ans PT FL) as (L3 & CP & POST). cbn in POST. destruct POST as [LS3 SP].
  exists L, LS, BL, L3, LS3. split; [exact INV|]. split; [exact SP|].
  split; [rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
  destruct SP as (_ & _ & GP3 & _). split; [rewrite (proj2 GP3); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV GP3 CR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem ist_facts_proof : forall {resv} st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB.
Proof.
  intros resv st0 LB st AR H. destruct (ist_jinv resv st0 LB st AR H) as (idle & L & LS & BL & INV & ND & TF & RESV & SEC & CR).
  exact (inv_istf (X_as idle) st L BL LS INV eq_refl eq_refl resv LB CR RESV).
Qed.

#[using="Type"] Theorem istr_facts_proof : forall {resv} st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB.
Proof.
  intros resv st0 LB st3 AR (o & st & f & sc & req & idx & H & Hsc & RQ & LF).
  destruct (ist_jinv resv st0 LB st AR H) as [idle J].
  destruct (jinv_slot resv idle st LB o f sc req st3 idx J Hsc RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & RESV & SEC & CR).
  destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
  - exact (inv_istf (X_as idle) st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
  - exact (inv_istf _ st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
Qed.

#[using="Type"] Theorem nest_facts_proof : forall {resv} st0 LB st sc st1 o st2 m f j req o' st3 idx,
  AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
  leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
  0 <= j < 48 -> req_ok j req ->
  leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
  nest_ok m st3.
Proof.
  intros resv st0 LB st sc st1 o st2 m f j req o' st3 idx AR H Hsc TA AM Hj RQ LF.
  destruct (ist_jinv resv st0 LB st AR H) as [idle J].
  destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. pose proof (jinv_am _ _ _ _ _ _ _ J1 AM) as J2.
  destruct (jinv_slot resv (m :: idle) st2 LB o' f j req st3 idx J2 Hj RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & _).
  assert (K : forall X3, INVL X3 st3 L3 BL LS3 -> x_idle X3 = m :: idle -> nest_ok m st3).
  { intros X3 INV3 XI. destruct (im_idle _ _ _ (proj1 (proj2 (proj2 INV3))) m ltac:(rewrite XI; left; reflexivity)) as [Em NI].
    split; [unfold get_meta_rec; rewrite Em; reflexivity|].
    intros h Hh. pose proof (head_listed _ _ _ _ _ INV3 LFree h Hh) as Hin. split.
    - intros ->. apply NI. exists LFree. exact Hin.
    - intros Hp. apply NI. exists LFree. exact (prev_listed _ _ _ _ _ INV3 LFree h m Hin Hp). }
  destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
  - exact (K _ INV3 eq_refl).
  - exact (K _ INV3 eq_refl).
Qed.

#[using="Type"] Theorem areach_ampre_proof : forall {resv} st LB, AREACH_from resv st LB -> AMpre_g (resv:=resv) st.
Proof.
  intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & RESV & SEC & _).
  exact (inv_ampre x0 st L BL LS INV eq_refl resv RESV SEC).
Qed.

#[using="Type"] Theorem ist_ampre_proof : forall {resv}, AMP_AS_g resv (am_pre_g resv).
Proof.
  intros resv st0 LB st sc st1 AR H Hsc TA.
  destruct (ist_jinv resv st0 LB st AR H) as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [(L & LS & BL & INV & _ & _ & RESV & SEC & _) _].
  exact (inv_ampre (X_as idle) st1 L BL LS INV eq_refl resv RESV SEC).
Qed.


(* [comment removed for export] *)
Local Definition g1 := (@ist_facts_proof : forall resv st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB).
Local Definition g2 := (@istr_facts_proof : forall resv st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB).
Local Definition g3 := (@nest_facts_proof : forall resv st0 LB st sc st1 o st2 m f j req o' st3 idx,
  AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
  leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
  0 <= j < 48 -> req_ok j req ->
  leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
  nest_ok m st3).
Local Definition g4 := (@areach_ampre_proof : forall resv st LB, AREACH_from resv st LB -> AMpre_g (resv:=resv) st).
Local Definition g5 := (@ist_ampre_proof : forall resv, AMP_AS_g resv (am_pre_g resv)).

End PORT.

End WithCeil.
End MallocFacts_inv4.

(* [comment removed for export] *)
Module MallocFacts_invR.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma areach_blk_slot_clear {resv} st LB blk :
  AREACH_from resv st LB -> In blk LB ->
  exists m bm i r off,
    hosts st bm m /\ 0 <= i <= m_last_idx (MR st m) /\ blk_slot blk = (fst bm, sstart (MR st m) i)
    /\ s_slots st !! (blk_slot blk) = Some (m, i)
    /\ s_regions st !! (fst bm) = Some r /\ r_kind r = RKGroup
    /\ blk_addr blk = r_base r + sstart (MR st m) i + UNIT * off /\ 0 <= off /\ 0 <= blk_size blk
    /\ UNIT * off + blk_size blk <= get_stride (MR st m) - IB
    /\ (forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bm ->
          snd b' + 16 <= sstart (MR st m) i \/ sstart (MR st m) i + get_stride (MR st m) <= snd b' + 4)
    /\ (forall blk', In blk' LB -> blk_slot blk' <> blk_slot blk -> fst (blk_slot blk') = fst bm ->
          blk_addr blk' + blk_size blk' <= r_base r + sstart (MR st m) i - IB
          \/ r_base r + sstart (MR st m) i + get_stride (MR st m) - IB <= blk_addr blk' - IB).
Proof.
  intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hb.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (LB_geo x0 st L BL LS INV LB CR blk Hb) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  exists m, bm, i, r, off. rewrite Ec in NH.
  split; [exact Hm|]. split; [exact Hi|]. split; [rewrite C1; exact Ec|].
  split. { rewrite C1, Ec. pose proof (is_total _ _ _ IS bm m i Hm Hi) as T. rewrite slot_start'_sstart, (hosts_gbase _ _ _ IM _ _ Hm) in T. exact T. }
  split; [exact Hr|]. split; [exact Kr|].
  split; [exact Ea|]. split; [exact Ho|]. split; [rewrite C2; exact Hn|]. split; [rewrite C2; exact Fit|]. split.
  - intros b' gh Hb' Hf. destruct (hdr_hosts x0 st L BL LS INV _ _ Hb') as [m' Hm'].
    destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m' b' Hm' Hf) as [A|A]; [left; exact A| right].
    rewrite sstart_succ in A. exact A.
  - intros blk' Hb2 NE Hf.
    destruct (LB_geo x0 st L BL LS INV LB CR blk' Hb2) as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & D1 & D2 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
    rewrite D1, Ec2 in Hf. cbn [fst] in Hf. rewrite Hf, Hr in Hr2. inversion Hr2; subst r2.
    assert (NE' : m2 <> m \/ i2 <> i).
    { destruct (aptr_eq_dec m2 m) as [->|]; [right| now left]. intros ->. apply NE. rewrite D1, C1, Ec2, Ec, Hf. reflexivity. }
    rewrite Ec2 in NH2. rewrite Ea2, D2.
    pose proof (sstart_succ st m i) as SS. pose proof (sstart_succ st m2 i2) as SS2.
    destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 bm2 i2 Hm2 Hf Hi2 NE' NH2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma areach_blk_frame {resv} st LB blk off m i :
  AREACH_from resv st LB -> In blk LB ->
  blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  s_slots st !! (blk_slot blk) = Some (m, i) ->
  let p := snd (blk_slot blk) + UNIT * off in
  let e := snd (blk_slot blk) + get_stride (MR st m) - IB in
  let res := e - p - blk_size blk in
  cell_read (get_shadow st (fst (blk_slot blk))) (p - 3) = Known (i + 32 * Z.min res 5)
  /\ (5 <= res -> cell_read (get_shadow st (fst (blk_slot blk))) (e - 4) = Known (byte_of res 0)
               /\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 3) = Known (byte_of res 1)
               /\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 2) = Known (byte_of res 2)
               /\ cell_read (get_shadow st (fst (blk_slot blk))) (e - 1) = Known (byte_of res 3)
               /\ res < 2^32).
Proof.
  intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hb HA SL.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (LB_blk st BL LB CR blk Hb) as (c & offk & n & Hk & C1 & C2 & C3).
  assert (offk = off) as -> by (rewrite HA, C1 in C3; unfold UNIT in C3; lia).
  pose proof (ish_blk st BL ISH ((c, off), n) m i Hk ltac:(cbn [bslot fst snd]; rewrite <- C1; exact SL)) as F.
  cbn [bslot boff bsize fst snd] in F. cbv zeta in F. unfold known, SHd in F. cbn [fst snd] in F.
  destruct F as (_ & K3 & _ & _ & _ & K5 & _ & _).
  cbv zeta. rewrite C1, C2. split; [exact K3|].
  intros R5. destruct (K5 R5) as (B0 & B1 & B2 & B3 & _ & R32). repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma areach_blk_addr {resv} st LB blk :
  AREACH_from resv st LB -> In blk LB -> blk_addr blk = conc st (blk_slot blk) + UNIT * snd (blk_id blk).
Proof.
  intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hb.
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3 & C4)). rewrite C3, C1, C4. reflexivity.
Qed.

End PORT.

End WithCeil.
End MallocFacts_invR.
