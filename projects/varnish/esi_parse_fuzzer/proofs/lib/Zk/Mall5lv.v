(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg MProg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Geom MI_Ext MI_Ws22 MI_WNtf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRep MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_slot (b : block) : cptr := fst (fst (fst b)).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.

(* [comment removed for export] *)
Definition brk_link (st : mstate) (pbrk : Z) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => pbrk = conc st (rid, off)
  | _ => True
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition corr1 (st : mstate) (b : block) (k : blk) : Prop :=
  blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k.
Definition CORR (st : mstate) (LB : list block) (BL : list blk) : Prop := Forall2 (corr1 st) LB BL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof.
  intros INV Hk. (first [ pose proof (INV) as dR_1; dand7 dR_1 as IR IA IM IL IG IS ISH | pose proof INV as (IR & IA & IM & IL & IG & IS & ISH) ]).
  (first [ pose proof ((is_blocks _ _ _ IS k Hk)) as dR_2; dex2 dR_2 as m i; destruct dR_2 as [Hs _] | pose proof ((is_blocks _ _ _ IS k Hk)) as dR_2; dand4 dR_2 as m i Hs _ | destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _) ]).
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_3; dand3 dR_3 as [b Hb] _ Es | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es) ]).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

Lemma conc_aadd st p d : (exists r, s_regions st !! fst p = Some r) -> conc st (aadd p d) = conc st p + d.
Proof. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.

Lemma conc_same st st' p : (exists r, s_regions st !! fst p = Some r /\ s_regions st' !! fst p = Some r) -> conc st' p = conc st p.
Proof. ((first [ intro dR_15; dex1 dR_15 as r; destruct dR_15 as [H1 H2] | intro dR_15; dand3 dR_15 as r H1 H2 | intros (r & H1 & H2) ])). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.

Lemma event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
Lemma cpath_resv {R} L (t : M R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_resv. Qed.

Lemma Forall2_In_l {A B} (P : A -> B -> Prop) l1 l2 a : Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists y; split; [left; reflexivity| exact Hxy]|].
  (first [ pose proof ((IH Hin)) as dR_4; dex1 dR_4 as b; destruct dR_4 as [Hb Pb] | pose proof ((IH Hin)) as dR_4; dand3 dR_4 as b Hb Pb | destruct (IH Hin) as (b & Hb & Pb) ]). exists b. split; [right; exact Hb| exact Pb].
Qed.

Lemma Forall2_impl_in {A B} (P Q : A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros HPQ; constructor.
  - apply HPQ; [left; reflexivity| left; reflexivity| exact Hxy].
  - apply IH. intros a b Ha Hb. apply HPQ; right; assumption.
Qed.

Lemma Forall2_filter {A B} (P : A -> B -> Prop) (p : A -> bool) (q : B -> bool) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> p a = q b) -> Forall2 P (filter p l1) (filter q l2).
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros E; cbn; [constructor|].
  rewrite (E _ _ Hxy). destruct (q y); [constructor; [exact Hxy| apply IH; exact E]| apply IH; exact E].
Qed.

Lemma Forall2_map_eq {A B C} (P : A -> B -> Prop) (f : A -> C) (g : B -> C) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> f a = g b) -> map f l1 = map g l2.
Proof. induction 1; intros E; cbn; [reflexivity|]. rewrite (E _ _ H). f_equal. apply IHForall2. exact E. Qed.

Lemma filter_id {A} (p : A -> bool) l : (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma bl_remove_filter c BL : NoDup (map bslot BL) ->
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

Definition AREACH_from (resv : list (Z * Z)) (st : mstate) (LB : list block) : Prop :=
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = run_secret /\ CORR st LB BL.   (* [comment removed for export] *)

Lemma areach_init {resv} : AREACH_from resv (minit run_secret resv) [].
Proof.
  exists (led_init resv), (fun _ => []), []. split; [apply INVL_init; pose proof run_secret_range; lia|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. constructor.
Qed.

Lemma areach_malloc_some {resv} : forall st LB n (o o' : mem) ans st' (pf : aptr) cst (c : cptr),
    AREACH_from resv st LB -> 0 <= n ->
    follow (mrun o (malloc st n)) ans = Some (o', (st', Some pf)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    AREACH_from resv st' (((c, fresh_off cst c n), conc st' pf, n) :: LB).
Proof.
  (intros st LB n o o' ans st' pf cst c; (first [ intro dR_16; dand8 dR_16 as L LS BL INV LIVE RESV SEC CR | intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]); intros Hn FF FC).
  (first [ pose proof ((malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF)) as dR_5; dex1 dR_5 as rc; dand5 dR_5 as FT CP LIVE' [GPR GPS] RES | pose proof ((malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF)) as dR_5; dand6 dR_5 as rc FT CP LIVE' [GPR GPS] RES | destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES) ]).
  unfold mrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc.
  (first [ dex1 RES as off; dand5 RES as LS' Epf Hoff INV' NI | dand6 RES as off LS' Epf Hoff INV' NI | destruct RES as (off & LS' & Epf & Hoff & INV' & NI) ]).
  set (L' := lafter L (cmalloc (strip st) n) ans) in *.
  exists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
  split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
  split; [rewrite GPS; exact SEC|].
  constructor.
  + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd]. rewrite Epf. apply conc_aadd.
    (first [ pose proof ((blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity))) as dR_7; dex1 dR_7 as r; destruct dR_7 as [Hr _] | pose proof ((blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity))) as dR_7; dand3 dR_7 as r Hr _ | destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _) ]). exists r. exact Hr.
  + eapply Forall2_impl_in; [exact CR|]. (intros b k Hb Hk; (first [ intro dR_17; dand3 dR_17 as C1 C2 C3 | intros (C1 & C2 & C3) ])). split; [exact C1|]. split; [exact C2|]. rewrite C3.
    rewrite (conc_same st st' (bslot k)); [reflexivity|].
    (first [ pose proof ((blk_region _ _ _ _ _ k INV Hk)) as dR_8; dex1 dR_8 as r; destruct dR_8 as [Hr Kr] | pose proof ((blk_region _ _ _ _ _ k INV Hk)) as dR_8; dand3 dR_8 as r Hr Kr | destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr) ]). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

Lemma areach_malloc_none {resv} : forall st LB n (o o' : mem) ans st',
    AREACH_from resv st LB -> 0 <= n ->
    follow (mrun o (malloc st n)) ans = Some (o', (st', None)) ->
    AREACH_from resv st' LB.
Proof.
  (intros st LB n o o' ans st'; (first [ intro dR_18; dand8 dR_18 as L LS BL INV LIVE RESV SEC CR | intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]); intros Hn FF).
  (first [ pose proof ((malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF)) as dR_9; dex1 dR_9 as rc; dand5 dR_9 as FT CP LIVE' [GPR GPS] RES | pose proof ((malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF)) as dR_9; dand6 dR_9 as rc FT CP LIVE' [GPR GPS] RES | destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES) ]).
  destruct rc as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
  set (L' := lafter L (cmalloc (strip st) n) ans) in *.
  exists (set_live (map bslot BL) L'), LS', BL.
  split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
  split; [rewrite GPS; exact SEC|].
  eapply Forall2_impl_in; [exact CR|]. (intros bb k Hb Hk; (first [ intro dR_19; dand3 dR_19 as C1 C2 C3 | intros (C1 & C2 & C3) ])). split; [exact C1|]. split; [exact C2|]. rewrite C3.
  rewrite (conc_same st st' (bslot k)); [reflexivity|].
  (first [ pose proof ((blk_region _ _ _ _ _ k INV Hk)) as dR_10; dex1 dR_10 as r; destruct dR_10 as [Hr Kr] | pose proof ((blk_region _ _ _ _ _ k INV Hk)) as dR_10; dand3 dR_10 as r Hr Kr | destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr) ]). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

Lemma areach_free {resv} : forall st LB (b : block) (pf : aptr) (o o' : mem) ans st',
    AREACH_from resv st LB -> In b LB ->
    fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
    follow (mrun o (free st (Some pf))) ans = Some (o', st') ->
    AREACH_from resv st' (filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB).
Proof.
  (intros st LB b pf o o' ans st'; (first [ intro dR_20; dand8 dR_20 as L LS BL INV LIVE RESV SEC CR | intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]); intros Hb Hfst Hconc FF).
  (first [ pose proof ((Forall2_In_l _ _ _ _ CR Hb)) as dR_11; dex1 dR_11 as k; destruct dR_11 as [Hk (C1 & C2 & C3)] | pose proof ((Forall2_In_l _ _ _ _ CR Hb)) as dR_11; dand3 dR_11 as k Hk (C1 & C2 & C3) | destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)) ]).
  destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
  (first [ pose proof ((blk_region _ _ _ _ _ ((c, off), n) INV Hk)) as dR_12; dex1 dR_12 as r; destruct dR_12 as [Hr Kr] | pose proof ((blk_region _ _ _ _ _ ((c, off), n) INV Hk)) as dR_12; dand3 dR_12 as r Hr Kr | destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr) ]). cbn [bslot fst snd] in Hr.
  assert (Epf : pf = aadd c (UNIT * off)).
  { unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
    apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
  subst pf.
  (first [ pose proof ((free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF)) as dR_13; dand5 dR_13 as FT CP LIVE' LS' INV' | destruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV') ]).
  destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
  set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
  exists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
  split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
  split; [rewrite SEC'; exact SEC|].
  rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
  rewrite C1.
  pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                ltac:((intros b' k'; (first [ intro dR_21; dand3 dR_21 as D1 _ _ | intros (D1 & _ & _) ])); rewrite D1; reflexivity)) as CRF.
  eapply Forall2_impl_in; [exact CRF|]. (intros b' k' Hb' Hk'; (first [ intro dR_22; dand3 dR_22 as D1 D2 D3 | intros (D1 & D2 & D3) ])). split; [exact D1|]. split; [exact D2|]. rewrite D3.
  rewrite (conc_same st st' (bslot k')); [reflexivity|].
  rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
  (first [ pose proof ((blk_region _ _ _ _ _ k' INV' Hk')) as dR_14; dex1 dR_14 as r'; destruct dR_14 as [Hr' _] | pose proof ((blk_region _ _ _ _ _ k' INV' Hk')) as dR_14; dand3 dR_14 as r' Hr' _ | destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _) ]). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
Qed.

End CEIL.

Notation AREACH := (AREACH_from p0_reserved).  (* [comment removed for export] *)

