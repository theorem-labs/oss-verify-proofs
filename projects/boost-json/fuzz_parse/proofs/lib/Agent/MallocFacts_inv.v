(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext
  MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~05block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~kc3blk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~p06mstate37Corelib4Init5Logict72eqt73and37Corelib7Numbers7BinNumsv61Zkc5bslot08blk_addr08blk_size08blk_slotkc4boffkc5bsizep04UNITp04concp04cptr46Stdlib6ZArith6BinInt1Zhld3addhld3mul37Corelib4Init9Datatypesho34list89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentfMallocFacts_inv3HCW~~~~~~hq35corr136Stdlib5Lists4Listhv87Forall2p06regionv61N25stdpp9countableii3bN_countable35stdpp7numbers1Nik36eq_decho34Someho33fstho36optiont72ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~inc4mledkc4INVLkc6extrasp07RKGroupp04aptrp05lheadp06r_kindp05rkindp09s_regionshv82In25stdpp4basejgc6lookup25stdpp4gmapji24gmapji2bgmap_lookupho34prodp04aaddinc7ld_resvincaevent_postp02evho34negbp08aptr_eqb37Corelib5Lists7ListDefjo53mapkc9bl_remove36Stdlib4Bool4Booljqf7Is_truejgc5NoDupjgc6filter25stdpp9decidablejtfbIs_true_dec35stdppblist_basics4listjvfblist_filter0bAREACH_fromhq34CORR69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~kjb7hsecretinc7ld_livekc2x0p08s_secret" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition corr1 : ltac2:(zQ "30!k5!oa!se>2st$2>1b$0>1k$1P") := ltac2:(zQ "h10!ub!v0!hgf!hh3!hhb!hi5!hif!k5!oa!hj9!hk0!hk8!hkf!hl6!se!hn5!hnc\2st$e\1b$7\1k$8@2$1@3$0$d@1$6^2@1$3^1@2$1@3$0$2@1$5^2@1$a^1@3$0$2@1$4^2@2$f@2$c^3@1$3^1@2$h0$b@1$9^1").
Definition CORR : ltac2:(zQ "40!hpb!k5!oa!se>2st$3>2LB@1$0$1>2BL@1$0$2P") := ltac2:(zQ "60!hpb!k5!oa!huf!se!igb\2st$4\2LB@1$0$1\2BL@1$0$2@5$5$1$2@1$3^3^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blk_region : ltac2:(zQ "hc0!ih6!ihf!oa!hpb!ub!ij4!il4!ile!im6!imd!v0!in7!hgf!ir8!is0!hh3!is7!it0!ita!iu1!se!iu9!iv2!iva!jg6!jh8!jie!jj6>1X$h0>2st$h4>1L$d>2BL@1$3$2>2LS>0$h3@1$3$h2>1k$2>0@5$e^6^5^4^3^2>0@3$h8$2^2^4@2$b$0\1r$0@2$a@3$4@1$9$0@6$h9$1$0@4$ha$1$6$5$0@4$hb$1$6$5$0@3$8$1$c@1$f^4@1$h7^8@2$7$0^1@3$4$h6@1$h5^1$h1").
Proof. intros X st L BL LS k.
  intros INV Hk. npose INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

Lemma conc_aadd : ltac2:(zQ "h30!ih6!ihf!hgf!ub!hkf!ij4!il4!ile!im6!imd!jk5!in7!jkd!se!iva!hn5!jh8!jie!jj6>2st$d>1p@2$a$1$2>1d$2>0@2$b$0\1r$0@3$3@1$9$0@6$h0$1$0@4$h1$1$6$5$0@4$h2$1$6$5$0@3$8$1$2^3@1$e^4@2$7$0^1@3$3$2@2$4^4@2$c^3^2@2$f@2$4^4^3^2").
Proof. intros st p d. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.

Lemma conc_same : ltac2:(zQ "h20!ih6!ihf!hgf!ij4!il4!ub!ile!im6!imd!hkf!se!iva!jh8!jie!jj6!jk5!v0!in7>2st$a>3st'$a>1p@2$f$1$2>0@2$h1$0\1r$0@2$h0@3$5@1$8$0@6$c$1$0@4$d$1$4$3$0@4$e$1$4$3$0@3$7$1$2^2@1$b^4@2$6$0^1@3$5@1$8$0@6$c$1$0@4$d$1$4$3$0@4$e$1$4$3$0@3$7$1$2^2@1$b^3@2$6$0^1@3$5$2@2$9^3^2@2$9^4^2").
Proof. intros st st' p. (intros nd_i1; ndestruct nd_i1 as (r & H1 & H2)). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.

Lemma event_post_resv : ltac2:(zQ "80!hgf!jl4!hpb!jk5!ub!jlf!ir8!jmd>1L$6>1e$7>1z$0@3$4@1$2@2$3$0$0@1$1@3$5^3^2^1@1$1^3").
Proof. intros L e z.
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
  ndestruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
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

Lemma bl_remove_filter : ltac2:(zQ "e0!oa!hpb!hh3!hl6!jn2!jna!ub!jpc!jq3!js1!jsc!jt5!jv0!kh7>1c$3>2BL@1$1$0>0@2$a$3@4$7$0$3$2^1@3$6@1$1$0@2$8^3^2@6$b$0@1$1$0@1$d$0\1k$0@1$9@1$4@2$5@1$2^1^4\1x$0@1$c@1$4@2$5@1$2^1^4^2").
Proof. intros c BL.
  induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
  cbn in ND. apply NoDup_cons in ND as [NI ND].
  destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
  - symmetry. apply filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
    exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
  - f_equal. apply IH. exact ND.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem areach_inv : ltac2:(zQ "h70!hpb!hgf!v0!ub!in7!oa!jk5!ir8!ita!hl6!iu1!jpc!ki6!k5!kj3!kn8!ko3!jl4!is0!hh3!koe!se!kp3>4resv@1$0@2$6$1$1>2st$h5>2LB@1$0$d>0@4$c?4HSEC^3^2^1@2$4$7\1L$7@2$4>0$a@1$0$8\2LS>0$a@1$0$8@2$4@1$0$5\2BL@1$0$5@2$2@5$h2$h4^6^3^1^2@2$2@3$3@1$0$9@1$h0^3@4$b$5$9$h3^1@2$2@3$3@1$0@2$6$1$1@1$h1^3^7@2$2@3$3$1@1$h6^6@1$f?4HSEC@3$e^6^5^1").
Proof. intros resv st LB.
  induction 1 as [|st LB n o o' ans st' pf cst c AR IH Hn FF FC|st LB n o o' ans st' AR IH Hn FF|st LB b pf o o' ans st' AR IH Hb Hfst Hconc FF].
  - exists (led_init resv), (fun _ => []), []. split; [apply INVL_init; hsb; lia|]. repeat split; try reflexivity. constructor.
  - ndestruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    ndestruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & _ & RES).
    unfold mrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc.
    ndestruct RES as (off & LS' & Epf & Hoff & INV' & NI).
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    nexists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd]. rewrite Epf. apply conc_aadd.
      destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _). exists r. exact Hr.
    + eapply Forall2_impl_in; [exact CR|]. (intros b k Hb Hk nd_i2; ndestruct nd_i2 as (C1 & C2 & C3)). split; [exact C1|]. split; [exact C2|]. rewrite C3.
      rewrite (conc_same st st' (bslot k)); [reflexivity|].
      destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - ndestruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    ndestruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & _ & RES).
    destruct rc as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    nexists (set_live (map bslot BL) L'), LS', BL.
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    eapply Forall2_impl_in; [exact CR|]. (intros bb k Hb Hk nd_i3; ndestruct nd_i3 as (C1 & C2 & C3)). split; [exact C1|]. split; [exact C2|]. rewrite C3.
    rewrite (conc_same st st' (bslot k)); [reflexivity|].
    destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - ndestruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
    destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
    assert (Epf : pf = aadd c (UNIT * off)).
    { unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
      apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
    subst pf.
    ndestruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV').
    destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
    set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
    nexists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    rewrite C1.
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                  ltac:((intros b' k' nd_i4; ndestruct nd_i4 as (D1 & _ & _)); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. (intros b' k' Hb' Hk' nd_i5; ndestruct nd_i5 as (D1 & D2 & D3)). split; [exact D1|]. split; [exact D2|]. rewrite D3.
    rewrite (conc_same st st' (bslot k')); [reflexivity|].
    rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
    destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
Qed.


(* [comment removed for export] *)
Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
  intros resv st LB blk off AR Hb Ho Ha.
  ndestruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off.
  exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.

End HCW.

