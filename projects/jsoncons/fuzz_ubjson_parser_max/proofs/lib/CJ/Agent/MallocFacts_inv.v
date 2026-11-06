(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext
MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep MallocTree MallocBlocks.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocFacts_inv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_inv.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Bool.Bool."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.list_basics.list."; "stdpp.numbers.N."], [["0BL"; "1Some"; "1fst"; "1list"; "1negb"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "3map"; "4N"; "4Z"; "0L"; "0LB"; "0LS"]; ["0RUNp"; "5AREACH_from"; "5block"; "6CORR"; "7secret_val"; "8event_post"; "8ld_live"; "8ld_resv"; "8mled"; "9INVL"; "9bl_remove"; "9blk"; "9bslot"; "9extras"; "9x0"; ":RKGroup"]; [":aadd"; ":aptr"; ":aptr_eqb"; ":conc"; ":cptr"; ":ev"; ":lhead"; ":mstate"; ":r_kind"; ":region"; ":rkind"; ":s_regions"; ":s_secret"; ";Is_true"; "<In"; "=add"]; ["0X"; "0c"; "0d"; "0e"; "0k"; "0p"; "0r"; "0resv"; "0st"; "0st'"; ">NoDup"; ">filter"; ">lookup"; "?N_countable"; "@Is_true_dec"; "Agmap"]; ["Agmap_lookup"; "Blist_filter"; "Ceq_dec"; "0x"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition corr1 (st : mstate) (b : block) (k : blk) : Prop :=
blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k.
Definition CORR (st : mstate) (LB : list block) (BL : list blk) : Prop := Forall2 (corr1 st) LB BL.
Lemma blk_region : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv "QO'M'Q7'H'3&K%211'Q6&Q1%511p031&Iv@r6r5r4r3r2%76654321&Q>%13?35'9'Q9'7'8'5%114&QL';'QO&R2&QM%34421:&R0%14643<&2'<&L%11G%43;31&Q;r8%211%@6?E;941(1r1%22H1%G3E41'Q:&Q8%115(O%L3421%N261qS>Q01%Q22Q11p0Q41p0Q71pS:QE1pQ0QA1p2QF1pLQJ1pSBQL1pS2QN1").
Proof. intros X st L BL LS k.
intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.
Lemma conc_aadd : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv "Q;'Q7'6';'<%3221'9'Q9'8'5%113&QL'QO&R2&QM%34<218&R0%14>43:&2r3%23A@1&Q;r4%211%=6EA9741(1r1%22D1%D3B41qS>F1%H2G1&Q3&Q0r2%22?1%42=1&Q?%62?B%2215%O3Q341p0:1pS6Q51pS<Q51pSBQ:1").
Proof. intros st p d. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.
Lemma conc_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv "Q<'Q7'6';'<%3221'9'Q9'7'8'5%114&QL'QO&R2&QM%34=219&R0%14?43;&2r2%23BA1&Q;r4%211%=6FB9741(1r1%22E1%D3B41r3%911%D6MI@>;1%H3F15%J251qS>L1%N2M1&Q3%128B%22@C%O3Q421p051pS<Q51pSDQ:1pSBQ;1").
Proof. intros st st' p. intros (r & H1 & H2). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.
Lemma event_post_resv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv "D'H'Q5'<'8'3'6%1244%311&G&Er3r2r1%43321%611%715%=3921pT:?1pS8A1pLC1").
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
destruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
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
Lemma bl_remove_filter : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv "Q3&Q4'3&K%211'QJ&:&Lr1%346821%5291'8&Jr3r2%3221&QK&R1%11?&Q=&4&Q2%?1>r4%3221%511%711qS:H1&QN%114qT8K1%?6LK=41A%E3LA1p0G1p2N1pS4Q21").
Proof. intros c BL.
induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
cbn in ND. apply NoDup_cons in ND as [NI ND].
destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
- symmetry. apply filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
- f_equal. apply IH. exact ND.
Qed.
Section SE.
Local Abbreviation SEC_T_areach_inv := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv "QN'3'6'<%2211%411'Q7&B%711'Av@r3r2r1%544321'9'H'Q6&Q1%B11p031&K%E11'7&I&Nr6%36A21@>?'8&Q4%M11&F%11E&:&L%24>61F%83641&G%11Kr7%<3Q321&Q<%11@&D%11Q2%A3Q:31&Cr5%23F1Q3%J241%K2:1%L2?1%M2I1q2O1%Q72Q01qQ0Q31%Q92Q41qLQ91%Q;2Q:1p0Q=1pNQD1pSBQG1pS@QI1")) (only parsing).
Variable resv : ltac:(sec_ty2 constr:(SEC_T_areach_inv) 0%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_areach_inv) 1%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_areach_inv) 2%nat 0%nat).
Theorem areach_inv : ltac:(sec_stmt2 constr:(SEC_T_areach_inv) 3%nat 0%nat).
Proof.
induction 1 as [|st LB n o o' ans st' pf cst c AR IH Hn FF FC|st LB n o o' ans st' AR IH Hn FF|st LB b pf o o' ans st' AR IH Hb Hfst Hconc FF].
- exists (led_init resv), (fun _ => []), []. split; [apply INVL_init; pose_secret; lia|]. repeat split; try reflexivity. constructor.
- destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
unfold mrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc.
destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
set (L' := lafter L (cmalloc (strip st) n) ans) in *.
exists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
split; [rewrite GPS; exact SEC|].
constructor.
+ split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd]. rewrite Epf. apply conc_aadd.
destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _). exists r. exact Hr.
+ eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
rewrite (conc_same st st' (bslot k)); [reflexivity|].
destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
- destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
destruct rc as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
set (L' := lafter L (cmalloc (strip st) n) ans) in *.
exists (set_live (map bslot BL) L'), LS', BL.
split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
split; [rewrite GPS; exact SEC|].
eapply Forall2_impl_in; [exact CR|]. intros bb k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
rewrite (conc_same st st' (bslot k)); [reflexivity|].
destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
- destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
assert (Epf : pf = aadd c (UNIT * off)).
{ unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
subst pf.
destruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV').
destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
exists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
split; [rewrite SEC'; exact SEC|].
rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
rewrite C1.
pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
rewrite (conc_same st st' (bslot k')); [reflexivity|].
rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
Qed.
End SE.
Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
intros resv st LB blk off AR Hb Ho Ha.
destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
assert (off = bo) by (unfold UNIT in *; lia). subst off.
exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.
End CEIL_WRAP_1.
