(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 Q5Rg QlEo_c1 QnDM_c1 Q2qa Q4J3 QytA Qy5Y QlQE QPjm QZAi QUZl Q7S0 Ql2m QGeV QFkE Q6y7 QDUx QJE4 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QnDM_c1.Mq0 Q2qa.Mq1 Q4J3.Mq1 QytA Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1.
Import Q9A7.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq3 QFkE Q6y7 QDUx.Mq4 QDUx.Mq5 QDUx.Mq6.
Import QJE4.Mq2.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r).

Definition lbrm (LB : list block) (blk : block) : list block :=
filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.

#[using="Type"] Lemma oracle_ok_refl m st : oracle_ok m m st.
Proof. intros rid r q h _ _ _ _ _. reflexivity. Qed.

#[using="Type"] Lemma oracle_ok_hdr_st o m st pf : ticks_ok st -> oracle_ok o m st -> oracle_ok o m (hdr_st st pf).
Proof.
intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
rewrite hdr_st_cell_read in Hc by exact TK.
destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

#[using="Type"] Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
- apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- reflexivity.
Qed.

#[using="Type"] Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof.
pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.
End RC__1.

Ltac cover_intervals tac :=
let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
intros lo0 hi0 HW y Hy; cbn [In] in HW;
repeat (destruct HW as [HW|HW]); try contradiction;
injection HW; intros; subst lo0 hi0; tac y Hy.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.

End FREE.

#[using="Type"] Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
cbn [map] in ND. inversion ND; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
- exfalso. apply H1. rewrite E. apply in_map. exact Hy.
- exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

#[using="Type"] Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
(forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
rewrite IH by (intros x Hx; apply HE; right; exact Hx).
destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
pose proof (HE a (or_introl eq_refl)); tauto.
Qed.

End RC__2.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya QPiB Qatc QSfG QdBa QpFQ QLaA QQg5 QoCS QQCz QhnL Q4en QBv7 QAnn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 QdBa.Mq0 QpFQ QLaA.Mq0 QQg5.Mq2 QoCS.Mq0 QQCz QhnL Q4en QBv7 QAnn.
Import QnDM_c1.Mq0 QytA Qy5Y.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition corr1 (st : mstate) (b : block) (k : blk) : Prop :=
blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k.
Definition CORR (st : mstate) (LB : list block) (BL : list blk) : Prop := Forall2 (corr1 st) LB BL.

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
destruct e as [rq|a len prot flags|a len|a len prot|p c h|w|ma ol nl fl]; cbn; try reflexivity.
4:{ destruct (is_errno_form z); reflexivity. }
- destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
- destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
- destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
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

#[using="Type"] Theorem areach_inv resv {sec} st LB : AREACH_from resv sec st LB ->
exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = sec /\ CORR st LB BL.
Proof.
induction 1 as [|st LB n o o' ans st' pf cst c AR IH Hn FF FC|st LB n o o' ans st' AR IH Hn FF|st LB b pf o o' ans st' AR IH Hb Hfst Hconc FF|st LB b off n o o' ans st' r cst rw AR IH Hb Hoff Hn Ha FF FC].
- exists (led_init resv), (fun _ => []), []. split; [apply INVL_init; lia|]. repeat split; try reflexivity. constructor.
- destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR [GPS GPI]] & RES).
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
destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR [GPS GPI]] & RES).
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
destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as (SUB & SEC' & _).
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
-
exact (realloc_areach_step pans_mem pupd_mem pans_mem_range resv st LB b off n o o' ans st' r cst rw IH Hb Hoff Hn Ha FF FC).
Qed.

#[using="Type"] Lemma areach_hdr_ok_proof : forall {resv sec} st LB (blk : block) (off : Z),
AREACH_from resv sec st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
intros resv sec st LB blk off AR Hb Ho Ha.
destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
assert (off = bo) by (unfold UNIT in *; lia). subst off.
exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
let needed := n + IB + UNIT in
let st4 := upd_meta g (fun mr =>
m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
(m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^63.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma bf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.

#[using="Type"] Lemma bf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma bm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma bm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma bf_regions : s_regions stF = s_regions st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_areas : s_areas stF = s_areas st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_reserved : s_reserved stF = s_reserved st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_next : s_next_rid stF = s_next_rid st3. Proof. reflexivity. Qed.
#[using="GN"] Lemma bf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
#[using="Type"] Lemma bm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma bf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="HC stM"] Lemma bf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite bf_ctx. reflexivity. Qed.

#[using="Type"] Lemma ticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

#[using="NR"] Lemma bf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

#[using="Type"] Lemma bf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

#[using="Type"] Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^63 - 4097 ->
malloc_core full_lay st1 n =
SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
if is_err r then ret (st1, None) else
let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
alloc_meta (step_seq st2) (fun st3 go =>
match go with
| None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
| Some g => ret (big_final st3 g rid n, Some (g, 0))
end) (ret (st1, None))).
Proof.
intros Hn. unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.

#[using="Type"] Lemma unk_agree_transfer st st' o m m' :
unk_agree st o m ->
(forall rid r, (s_regions st') !! rid = Some r -> r_kind r = RKGroup ->
((s_regions st) !! rid = Some r /\ get_shadow st' rid = get_shadow st rid /\
(forall off, grp_hdr_cov st rid off -> grp_hdr_cov st' rid off) /\
(forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st rid) off = Unknown h ->
~ grp_hdr_cov st' rid off -> m' (wa (r_base r + off)) = m (wa (r_base r + off))))
\/ (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st' rid) off = Unknown h -> grp_hdr_cov st' rid off)) ->
unk_agree st' o m'.
Proof.
intros UA H rid r off h Hr Hk Ho Hc NG.
destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
- rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
- exfalso. apply NG. eapply NEW; eauto.
Qed.

#[using="Type"] Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. intros EG (b & gh & Hb & E & R). exists b, gh. rewrite EG. auto. Qed.

#[using="Type"] Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
destruct a as [e|b]; cbn [range_val]; intros He.
- unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (2 ^ 64 - e =? 0); reflexivity.
- reflexivity.
Qed.

#[using="Type"] Lemma mmap_answer_ok_err live len e : 1 <= e <= 4095 -> mmap_answer_ok live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof.
intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
- replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- apply Z.ltb_lt. lia.
Qed.

#[using="Type"] Lemma mmap_answer_ok_addr live len xa : 0 <= len ->
mmap_addr_ok len [] xa = true -> mmap_answer_ok live len xa = true ->
0 < xa /\ xa mod 4096 = 0 /\ xa + round_up_pg len <= alloc_ceiling /\ ranges_free live xa (round_up_pg len) = true /\ is_err xa = false.
Proof.
intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
rewrite QYTG.Mq0.alloc_ceiling_State in A3. change page_size with 4096 in A1.
unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
assert (NE : is_errno_form xa = false).
{ unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; unfold alloc_ceiling in A3; lia). reflexivity. }
destruct B as [B|B]; [rewrite NE in B; discriminate|].
rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. unfold alloc_ceiling in A3. lia.
Qed.

#[using="Type"] Lemma brk_link_ps_ext st st' s :
c_brk (ctx st') = c_brk (ctx st) ->
(forall rid off, c_brk (ctx st) = BrkLive rid off -> conc st' (rid, off) = conc st (rid, off)) ->
brk_link_ps st s -> brk_link_ps st' s.
Proof.
intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
rewrite (EC rid off eq_refl). exact BL.
Qed.

#[using="Type"] Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) :
0 <= lo -> hi <= 2^64 ->
(forall a, 0 <= a < 2^64 -> (a < lo \/ hi <= a) -> m' (wa a) = m (wa a)) -> munch [(lo, hi)] m m'.
Proof.
intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.

#[using="Type"] Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
destruct (Z.eq_dec (off / 16) 0) as [E|NE].
- rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
- rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

#[using="Type"] Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma big_stride n rid : 0 <= n < 2^63 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite bf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Definition AMP_BIG (am_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, AREACH st LB -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
am_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

Section BIG.
Variable am_pre : mstate -> Prop.

Hypothesis AMP : AMP_BIG am_pre.

End BIG.

End RC__1.
