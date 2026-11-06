(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en.
Import ListNotations.
Local Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma INVL_init secret resv : 0 <= secret < 2 ^ 64 ->
INVL x0 (minit secret resv) (led_init resv) [] (fun _ => []).
Proof.
intros Hs.
assert (NOH : forall b m, ~ hosts (minit secret resv) b m) by (intros b m [ai H]; cbn in H; rewrite lookup_empty in H; discriminate).
assert (MR0 : forall m, MR (minit secret resv) m = meta0) by (intros m; unfold MR, get_meta_rec; cbn; rewrite lookup_empty; reflexivity).
split; [| split; [| split; [| split; [| split; [| split]]]]].
- constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
+ reflexivity.
+ rewrite map_to_list_empty. cbn. apply Permutation_refl.
+ rewrite map_to_list_empty. cbn. apply Permutation_refl.
+ split; [lia| left; reflexivity].
+ intros b l. split; [discriminate|]. intros (rid & r & H & _). rewrite lookup_empty in H. discriminate.
+ split; [reflexivity|]. intros rid r H. rewrite lookup_empty in H. discriminate.
+ split; [lia|]. split; [lia|]. intros rid off H. discriminate.
- constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
+ split; [lia|]. split; [lia|]. split; intros i v H; rewrite lookup_empty in H; discriminate.
+ split; [exact Hs|]. left. repeat split; reflexivity.
+ intros _. split; reflexivity.
+ split; [unfold NSLOTS; lia|]. intros H. lia.
+ intros sc Hsc. unfold usage, gcnt. cbn. rewrite lookup_empty, map_to_list_empty. reflexivity.
- constructor; cbn.
+ intros m _. rewrite MR0. reflexivity.
+ intros m b H. rewrite MR0 in H. discriminate.
+ intros b h H. rewrite lookup_empty in H. discriminate.
+ intros m [].
+ intros z [].
- constructor; cbn.
+ intros h. destruct h; cbn; [unfold active; cbn; rewrite lookup_empty|]; reflexivity.
+ intros h. exact I.
+ intros h. constructor.
+ intros h1 h2 m [].
+ intros m. rewrite MR0. cbn. split; [| reflexivity]. split; [intros [h []]| congruence].
+ intros m [].
+ intros sc m [].
+ intros h H. exfalso. apply H. reflexivity.
- constructor; cbn.
+ intros m b ai H. rewrite lookup_empty in H. discriminate.
+ intros b ai H. rewrite lookup_empty in H. discriminate.
+ intros m1 m2 b1 b2 ai1 ai2 H. rewrite lookup_empty in H. discriminate.
+ intros rid r H. rewrite lookup_empty in H. discriminate.
+ intros b h H. rewrite lookup_empty in H. discriminate.
- constructor; cbn.
+ intros s m i H. rewrite lookup_empty in H. discriminate.
+ intros b m i H. exfalso. exact (NOH _ _ H).
+ intros b m ai i H. rewrite lookup_empty in H. discriminate.
+ intros s H. discriminate.
+ constructor.
+ intros k [].
- constructor; cbn.
+ intros rid sh H. rewrite lookup_empty in H. discriminate.
+ intros rid sh H. rewrite lookup_empty in H. discriminate.
+ intros b m i H. exfalso. exact (NOH _ _ H).
+ intros b m o H. exfalso. exact (NOH _ _ H).
+ intros b m p i H. exfalso. exact (NOH _ _ H).
+ intros k m i [].
Qed.

#[using="Type"] Lemma INVL_set_live X st L BL LS v : INVL X st L BL LS -> INVL X st (set_live v L) BL LS.
Proof.
intros (IR & IA & IM & IL & IG & IS & ISH). split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
destruct IR; constructor; cbn; auto.
Qed.

#[using="Type"] Lemma cpath_follow {R} L (t : M R) L' r : cpath L t L' r -> exists ans, follow t ans = Some r /\ lafter L t ans = L'.
Proof.
induction 1 as [L0 r0|L0 e k z L1 r0 Hz Hp IH].
- exists []. split; reflexivity.
- destruct IH as (ans & Hf & Hl). exists (z :: ans).
destruct e; cbn [follow lafter]; try (split; [exact Hf| exact Hl]). cbn in Hz. discriminate.
Qed.

#[using="Type"] Lemma ctree_ok_paths {R} : forall (t : M R) L (P1 P2 : mled -> R -> Prop),
ctree_ok L t P1 -> (forall L' r, cpath L t L' r -> P2 L' r) -> ctree_ok L t P2.
Proof.
induction t as [r|e k IH]; intros L P1 P2 H HP; cbn [ctree_ok] in *.
- apply HP. constructor.
- destruct H as [He Hk]. split; [exact He|]. intros z Hz. apply (IH z _ P1); [apply Hk; exact Hz|].
intros L' r Hp. apply HP. econstructor; eauto.
Qed.

#[using="Type"] Lemma bl_remove_map c BL : map bslot (bl_remove c BL) = ap_remove c (map bslot BL).
Proof.
induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma In_bslot c BL : In c (map bslot BL) -> exists off n, In ((c, off), n) BL.
Proof.
intros H. apply in_map_iff in H as ([[c' off] n] & E & Hin). cbn in E. subst c'. exists off, n. exact Hin.
Qed.

Definition pans0 (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pupd0 (o : unit) (_ : ev) (_ : Z) : unit := o.
#[using="Type"] Lemma pans0_range : forall o p c h, 0 <= pans0 o p c h < 256.
Proof. intros. unfold pans0. lia. Qed.

Definition SIMREL (cs : mstate) (L : mled) : Prop :=
exists st BL LS, strip st = cs /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL.

#[using="Type"] Theorem creach_sim cs L : creach cs L -> SIMREL cs L.
Proof.
induction 1 as [resv|cs L n L' cs' r CR IH Hn CP|cs L c L' cs' CR IH Hc CP].
- exists (minit 0 resv), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; lia| reflexivity].
- destruct IH as (st & BL & LS & <- & INV & LIVE).
destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
+ destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
+ destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
- destruct IH as (st & BL & LS & <- & INV & LIVE).
rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
Qed.

#[using="Type"] Theorem cmalloc_contract_proof : forall cs L n,
creach cs L -> 0 <= n ->
ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
intros cs L n CR Hn. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
apply (ctree_ok_paths _ L (fun _ _ => True)).
- apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
- intros L' [cs' r] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE', LIVE. exact NI.
Qed.

#[using="Type"] Theorem cfree_contract_proof : forall cs L c,
creach cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
intros cs L c CR Hc. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
apply ptree_ctree_ok.
eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.

#[using="Type"] Theorem cmalloc_ctree st L BL LS n :
INVL x0 st L BL LS -> (forall c, In c (ld_live L) -> In c (map bslot BL)) -> 0 <= n ->
ctree_ok L (cmalloc (strip st) n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
intros INV LIVE Hn.
apply (ctree_ok_paths _ L (fun _ _ => True)).
- apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
- intros L' [cs' r] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE'. intros Hc. apply NI. apply LIVE. exact Hc.
Qed.

#[using="Type"] Theorem cfree_ctree st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL -> ctree_ok L (cfree (strip st) (Some c)) (fun _ _ => True).
Proof.
intros INV Hk. apply ptree_ctree_ok.
eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.

#[using="Type"] Theorem cmalloc_leaf_INVL st L BL LS n L' cs' r :
INVL x0 st L BL LS -> 0 <= n -> cpath L (cmalloc (strip st) n) L' (cs', r) ->
ld_live L' = ld_live L /\
exists st' LS', strip st' = cs' /\
match r with
| None => INVL x0 st' L' BL LS'
| Some c => exists off, 0 <= off <= 255 /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
end.
Proof.
intros INV Hn CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in LIVE', RES. split; [exact LIVE'|].
exists st'. destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
- destruct RES as (off & LS' & _ & Hoff & INV' & NI). exists LS'. split; [reflexivity|]. exists off. auto.
- destruct RES as (LS' & INV'). exists LS'. split; [reflexivity| exact INV'].
Qed.

#[using="Type"] Theorem cfree_leaf_INVL st L BL LS c off n L' cs' :
INVL x0 st L BL LS -> In ((c, off), n) BL -> cpath L (cfree (strip st) (Some c)) L' cs' ->
ld_live L' = ld_live L /\ exists st' LS', strip st' = cs' /\ INVL x0 st' L' (bl_remove c BL) LS'.
Proof.
intros INV Hk CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'. split; [exact LIVE'|].
exists st', LS'. split; [reflexivity| exact INV'].
Qed.

End RC__1.
