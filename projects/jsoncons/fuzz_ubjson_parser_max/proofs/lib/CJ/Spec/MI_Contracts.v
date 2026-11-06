(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_List MI_Ext
MI_Pres2 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Contracts () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Contracts.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0BL"; "1Some"; "1list"; "1nil"; "1pair"; "1prod"; "1unit"; "2True"; "2and"; "2eq"; "2ex"; "3map"; "4Z"; "0L"; "0LS"; "0RUNp"]; ["5ap_remove"; "5creach"; "5ctree_ok"; "5ld_live"; "5led_init"; "5mled"; "5set_live"; "6SIMREL"; "6pans0"; "7INVL"; "7bl_remove"; "7blk"; "7bslot"; "7extras"; "7x0"; "8aptr"]; ["8cfree"; "8cptr"; "8lhead"; "8minit"; "8mstate"; "9In"; ":le"; ":lt"; ":pow"; "0X"; "0c"; "0cs"; "0h"; "0n"; "0o"; "0off"]; ["0p"; "0resv"; "0secret"; "0st"; "0v"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_INVL_init := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "Q4'<'2'5%1233%311'8&Q6zr2%3221&Q7&Q8+2+R0%3221%5271%;271&Iv?&N&Q3r3%221>&D%11@(3&K%211'Q2&O%511q031%?6>=:851p0A1pS4N1pS6Q31")) (only parsing).
Variable secret : ltac:(sec_ty2 constr:(SEC_T_INVL_init) 0%nat 0%nat).
Variable resv : ltac:(sec_ty2 constr:(SEC_T_INVL_init) 1%nat 0%nat).
Lemma INVL_init : ltac:(sec_stmt2 constr:(SEC_T_INVL_init) 2%nat 0%nat).
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
End SE.
Lemma INVL_set_live : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "O'M'Q4'E'2&K%211'Q2&O%511p031&Q1%811&Iv?r6r5r4r3r2%76654321r7&F%1247%;6:39176p051pS:>1pNA1p2F1pLJ1pS8L1pRDN1").
Proof. intros X st L BL LS v.
intros (IR & IA & IM & IL & IG & IS & ISH). split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
destruct IR; constructor; cbn; auto.
Qed.
Lemma cpath_follow {R} L (t : M R) L' r : cpath L t L' r -> exists ans, follow t ans = Some r /\ lafter L t ans = L'.
Proof.
induction 1 as [L0 r0|L0 e k z L1 r0 Hz Hp IH].
- exists []. split; reflexivity.
- destruct IH as (ans & Hf & Hl). exists (z :: ans).
destruct e; cbn [follow lafter]; try (split; [exact Hf| exact Hl]). cbn in Hz. discriminate.
Qed.
Lemma ctree_ok_paths {R} : forall (t : M R) L (P1 P2 : mled -> R -> Prop),
ctree_ok L t P1 -> (forall L' r, cpath L t L' r -> P2 L' r) -> ctree_ok L t P2.
Proof.
induction t as [r|e k IH]; intros L P1 P2 H HP; cbn [ctree_ok] in *.
- apply HP. constructor.
- destruct H as [He Hk]. split; [exact He|]. intros z Hz. apply (IH z _ P1); [apply Hk; exact Hz|].
intros L' r Hp. apply HP. econstructor; eauto.
Qed.
Lemma bl_remove_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "C&Q1'2&K%211'9%415&;&L&Jr2r1%3221%64:<51&@%84<>74%2261%<3;41p2>1pRFB1").
Proof. intros c BL.
induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.
Lemma In_bslot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "M&Q1'2&K%211&Q5r2&;&Lr1%347921%63:51':'<'5%12>2%2213(4r5%24B61=%34571;r4%A3621qRL:1%<2;1qS0<1%>2=1p0@1p2H1pRFL1").
Proof. intros c BL.
intros H. apply in_map_iff in H as ([[c' off] n] & E & Hin). cbn in E. subst c'. exists off, n. exact Hin.
Qed.
Definition pans0 (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pupd0 (o : unit) (_ : ev) (_ : Z) : unit := o.
Lemma pans0_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "E'6&O'<'8&Q6z&Hr4r3r2r1%544321%8271&Q7+X0%2241%=241pRJ?1pRF@1pS2B1pRND1").
Proof. intros. unfold pans0. lia. Qed.
Definition SIMREL (cs : mstate) (L : mled) : Prop :=
exists st BL LS, strip st = cs /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL.
Section SE.
Local Abbreviation SEC_T_creach_sim := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "='Q4'E'Av?r2r1%43321&Gr3%2215p041pL:1pRH<1")) (only parsing).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_creach_sim) 0%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_creach_sim) 1%nat 0%nat).
Theorem creach_sim : ltac:(sec_stmt2 constr:(SEC_T_creach_sim) 2%nat 0%nat).
Proof.
induction 1 as [resv|cs L n L' cs' r CR IH Hn CP|cs L c L' cs' CR IH Hc CP].
- exists (minit secret_val resv), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; pose_secret; lia| reflexivity].
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
End SE.
Section SE.
Local Abbreviation SEC_T_cmalloc_contract_proof := (forall cs L n, creach cs L -> 0 <= n ->
ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end)) (only parsing).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_cmalloc_contract_proof) 0%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_cmalloc_contract_proof) 1%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_cmalloc_contract_proof) 2%nat 0%nat).
Theorem cmalloc_contract_proof : ltac:(sec_stmt2 constr:(SEC_T_cmalloc_contract_proof) 3%nat 0%nat).
Proof.
intros CR Hn.
destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
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
End SE.
Theorem cfree_contract_proof : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Contracts "L'Q4'E&Q1'Av?r3r2%43321&Q5&C%115%33951&Br4&Q0r5(1%12?<%4231'7q0D1q0D1%:5BF941p0<1p0A1pRFG1pLI1pRHK1").
Proof.
intros cs L c CR Hc. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
apply ptree_ctree_ok.
eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.
End CEIL_WRAP_1.
