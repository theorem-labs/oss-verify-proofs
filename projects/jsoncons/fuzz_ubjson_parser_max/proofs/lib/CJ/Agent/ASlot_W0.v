(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep MallocKit_AB MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W0.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1bool"; "1option"; "1orb"; "1true"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "5ctx_ta_same"; "5geom_same"; "4geom_same"; "4ta_rel"; "6active"; "6aptr"]; ["6bounces"; "6conc"; "6decay_bounces"; "6g_meta"; "6get_meta_rec"; "6get_shadow"; "6ghdr"; "6m_avail"; "6m_freed"; "6m_set_next"; "6m_set_prev"; "6m_sizeclass"; "6mctx"; "6meta"; "6mstate"; "6optr"]; ["6put_meta"; "6s_groups"; "6set_active"; "6set_bounce"; "6set_group_active_idx"; "6shadow"; "7land"; "7le"; "7lt"; "7pow"; "7sub"; "7testbit"; "0ai"; "0b"; "0c"; "0g"]; ["0h"; "0i"; "0n"; "0p"; "0q"; "0r"; "0rid"; "0sc"; "0st"; "0st1"; "0st2"; "8lookup"; "9N_countable"; "9Z_countable"; "9prod_countable"; ":prod_eq_dec"]; [";gmap"; ";gmap_lookup"; "<eq_dec"; "=eq_dec"; "0v"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition ctx_ta_same (c c1 : mctx) : Prop :=
c_secret c1 = c_secret c /\ c_init_done c1 = c_init_done c /\ c_mmap_counter c1 = c_mmap_counter c
/\ c_free_meta_head c1 = c_free_meta_head c /\ c_avail_meta c1 = c_avail_meta c /\ c_avail_meta_count c1 = c_avail_meta_count c
/\ c_avail_meta_area_count c1 = c_avail_meta_area_count c /\ c_meta_alloc_shift c1 = c_meta_alloc_shift c
/\ c_meta_area_head c1 = c_meta_area_head c /\ c_meta_area_tail c1 = c_meta_area_tail c /\ c_avail_meta_areas c1 = c_avail_meta_areas c
/\ c_usage c1 = c_usage c /\ c_unmap_seq c1 = c_unmap_seq c /\ c_seq c1 = c_seq c /\ c_brk c1 = c_brk c.
Definition geom_same (r r1 : meta) : Prop :=
m_mem r1 = m_mem r /\ m_last_idx r1 = m_last_idx r /\ m_freeable r1 = m_freeable r /\ m_sizeclass r1 = m_sizeclass r /\ m_maplen r1 = m_maplen r.
Record ta_rel (sc : Z) (st st1 : mstate) : Prop := mkTR {
tr_regions : s_regions st1 = s_regions st;
tr_shadow : s_shadow st1 = s_shadow st;
tr_next : s_next_rid st1 = s_next_rid st;
tr_areas : s_areas st1 = s_areas st;
tr_slots : s_slots st1 = s_slots st;
tr_tick : s_tick st1 = s_tick st;
tr_secret : s_secret st1 = s_secret st;
tr_reserved : s_reserved st1 = s_reserved st;
tr_ctx : ctx_ta_same (ctx st) (ctx st1);
tr_active : forall c, c <> sc -> active st1 c = active st c;
tr_bounces : forall i, 0 <= bounces st i -> 0 <= bounces st1 i <= bounces st i;
tr_geom : forall q, geom_same (get_meta_rec st q) (get_meta_rec st1 q);
tr_bits : forall q i, 0 <= i ->
Z.testbit (m_avail (get_meta_rec st1 q)) i || Z.testbit (m_freed (get_meta_rec st1 q)) i = true ->
Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true;
tr_mrange : forall q, 0 <= m_avail (get_meta_rec st q) < 2^32 -> 0 <= m_freed (get_meta_rec st q) < 2^32 ->
0 <= m_avail (get_meta_rec st1 q) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 q) < 2^32;
tr_groups : forall b, (exists gh1, (s_groups st1) !! b = Some gh1) <-> (exists gh, (s_groups st) !! b = Some gh);
tr_gmeta : forall b gh1, (s_groups st1) !! b = Some gh1 ->
exists gh, (s_groups st) !! b = Some gh /\ g_meta gh1 = g_meta gh
/\ (g_active_idx gh1 = g_active_idx gh
\/ (0 <= g_active_idx gh1 <= 31 /\ forall g, g_meta gh = Some g -> m_sizeclass (get_meta_rec st g) <> 0))
}.
Lemma ctx_ta_same_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "5'L&:r1%2211pRN41").
Proof. intros c. repeat split; reflexivity. Qed.
Lemma geom_same_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "5'M&;r1%2211pS<41").
Proof. intros r. repeat split; reflexivity. Qed.
End CEIL_WRAP_1.
Ltac ta_auto :=
first [ reflexivity
| apply ctx_ta_same_refl
| (cbn; repeat split; reflexivity)
| (intros; apply geom_same_refl)
| (intros ? ? ? Hb__; exact Hb__)
| (intros ? Ha__ Hf__; split; [exact Ha__| exact Hf__])
| (intros ? ? Hq__; eexists; split; [exact Hq__|]; split; [reflexivity| left; reflexivity])
| (intros; unfold bounces, ctx in *; cbn in *; lia)
| idtac ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma ta_rel_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "8'9'N'=r2r1%33211pSB51pS@71").
Proof. intros sc st. constructor; ta_auto. Qed.
Section SE.
Local Abbreviation SEC_T_ta_rel_trans := (ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "A'9'N'=r4r3r2%43321r5%63143r6%83136p031p061pSF<1pSD=1pSB>1pS@@1")) (only parsing).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_ta_rel_trans) 0%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ta_rel_trans) 1%nat 0%nat).
Variable st1 : ltac:(sec_ty2 constr:(SEC_T_ta_rel_trans) 2%nat 0%nat).
Variable st2 : ltac:(sec_ty2 constr:(SEC_T_ta_rel_trans) 3%nat 0%nat).
Lemma ta_rel_trans : ltac:(sec_stmt2 constr:(SEC_T_ta_rel_trans) 4%nat 0%nat).
Proof.
intros A B. destruct A as [R1 S1 N1 A1 L1 T1 E1 V1 C1 AC1 B1 G1 BI1 MR1 GR1 GM1].
destruct B as [R2 S2 N2 A2 L2 T2 E2 V2 C2 AC2 B2 G2 BI2 MR2 GR2 GM2].
constructor; try congruence.
- unfold ctx_ta_same in *. destruct C1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). destruct C2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
repeat split; congruence.
- intros c Hc. rewrite AC2 by exact Hc. apply AC1. exact Hc.
- intros i Hi. pose proof (B1 i Hi). pose proof (B2 i ltac:(lia)). lia.
- intros q. destruct (G1 q) as (?&?&?&?&?). destruct (G2 q) as (?&?&?&?&?). repeat split; congruence.
- intros q i Hi Hb. apply (BI1 q i Hi). apply (BI2 q i Hi). exact Hb.
- intros q Ha Hf. destruct (MR1 q Ha Hf) as [Ha1 Hf1]. exact (MR2 q Ha1 Hf1).
- intros b. rewrite GR2. apply GR1.
- intros b gh2 H2. destruct (GM2 b gh2 H2) as (gh1 & H1 & M1 & AI1). destruct (GM1 b gh1 H1) as (gh & H & M & AI).
exists gh. split; [exact H|]. split; [congruence|].
destruct AI1 as [Q1|[RR1 P1]]; destruct AI as [Q0|[R0 P0]]; [left; congruence| right; split; [lia| exact P0] | right | right; split; [lia| exact P0]].
split; [lia|]. intros g Hg E0. apply (P1 g); [congruence|]. destruct (G1 g) as (_ & _ & _ & SC1 & _). rewrite SC1. exact E0.
Qed.
End SE.
Lemma ta_rel_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "='9'N&O'=r3r2&Q2r1%23413%63541pT:81pSB:1pS@<1").
Proof. intros sc st v.
constructor; ta_auto.
intros c Hc. rewrite active_set_active. destruct (Z.eqb_spec c sc); [lia| reflexivity].
Qed.
Lemma ta_rel_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "R?'9'N&?'M&<&Dr3r2%3221r1%6221&Q7z%2214'6'1&3&Q;&Gr4%211%421>&H%114%721A%9241(4%=3<21r7r6%I221%=11%?21J%;13%A21L%C231%F3E1:p0:1p0I1pS4Q71'5r5%Q521G%I11%Q12Q01&Q8&Q9+2+Q0%3221%5271%;271%Q?2G;%O11%Q;2Q:1%:226%@221%Q71@%Q?2Q>1%>22:%D221%Q71D%QC2QB1%B22>%H221%I251p0:1p0@1'=&Q0%13MQCQ9%33Q;Q:1p051p0Q21p0R01pS<R81pS0R:1pSBR<1pS@R>1").
Proof. intros sc st g r.
intros GS BS RS. constructor; ta_auto.
- intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact GS| apply geom_same_refl].
- intros q i Hi. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; apply BS; exact Hi| auto].
- intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact RS| auto].
Qed.
Lemma ta_rel_put_links : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "H'9'N&?&O'=r5r4&Q0r3&Jr2&Ir1&D%1286%4231%7261%:391;%>3=<1pS6@1pS8A1pS0C1pSBE1pS@G1").
Proof. intros sc st g p n. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_next : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "D'9'N&?&O'=r4r3&Q0r2&Ir1&D%1264%4231%73618%;3:91pS6=1pS0?1pSBA1pS@C1").
Proof. intros sc st g n. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_prev : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "D'9'N&?&O'=r4r3&Q0r2&Jr1&D%1264%4231%73618%;3:91pS8=1pS0?1pSBA1pS@C1").
Proof. intros sc st g p. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_set_bounce : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "H'9'N'5&Q7zr1%3221&@r3r2%3221%8261%:261'=r5r4&Q3%13982%53431p071pT:D1pS4E1pSBE1pS@G1").
Proof. intros sc st i v.
intros Hv. constructor; ta_auto.
intros j Hj. rewrite bounces_set. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.
Lemma ta_rel_decay : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "F'9'N&Q7z&@r2&Q:r1+7%3221%6251%9281'=r4r3&B%12;2%53431p071pRNC1pSBC1pS@E1").
Proof. intros sc st c.
intros Hb. unfold decay_bounces. destruct (_ && _) eqn:E; [|apply ta_rel_refl].
apply andb_prop in E. destruct E as [_ E]. apply negb_true_iff in E. apply Z.eqb_neq in E.
apply ta_rel_set_bounce. lia.
Qed.
Lemma ta_rel_set_gai : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "R5'9'N&?'5&Q7z&Q6r1+O%3221%6251%7223%9221'F'6'2%113&QK'R0&QO'8&R2&R3%4432G1&QN&QL&QM%36762K51%:4J51?&R1%14L73Ar5&Q1r6%211%B6Q1F7541(0r2%22I1%I3G41&O&Cr3%211%82Q:7%O3521&7&K&Dr8%2218%411%Q63QD1Q?%711p091p0@1pS0QF1pS2Q<1'=&Q4r4%231CN%43MO1p061p0QD1pRJR11pRLR01pSBR21pS@R41").
Proof. intros sc st b ai.
intros Hai HSC. unfold set_group_active_idx. destruct (get_group st b) as [h|] eqn:Hb; [|apply ta_rel_refl].
unfold get_group in Hb.
constructor; ta_auto.
- intros b'. cbn [s_groups set_groups]. destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq. split; intros _; eauto.
+ rewrite lookup_insert_ne by congruence. split; intros X; exact X.
- intros b' gh1 H. cbn [s_groups set_groups] in H. destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in H. inversion H; subst. exists h. split; [exact Hb|]. cbn. split; [reflexivity| right; split; [exact Hai| intros g Hg; exact (HSC h g Hb Hg)]].
+ rewrite lookup_insert_ne in H by congruence. exists gh1. auto.
Qed.
Lemma tr_get_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "C'9'N'8'=r4r3r2%43321'6'Q5&E%1265%2286%53421p071pS>=1pSD?1pSB@1pS@B1").
Proof. intros sc st st1 rid. intros TR. unfold get_shadow. rewrite (tr_shadow _ _ _ TR). reflexivity. Qed.
Lemma tr_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "B'9'N&?'=r4r3r2%43321'6&A%1254%2275%43<21p061pS:<1pSD>1pSB?1pS@A1").
Proof. intros sc st st1 q. intros TR. unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity. Qed.
Lemma rec_set_gai : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "C&?'9'N'6'M&D&Q4r4r3r2%43321r1%7221%8242%;3:21pS:?1pSB>1pRJ@1pRLB1").
Proof. intros b ai st q. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
Lemma active_set_gai : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W0 "C&?'9'N'6&O&>&Q4r4r3r2%43321r1%7221%8242%;3:21pS4>1pSB>1pRJ@1pRLB1").
Proof. intros b ai st i. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
End CEIL_WRAP_2.
