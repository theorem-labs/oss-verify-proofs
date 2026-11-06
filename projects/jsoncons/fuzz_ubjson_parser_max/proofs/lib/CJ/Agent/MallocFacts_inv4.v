(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Read MI_WFree
MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WNtf2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_Cnt MI_WTry2 MI_WGroup MI_TF2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WMalloc MI_Sim MI_Contracts MI_Fuel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_B MallocFacts_AM MallocNat MallocFacts_AS
MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocFacts_inv4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_AM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_AS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_inv4.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocNat."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WSlot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WSlot2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["0BL"; "1None"; "1Some"; "1cons"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "3N"; "3Z"; "0L"]; ["0L3"; "0LB"; "0LS"; "0LS3"; "0RUNp"; "4AREACH_from"; "4block"; "5MFACTS_g"; "6AMpre_g"; "6fresh_above"; "7IST"; "7ISTF_g"; "7LFACTS"; "7fact_bit_stride"; "7fact_freelist"; "7fact_ghdr_unk"]; ["7fact_host_stride"; "7fact_links"; "7fact_lists"; "7fact_mw"; "7fact_sc0_full"; "7lmem"; "7req_ok"; "7ta_fail"; "8hosts"; "9CORR"; ":JINV"; ":JINVi"; ";bS"; ";kS"; "<leaf_of"; "<mem"]; ["=secret_val"; ">ld_resv"; ">mled"; "?INVL"; "?MR"; "?blk"; "?extras"; "?frontier"; "?live_group"; "@GP"; "@X_as"; "ASLOT_POST"; "BLActive"; "Bactive"; "Balloc_meta"; "Balloc_slot"]; ["Baptr"; "Bfull_lay"; "Blhead"; "Bm_mem"; "Bm_next"; "Bm_sizeclass"; "Bmstate"; "Boptr"; "Bregion"; "Bs_regions"; "Bs_secret"; "Bs_tick"; "Bset_tick"; "Bstrip"; "CIn"; "Dlt"]; ["Ele"; "Elt"; "0X"; "0b"; "0f"; "0g"; "0h"; "0idle"; "0idx"; "0m"; "0o"; "0r"; "0req"; "0resv"; "0rid"; "0sc"]; ["0st"; "0st'"; "0st0"; "0st1"; "0st2"; "0st3"; "Flookup"; "GN_countable"; "Hgmap"; "Hgmap_lookup"; "Ieq_dec"; "0t"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section GF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Lemma lmem_listed : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "E&R0'R2&R>r2vBr1%211%53741&QHvS0r3%3221&Q5&R=%115r4%4221p061p0;1pU>B1pUDD1").
Proof. intros m h.
intros Hin [b Hb]. unfold lmem. rewrite !get_meta_rec_strip. fold (MR st m).
split; [rewrite (hosts_mem _ _ _ IM _ _ Hb); discriminate|].
split; [exact (listed_next _ _ _ _ _ INV m h Hin)|].
destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) h m Hin) as (y & _ & E & _). rewrite E. discriminate.
Qed.
Lemma mem_live : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "C&R0':&R7&R3&QDvS0r2%3221%511(2r1%22;1%;3:41&Q8r3%23:91p041pU8A1pU<B1").
Proof. intros g b. intros H. exact (mem_hosts X st L BL LS INV ZB g b H). Qed.
Lemma linked_group_listed : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "Q4&R0':&R7&R3&QDvS0r2%3221%511(2r1%22;1%;3:41&<&R4r3%<2;1%311(1%11C%C3B31%811&R>r4vB(QL&R5%G2F4%211%411%611%93O81p0;1p0E1pU8Q21pU<Q31").
Proof. intros g b.
intros Hb Hn. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
destruct h as [sc|].
- destruct (il_active _ _ IL sc g Hh) as (_ & _ & <-). exact Hh.
- exfalso. apply (free_not_live _ _ _ _ _ INV g Hh). exists b. exact (mem_live _ _ Hb).
Qed.
Lemma l_lists : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&Q2&R=vS0%211%411").
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
Lemma l_freelist : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&N&R=vS0%211%411").
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
Lemma l_mw : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&Q3&R=vS0%211%411").
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
Lemma l_host_stride : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&Q0&R=vS0%211%411").
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
Lemma l_links : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&Q1&R=vS0%211%411").
Proof.
intros g Hg. unfold lmem in Hg. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. destruct Hg as (Hm & Hn & Hp).
destruct (c_links X st L BL LS INV) as [CN CP _ _].
split.
- intros n E. rewrite get_meta_rec_strip. exact (proj1 (CN g n E)).
- intros p E. rewrite get_meta_rec_strip. exact (proj1 (CP g p E)).
Qed.
Lemma l_sc0_full : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&Q4&R=vS0%211%411").
Proof.
intros g b gh Hb Hgh Hsc. rewrite s_groups_strip in Hgh. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
pose proof (mem_live _ _ Hb) as Hh. destruct (hosts_ok _ _ _ IG _ _ Hh) as (ai & Hg & GO).
rewrite Hg in Hgh. inversion Hgh; subst gh. cbn. exact (g_full0 _ _ _ _ _ _ GO Hsc).
Qed.
Lemma l_bit_stride : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5&M&R=vS0%211%411").
Proof.
intros g b i Hb Hi Hbits Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| exact GE].
exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 F0].
rewrite A0, F0, !Z.bits_0 in Hbits. discriminate Hbits.
Qed.
Lemma inv_lfacts : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5'L&R=vS0%211%411").
Proof. constructor; [exact l_lists| exact l_freelist| exact l_mw| exact l_host_stride| exact l_links| exact l_sc0_full| exact l_bit_stride]. Qed.
Lemma inv_ghdr_unk : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "3&OvS0%211").
Proof.
intros b gh o Hb Ho. destruct (hdr_hosts X st L BL LS INV b gh Hb) as [m Hm].
exact (ish_ghdr _ _ ISH b m o Hm ltac:(lia)).
Qed.
Variable resv : list (Z * Z).
Variable LB : list block.
Hypothesis CR : CORR st LB BL.
Hypothesis RESV : ld_resv L = resv.
Local Ltac inst f :=
first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV ZB) | exact (f _ _ _ _ _ INV ZB NFR)
| exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV ZB _ CR) | exact (f _ _ _ _ _ INV ZB NFR _ CR) ].
Lemma inv_mfacts : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5'GvRMvS0vA%43321").
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
Lemma inv_istf : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5'KvRMvS0vA%43321").
Proof. constructor; [exact inv_mfacts| exact inv_lfacts| exact inv_ghdr_unk]. Qed.
Lemma frontier_fresh : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "Q3'='R8'>':'6%114&S6'S8&S:&S7%34:219&S9%14<43;r3&R9vS0%211%;6A@7541(2r2%22C1%B3@41&R@&QGr4%23:1<%4217&Ir5%23>1@p041p0:1pUFN1pUHQ01pUNQ21").
Proof. intros rid r o.
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
Hypothesis SEC : s_secret st = secret_val.
Lemma inv_ampre : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "5'HvDvRMvS0%43321").
Proof.
pose proof (ia_secret _ IA) as [S0 SD]. pose proof (ia_avail _ IA) as [AC AV]. pose proof (ir_cursor _ _ _ IR) as (C1 & C2 & C3).
assert (RB : forall rid r, s_regions st !! rid = Some r -> 0 < r_len r < 2 ^ 47).
{ intros rid r Hr. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & L0 & _ & CE & _). pose proof (round_up_ge (r_len r)). pose_ceil. lia. }
constructor.
- unfold ctx. destruct SD as [(_ & E & _)|[_ E]]; rewrite E; lia.
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
Lemma CORR_GP : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "Q5'QF'R6'QB'4&QE%211'R2&R0%511p031&F%811&QCvDr7r6r4r3r2%76654321&QI%1276&Q9r8r5%33281%433:;p021p071p0:1pQ4C1pQ6F1p2K1pQ0O1pV4Q11pV2Q21pU6Q41").
Proof. intros X st st' L BL LS LB.
intros INV [GPR _] CR. eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3).
split; [exact C1|]. split; [exact C2|]. rewrite C3. rewrite (conc_same st st' (bslot k)); [reflexivity|].
destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.
Definition JINVi (resv : list (Z * Z)) (idle : list aptr) (st : mstate) (LB : list block) : Prop :=
exists L LS BL, INVL (X_as idle) st L BL LS /\ NoDup idle /\ TF0 st /\ ld_resv L = resv /\ s_secret st = secret_val /\ CORR st LB BL.
Definition JINV (resv : list (Z * Z)) (st : mstate) (LB : list block) : Prop := exists idle, JINVi resv idle st LB.
Lemma jinv_top : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "O'4'8'>%2211%411'R6&F%711'='EvDr4r3r2%544321&R?&R;%116%3215&Q:r6&R<r5%22;1%5341=p071p0<1pVHC1pQ4E1pV6H1pULJ1").
Proof. intros resv st0 LB t.
intros AR Ht. destruct (areach_inv resv st0 LB AR) as (L & LS & BL & INV & _ & RESV & SEC & CR).
exists [], L, LS, BL. split; [apply INVL_set_tick; [lia| exact INV]|].
split; [apply NoDup_nil; exact I|| constructor|]. split; [apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| exact Ht]|].
split; [exact RESV|]. split; [exact SEC|]. exact CR.
Qed.
Section SE.
Local Abbreviation SEC_T_jinv_ta := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "Q>'4'8'>%2211%411&R0%611'R6&F%911&Q;r6r5r4r3%544321'9&R@z%2215&RA+Q@%2281%7241&Q7%13<>;r9r8%B421?A':&R7&QM%12CD(1%11M%63531%D281p0<1p0?1p0H1pV8Q11pV0Q71pQ4Q11pV2Q41pU@Q61pULQ91")) (only parsing).
Variable resv : ltac:(sec_ty2 constr:(SEC_T_jinv_ta) 0%nat 0%nat).
Variable idle : ltac:(sec_ty2 constr:(SEC_T_jinv_ta) 1%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_jinv_ta) 2%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_jinv_ta) 3%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_jinv_ta) 4%nat 0%nat).
Variable st1 : ltac:(sec_ty2 constr:(SEC_T_jinv_ta) 5%nat 0%nat).
Lemma jinv_ta : ltac:(sec_stmt2 constr:(SEC_T_jinv_ta) 6%nat 0%nat).
Proof.
intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc TA.
destruct (try_avail_ok (option (mstate * Z)) (X_as idle) L BL sc kS bS eq_refl eq_refl Hsc st LS INV) as (st1' & first & LS1 & E & TAF & RES).
unfold ta_fail in TA. rewrite E in TA. unfold kS in TA. inversion TA. subst st1' first.
destruct RES as [(_ & HA & INV1)|(g & bg & ai & idx & NZ & _)]; [| exfalso; exact (NZ eq_refl)].
split; [| exact HA]. exists L, LS1, BL. split; [exact INV1|]. split; [exact ND|].
split; [exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF)|]. split; [exact RESV|].
split; [rewrite (taf_ssec _ _ _ TAF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_taf _ _ _ TAF) CR).
Qed.
End SE.
Lemma jinv_am : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "QE'4'8'>%2211%411&R0%611'R6&F%911&Q?&Q;r7r6r5r4%544321&Q>'6&R7%C2=1%311&QNvD&Q=%12B6&Q<%117%6557?31(2%<1I%N2H1(7r3r2%62N1%44M631%8261%E4AG:1r9(3r8%23Q591%Q0441LNp061p0M1pUDQ91pV:Q81pUFQ61pQ4Q81pV8Q;1pU@Q=1pULQ@1").
Proof. intros resv idle st1 LB o st2 m.
intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) (ans & o' & FL).
set (Post := fun (L' : mled) (r : option (mstate * optr)) =>
match r with
| Some (s2, Some m') => exists LS', INVL (X_as (m' :: idle)) s2 L' BL LS' /\ ~ In m' idle /\ AM_frame st1 s2 /\ L_frame L L'
| _ => True
end).
assert (FT : ftree L (alloc_meta st1 kS bS) Post).
{ apply (alloc_meta_ft _ BL Post kS bS (X_as idle) st1 L) with (LS := LS); [| | exact INV| apply amf_refl| apply lf_refl].
- intros s1 L1 LS1 _ _ _. exact I.
- intros s1 L1 LS1 m' INV1 NI AF LF. cbn. exists LS1. split; [exact INV1|]. split; [exact NI|]. split; [exact AF| exact LF]. }
pose proof (ftree_prun pans_mem pupd_mem pans_mem_range (alloc_meta st1 kS bS) L Post o FT) as PT.
unfold mrun in FL. destruct (ptree_follow _ L _ ans PT FL) as (L' & CP & POST). cbn in POST.
destruct POST as (LS' & INV2 & NI & AF & LF).
exists L', LS', BL. split; [exact INV2|].
split; [apply NoDup_cons; split; [intros Hin; apply NI; apply list_elem_of_In; exact Hin| exact ND]|].
split; [exact (TF0_ctrl st1 st2 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF)|].
split; [rewrite (lf_resv _ _ LF); exact RESV|].
split; [rewrite (amf_ssec _ _ AF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_amf _ _ AF) CR).
Qed.
Lemma ist_jinv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "I'4'8'>%2211%411'R6&F%711'EvDr4r3r2%544321'J%13653&Q:r6%23178p041p071pV2@1pQ4?1pV6B1pULD1").
Proof. intros resv st0 LB st.
intros AR. induction 1 as [t Ht|o st sc st1 st2 m _ IH Hsc TA AM].
- exact (jinv_top resv st0 LB t AR Ht).
- destruct IH as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. exists (m :: idle). exact (jinv_am _ _ _ _ _ _ _ J1 AM).
Qed.
Lemma jinv_slot : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv4 "S='4'8'>%2211%411&R0%611'R6&F%911&Q?'5&Q;r:r9r8r7%544321'9&R@zr5%3221&RA+Q@%2241%8241&Q6r6%2218&Q>'6%O2IN%211&QOvD&R1r;&Q=%12Q0Q5&Q<%119%89796K5J>31(2(7r4%24Q7Q<I1%42?1%B4?Q261';'QB'R2p01Q>&QE%QF11&QC&QJrB%211rAr3%66J32Q81@&QKr=r<r2r1%5;Q0:438Q>7NQF21':&QA%115rC%43R421&R:%11Q5&Q@%11Q9%93R;31&Q9r@%23Q;1D%QO241%R02:1%R12@1%R22G1qQ8Q11%Q52Q21qQ2Q51%Q72Q61q2Q31%Q92Q41qQ6Q71%Q;2Q81qQ0Q;1%Q=2Q<1p0Q?1p0R31p0R71p0RA1pUBS11pV<RM1pUJS31pV0S41pU:RL1pUFRN1pQ4S01pV2S31pU@S51pULS81").
Proof. intros resv idle st LB o f sc req st3 idx.
intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc [Hreq Hfit] (ans & o' & FL).
unfold mrun in FL. apply (@alloc_slot_follow_mono _ _ pans_mem pupd_mem full_lay f (f + 49)) in FL; [| lia].
set (Post := fun (L' : mled) (r : option (mstate * Z)) =>
match r with Some (s3, i) => exists LS3, SLOT_POST idle sc req st L BL s3 i L' LS3 | None => True end).
assert (FT : ftree L (alloc_slot full_lay (f + 49) st sc req kS bS) Post).
{ apply (alloc_slot_ft _ Post (f + 49)%nat sc idle st L BL LS req kS bS ltac:(lia) INV TF ND Hsc Hreq Hfit).
intros st1 i L1 LS1 SP. cbn. exists LS1. exact SP. }
pose proof (ftree_prun pans_mem pupd_mem pans_mem_range _ L Post o FT) as PT.
destruct (ptree_follow _ L _ ans PT FL) as (L3 & CP & POST). cbn in POST. destruct POST as [LS3 SP].
exists L, LS, BL, L3, LS3. split; [exact INV|]. split; [exact SP|].
split; [rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
destruct SP as (_ & _ & GP3 & _). split; [rewrite (proj2 GP3); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV GP3 CR).
Qed.
Theorem ist_facts_proof : forall {resv} st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB.
Proof.
intros resv st0 LB st AR H. destruct (ist_jinv resv st0 LB st AR H) as (idle & L & LS & BL & INV & ND & TF & RESV & SEC & CR).
exact (inv_istf (X_as idle) st L BL LS INV eq_refl eq_refl resv LB CR RESV).
Qed.
Theorem istr_facts_proof : forall {resv} st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB.
Proof.
intros resv st0 LB st3 AR (o & st & f & sc & req & idx & H & Hsc & RQ & LF).
destruct (ist_jinv resv st0 LB st AR H) as [idle J].
destruct (jinv_slot resv idle st LB o f sc req st3 idx J Hsc RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & RESV & SEC & CR).
destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
- exact (inv_istf (X_as idle) st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
- exact (inv_istf _ st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
Qed.
Theorem nest_facts_proof : forall {resv} st0 LB st sc st1 o st2 m f j req o' st3 idx,
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
Theorem areach_ampre_proof : forall {resv} st LB, AREACH_from resv st LB -> @AMpre_g _ resv st.
Proof.
intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & RESV & SEC & _).
exact (inv_ampre x0 st L BL LS INV eq_refl resv RESV SEC).
Qed.
Theorem ist_ampre_proof : forall {resv}, AMP_AS_g resv (am_pre_g resv).
Proof.
intros resv st0 LB st sc st1 AR H Hsc TA.
destruct (ist_jinv resv st0 LB st AR H) as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [(L & LS & BL & INV & _ & _ & RESV & SEC & _) _].
exact (inv_ampre (X_as idle) st1 L BL LS INV eq_refl resv RESV SEC).
Qed.
Local Definition g1 := (@ist_facts_proof : forall resv st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB).
Local Definition g2 := (@istr_facts_proof : forall resv st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB).
Local Definition g3 := (@nest_facts_proof : forall resv st0 LB st sc st1 o st2 m f j req o' st3 idx,
AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
0 <= j < 48 -> req_ok j req ->
leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
nest_ok m st3).
Local Definition g4 := (@areach_ampre_proof : forall resv st LB, AREACH_from resv st LB -> @AMpre_g _ resv st).
Local Definition g5 := (@ist_ampre_proof : forall resv, AMP_AS_g resv (am_pre_g resv)).
End CEIL_WRAP_1.
