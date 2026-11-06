(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_free_K () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_free_K.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_Bpres."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Bool.Bool."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.list_basics.list."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1bool"; "1fst"; "1list"; "1negb"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"]; ["3map"; "4N"; "4Z"; "0LB"; "0LB'"; "5PROT"; "5hdr_st"; "6blk_addr"; "6blk_slot"; "6block"; "7CINV"; "7ci_mptrs"; "7ci_slots"; "7hdr_known"; "7hosts"; "7is_gm"]; ["7slot_free"; "8KINV"; "8LPRE"; "8ZINV"; "8amc"; "9actives"; "9ctx_head_cells"; "9ctx_tail_cells"; "9meta_cells"; "9pw"; "9ticks_ok"; ":optr_in"; ";cell"; "<Known"; "<aptr"; "<aptr_eqb"]; ["<area"; "<cell_read"; "<cellval"; "<conc"; "<cptr"; "<ctx"; "<get_meta_rec"; "<get_shadow"; "<ghdr"; "<m_sizeclass"; "<mctx"; "<meta"; "<mstate"; "<optr"; "<r_base"; "<region"]; ["<s_areas"; "<s_ctx"; "<s_groups"; "<s_metas"; "<s_next_rid"; "<s_regions"; "<s_reserved"; "<s_shadow"; "<s_slots"; "<s_tick"; "<shadow"; "<wr8"; "=Is_true"; ">In"; "?add"; "?le"]; ["?lt"; "?modulo"; "?sub"; "0Zs"; "0b"; "0b'"; "0b1"; "0blk"; "0c"; "0f"; "0g"; "0i"; "0i1"; "0k"; "0o"; "0p"]; ["0pf"; "0q"; "0r"; "0rid"; "0rid'"; "0st"; "0st'"; "0st2"; "@delete"; "@filter"; "@lookup"; "Abv"; "BN_countable"; "BZ_countable"; "Bprod_countable"; "CIs_true_dec"]; ["Cprod_eq_dec"; "Dmap_delete"; "Egmap"; "Egmap_lookup"; "Egmap_partial_alter"; "Flist_filter"; "Geq_dec"; "Heq_dec"; "0v"; "0w"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma cell_read_wr8 st p v rid o :
ticks_ok st -> 0 <= v < 256 ->
cell_read (get_shadow (wr8 p v st) rid) o =
if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
- destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
- rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.
Lemma wr8_tables : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "R?'QL&Q>'B':';'SB'A&SF&S<'QO%544321&R5&R;r2r1r3%43321%611%713%?3921&S@&SG%24@?D1&S>&S=%26CBAG41'Q@%F4J521&R0%11=%21?%K3421'QH%L4Q0;81&R2%11C%21E%Q13421'8%12Q6Q5%Q34Q7B?1&R8%11J%21L%Q83421'4%82Q<Q<%211&R6%11Q1%21Q3%Q?3421'QJ&R1%11Q6%21Q8%QD3421&R9%11Q:%21Q<%QH3QF21'QK&QFr4%QD3QAQC1%321QC%423QD%QO3621pV4R31%R2291%R32>1%R42D1%R52L1%R62Q41%R72Q;1%R82QH1pWBR:1pV0R<1pV<R>1").
Proof. intros st p v. repeat split; reflexivity. Qed.
Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop :=
(exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b - IB <= o < snd b + 12)
\/ (exists b g i, hosts st b g /\ fst b = rid /\ 0 <= i <= m_last_idx (get_meta_rec st g) /\ o = sstart_of (get_meta_rec st g) i - IB)
\/ (exists blk, In blk LB /\ fst (blk_slot blk) = rid
/\ snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk)) - IB <= o < snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk))).
Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : forall rid o, PROT st LB rid o -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.
Lemma hosts_sh : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "<&Q>&=&NvS6r2r1%43321vS5%63143%8231pV4:1pU:;1").
Proof. intros b q. unfold hosts. rewrite EG. tauto. Qed.
Lemma is_gm_sh : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K ":&Q>&=&OvS6r1%3221vS5%5213%7231pV491").
Proof. intros q. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
Lemma conc_sh : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K ";&Q>';'B&QCvS6r1%3221vS5%5213%83731pV4:1").
Proof. intros q. unfold conc, get_region. rewrite ER. reflexivity. Qed.
Lemma hdr_known_sh : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "Q;'8'A'B%3221&Q>';&3r4%23761r1%53921':&R?+1%2215+3%4271%6231&EvS5vC&RB&9r7%23GF1r2%5221%9487D1p0;1pULK1&Mr6r5%34>21JvS6%541<43p031p081p0L1pV8Q61pUJQ61pU>Q51pV0Q71").
Proof. intros p b1 i1 rid.
intros <- HP (v3 & lo & hi & H3 & I3 & H2 & H1 & E). exists v3, lo, hi.
rewrite !SHP by (apply HP; lia). auto 10.
Qed.
Section SE.
Local Abbreviation SEC_T_KINV_shadow := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K ";'B'Q1vS5vCr1%43321vS6r2%73251p041pUB:1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_KINV_shadow) 0%nat 0%nat).
Lemma KINV_shadow : ltac:(sec_stmt2 constr:(SEC_T_KINV_shadow) 1%nat 0%nat).
Proof.
intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
{ intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
- unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
- intros ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
exists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
eapply hdr_known_sh; [reflexivity| | exact HK].
intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
constructor.
- apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
- apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
- apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
- intros b g HB. apply GMO. apply hosts_sh. exact HB.
- intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
- intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
- intros s g i Hs. rewrite ESL in Hs. rewrite EM. destruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
- intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
- intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
- intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
right; left. exists b, g, i. auto.
- apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
constructor; [| rewrite EG; exact NG| exact SZ].
exists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
+ rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
+ eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
- exact (ki_nodup _ _ _ K).
- pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
- intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
- intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
- exact TK'.
Qed.
End SE.
End KSH.
Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).
Lemma hdr_st_tables : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "RH'QL&Q>':';'SB'A&SF&S<'QO%544321&R5&Fr2r1%3221%511%614%>3821&S@'B&SG%34@?21&S>&S=%26CBA541'Q@%F4I521&R0%11>%21A%K3421'QH%L4O;81&R2%11D%21G%Q13421'8%12Q5C%Q34Q6B?1&R8%11K%21N%Q83421'4%82JJ%211&R6%11Q2%21Q5%Q?3421'QJ&R1%11Q7%21Q:%QD3421&R9%11Q;%21Q>%QH3QF21'QK&QFr3%QD21QC%321QC%423QD%QO3621pV4R21%R04R3Q?Q<8&R3%11QH%21QK%R53421&R4%11QL%21QO%R93R721%R;251%R<2;1%R=2D1%R>2I1%R?2O1%R@2Q71%RA2Q?1%RB2QF1%RC2R41pV2RE1pV<RG1").
Proof. intros st pf. repeat split; reflexivity. Qed.
Lemma ticks_ok_hdr_st : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "<'QL&Q>&Q:r2%211&Fr3%2214%611p051pV291pV<;1").
Proof. intros st pf. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.
Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
cell_read (get_shadow (hdr_st st pf) rid) o =
if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
then Known (if o =? snd pf - 3 then 255 else 0)
else cell_read (get_shadow st rid) o.
Proof.
intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
cbn [aadd fst snd].
destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.
Lemma hdr_st_cell_read_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "Q>'QL'8'A'B%3221&Q:r4%211'?&>';r3&3%13;:7%43<31%611&R@r2&RB&9%13BA>+3%4221%7261&R?%1258%B231%C2<1'QB&QA&QG&Fr6r5%3221%521M%721I%725O%921K%M3;31p0=1p0Q21pUNQ71pV8Q91pV2Q81pV<Q=1").
Proof. intros st pf rid o.
intros TK H. rewrite hdr_st_cell_read by exact TK.
destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
reflexivity.
Qed.
Lemma hdr_st_known_back : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "QM'QL'8'A'B%3221&Q:r5%211':&R?+1r1%3221+3%5231%7231'<';'QB&QA&QGr9&3r8%23FE1%5241&RB&9%13JI5r3%4221%<261(Q=%11F%A3@31qWDQ01%D2Q11p0F1pULQ31&Fr7r6%3221%G21Q5r4%J221%>1A%N3M21%L2K8%N218%Q13Q01AqWDQ@1%Q42QA1p061p0@1p0Q@1pWBQE1pUNQF1pV8QH1pV2QG1pV<QL1").
Proof. intros st pf rid o v.
intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
cbn [orb] in H. exists v; exact H.
Qed.
Lemma ZINV_hdr_st : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "A'QL&Q>'4%112&Q3r3r1%3221&Fr4%2215r2%8221p061pU8;1pV2>1pV<@1").
Proof. intros st pf Zs. apply ZINV_ext; reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_KINV_hdr_st := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "RN'QL'4&I%211'B&Q>'QO'Jr7r6%3221&R=r3%23;15'Q1r9%23187r1%73@13':r2r;%;3D21&>';&QD&H%117%21D%53421%711%<291p0>1pU<O1'A&3%132Q0L%;1L%334Q21%?3531'6%11Q3&S:'SB&SF&S<%34<21Q8&SC%14>43Q:r8%?3@Q>1&R5r<%211%<6DQ@8641(1%12QBQ?%Q13@31&R>&QN%11QD&9%13LQJQ?%5231&G%11@%Q:3QN31&RAr:%83Q3R11+@%4221z%QA3R521&Fr?%221QGr=%R0321Jp061p0>1p0H1p0Q;1p0QB1p0R41p0R81p0R<1pV6RA1pU@RF1pV2RD1pUBRF1pQ:RH1pQ8RI1pV<RM1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 1%nat 0%nat).
Variable LB' : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 2%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 3%nat 0%nat).
Variable pf : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 4%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 5%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_KINV_hdr_st) 6%nat 0%nat).
Lemma KINV_hdr_st : ltac:(sec_stmt2 constr:(SEC_T_KINV_hdr_st) 7%nat 0%nat).
Proof.
intros C Hin K HLB Hfst Hr Hpo PM.
pose proof (ci_ticks _ _ C) as TK.
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
destruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
pose proof (ki_gmetas _ _ _ K) as CG.
destruct HP as [HP|[HP|HP]].
- destruct HP as (b & gh & Hb & Fb & Ho).
specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
- destruct HP as (b & g & i & HB & Fb & Hi & ->).
pose proof (CG b g HB) as GO. destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
{ unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
- destruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
unfold IB in *. lia.
Qed.
End SE.
Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
In x (filter P l) <-> In x l /\ P x.
Proof.
rewrite <- list_elem_of_In, list_elem_of_filter.
pose proof (list_elem_of_In l x) as E. tauto.
Qed.
Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
List.NoDup l -> List.NoDup (filter P l).
Proof.
induction l as [|x l IH]; intros ND; [constructor|].
rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.
Lemma map_filter_slot : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "Q5&Q>'2p021'4&I%211';&QD%511&@&H&S9&SE%119&R<r3r1%711%311%511qU:@1&S?%114qWFC1%=6DC;418%@4EB?1%>1C%<1;%>11qWFM1%913qWFO1%G4LIF@%F6Q1I7421%L3J91pQ8N1pUDQ21").
Proof. intros f LB.
induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.
Lemma KINV_filter_slot : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "Q2'QL'4&I%211'B&Q>'2p021'Q1r4r3r2%43321r5&S9&SE%11>&R<&Hr1%211%;11%511qU:E1&S?%114qWFH1%=6IH;41B%D3?1Bp0A1pUDG1pUBK1pQ8M1pV<Q11").
Proof. intros st LB c f.
intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
- apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
exact (proj1 (List.Forall_forall _ _) BL blk Hin).
- rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.
Lemma LPRE_intro : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "S9'QL'4&I%211'B&Q>&Lr7%211&Nr8r4r5%43321';'6'8%12<=%311&S:&QD'SB&S@'A&SF&SG%4432F1&S>&S<&S=%36762J51%:4J51>&SC%14L73@&Hr3%211&R8r9%211%E6DG9741(1(7r6%24Q7Q81Q1%42L1%Q03L61&>&Q0&QFr:%221Q<%421Q8%611'QH%Q811%Q34QCNJ2%I4QDOK3%H1Q>&R2r;%211%Q;6Q:86541(0%11:%QC3:31&R?&QIr<%D21O%311%52E1'Q2r=&S9&SE%11R:&R<&5&Q?r1%Q?11%Q@1R8%4221%611%811qU:RD1&S?%114qWFRG1%@6RHRG>41F%C6B1OQ9QERAp0E1p0L1p0Q91p0QA1p0RC1p0RI1pU@S01pUHRO1pV0RO1pUFS01pUBS21pQ8S41pV<S81").
Proof. intros st LB c g p i blk.
intros CS HB SL NF NG HC. destruct (CS _ _ _ SL) as (GM & E & I).
constructor; auto.
- rewrite <- E. exact NG.
- apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.
Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.
Lemma drop_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "D';'SB'A&SF&S<'QO%544321&R5vS6%211&S8&SA&SD%14;:98%34<981vS3vS5%:11%85@<431%C3=:1"). Proof. reflexivity. Qed.
Lemma drop_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "D';'SB'A&SF&S<'R:%544321&R7vS6%211&S8&SA&SD%14;:98%34<981vS3vS5%:11%85@<431%C3=:1"). Proof. reflexivity. Qed.
Lemma conc_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "E'8'A'B%3221&>';&3r1%23761vS3%53921%711&QCvS6r2%3221vS5%5213%=3@31p081pV4A1").
Proof. intros q. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma pw_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "G&QM&Q;'A&>';r1vS3%33521%511qWF71%9215'S;yR0%211&Q9vS6r2%3221vS5%5213%@3731p0;1pV0F1").
Proof. intros p. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite conc_drop by exact H. reflexivity. Qed.
Lemma get_shadow_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "A'A&>';r1vS3%33521%511'R:&QGvS6r2%3221vS5%5213%<3731p091pV:@1").
Proof. intros rid'. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rec_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K ";&Q>';'QK&QFvS6r1%3221vS5%5213%83731pV4:1"). Proof. intros q. reflexivity. Qed.
Lemma meta_cells_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "?&Q>';'4'Q<%211&Q8vS6&QFvS5r1%3221%6251%7242%<3921pV4>1").
Proof. intros q.
destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !pw_drop by assumption. reflexivity.
Qed.
Lemma ctx_head_cells_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K ":';'4'Q<%211&Q6vS6%211vS5%411%93631").
Proof.
destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !pw_drop by assumption. reflexivity.
Qed.
Lemma actives_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "<';'4'S;yR0%211%411&Q5vS6%211vS5%411%;3631").
Proof.
destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply pw_drop. apply PA.
Qed.
Lemma ctx_tail_cells_drop : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K ":';'4'Q<%211&Q7vS6%211vS5%411%93631").
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (conc_drop (brid, boff)) by exact PB. reflexivity.
Qed.
End DROP.
Lemma ci_mptrs_frame : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free_K "QH'QL&Kr2%211';'8&QM%2211%3212%4213'B%6221%7212%8213%9214%:215&Q4&QE%11@%311r3%411%611%C3841'SB&Q>&S@'A&SF&SG%4432D1&S>&S<&S=%36762H51'Q@%<4;621&R0%11Br4%311%Q53531'QO%C4@?;1&R5%116r5%311%Q<3531%Q@13p021p0:1p0M1p0QB1pV@QF1pV<QG1").
Proof. intros st st2.
intros (M1 & M2 & M3 & M4 & M5) EC EA ER.
assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
unfold amc in EC. inversion EC.
unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.
End CEIL_WRAP_1.
