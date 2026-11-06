(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA As0Tables
ArtMem JatInitCache JatPopulate1 ArtRuns ArtRunsMem JatCls JatFp JatClsRep JatClsGfa2 JatClsRefill JatCellEx JatCARSpec JatAlloc3Pure JatDepot ArtBridge JatAllocate3
JatInv JatInvMallocPure JatInvMallocFp JatInvMalloc JatLift JatWrapPure JatWrapKit JatWrapMallocX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapMallocC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInvMalloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "1None"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2not"; "2or"; "3Z"; "0FF"; "0FPL"; "0L"; "0LB"; "0LK"; "4page_base"; "0M"; "0M1"; "5apart"; "6AMmapFixedNR"; "6AMmapNull"; "6aev"]; ["7page_allowedb"; "8blocks_apart"; "8defined"; "9FS_BYTES"; "9S"; "9ablock_range"; "9aheap_pres"; "9ar_fs"; "9ff_addr"; "9ff_bytes"; "9ff_class"; "9fframe"; "9fframes_apart"; "9in_shadow_of"; "9shadow_blk"; ":art_ca_events"]; [":art_ca_pre"; ";art_cls"; ";art_cls_mfa'"; ";art_cls_needs_populate"; ";art_cls_new"; ";cl_cache"; ";cl_free"; ";cl_mfa"; "<art_gap"; "<art_out"; "=art_client_ok"; "=art_run"; "=art_run_ok"; "=rn_HI"; "=rn_ar"; "=rn_qs"]; ["=rn_spb"; ">art_mrep_W"; "?mem_grows"; "0Sp"; "@In"; "@incl"; "Aadd"; "Ale"; "Alt"; "Amodulo"; "Amul"; "Aof_nat"; "Apow"; "Asub"; "0a"; "0b"]; ["0c"; "0cl"; "0f"; "0k"; "0l"; "0len"; "0lo"; "0n"; "0r"; "0rn"; "0spb"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0u"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_ca_events_no_null : ltac2:(TCodec.tc2 tcn__JatWrapMallocC "E'C'QA&A&R4'O(Nr2r1%3221&Q?r5r4r3%43321%;3:61%=11pUB@1pU<A1pU4A1pU2C1pUFD1").
Proof.
intros spb c cl len r H. unfold art_ca_events, art_refill_events in H. destruct (cl_cache cl); [|exact H]. destruct (art_cls_needs_populate c cl); [|exact H].
destruct H as [H|H]; [discriminate H|]. match type of H with In _ (if ?b then _ else _) => destruct b end; [exact H|]. destruct H as [H|[]]. discriminate H.
Qed.
Lemma art_ca_events_no_nr : ltac2:(TCodec.tc2 tcn__JatWrapMallocC "E'C'QA&A&R4'O(Mr2r1%3221&Q?r5r4r3%43321%;3:61%=11pU:@1pTNA1pU4A1pU2C1pUFD1").
Proof.
intros spb c cl a l H. unfold art_ca_events, art_refill_events in H. destruct (cl_cache cl); [|exact H]. destruct (art_cls_needs_populate c cl); [|exact H].
destruct H as [H|H]; [discriminate H|]. match type of H with In _ (if ?b then _ else _) => destruct b end; [exact H|]. destruct H as [H|[]]. discriminate H.
Qed.
Lemma art_ca_pre_mfa_pop : ltac2:(TCodec.tc2 tcn__JatWrapMallocC "Q8'C'QA'@'8%114&QEr1%211(9%119%83631'4&QCr3r2%3221(>%?3621&QG&Q@r4%2218%411&QB&R6&R;&7&QF%11?%32M1%511&QD%12<C%9231%;2E1%Q13Q3=1p0C1p0K1pU4Q51pU2Q71").
Proof. intros c cl E NP. unfold art_ca_pre. rewrite E. rewrite art_cls_refill_eq. unfold art_cls_pre_take. rewrite NP. reflexivity. Qed.
Section ExitMem.
Variable FSG : Type.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_wmc_mem := (forall rn (G : art_gs FSG) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (log' : list aev)
(Sp n rz qz rs qr km : Z) (cl' : art_cls), let c := AsanTab.class_id (rs + rz) in
let cl := g_cls FSG G c in
let w := art_ca_cptr c cl in
let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
let FPL := art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) in
art_run_ok rn -> 1 <= c <= 30 -> art_cls_ok c cl -> cl_mu cl = 262144 * km -> rz = 16 * qz -> rs = 8 * qr ->
(cl_cache cl = [] -> art_cls_needs_populate c cl = true -> cl_mu cl + 262144 <= 3758096384
/\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
cl' = art_cls_pop (art_ca_pre c cl) ->
log' = g_log FSG G ++ art_ca_events (rn_spb rn) c cl ->
bhist A M model (g_log FSG G) log' A' M1 model' ->
mem_grows (mrestrict (bhid A model) M) (mrestrict (bhid A' model') M1) ->
(forall x : word, ~ FPL (U x) -> mrestrict (bhid A' model') M1 x = mrestrict (bhid A model) M x) ->
wrA (mrestrict (bhid A' model') M1) (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ->
wrA (mrestrict (bhid A' model') M1) (rn_spb rn + c * 2 ^ 32 + 3758096384) (cl_mfa cl') ->
(forall x : word, ~ FPL (U x) -> M1 x = M x)
/\ mem_grows M M1
/\ (forall x : word, (rn_spb rn + c * 2 ^ 32 <= U x < rn_spb rn + c * 2 ^ 32 + cl_mu cl'
\/ rn_spb rn + c * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + c * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false)) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 2%nat 0%nat).
Variable A' : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 4%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 6%nat 0%nat).
Variable model' : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 7%nat 0%nat).
Variable log' : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 8%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 10%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 11%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 12%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 13%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 14%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 15%nat 0%nat).
Variable cl' : ltac:(sec_ty2 constr:(SEC_T_art_wmc_mem) 16%nat 0%nat).
Lemma art_wmc_mem : ltac:(sec_stmt2 constr:(SEC_T_art_wmc_mem) 17%nat 0%nat).
Proof using fx rn G A A' M M1 model model' log' Sp n rz qz rs qr km cl'.
intros c cl w ab FPL ROK Hc OK Emu Erz16 Ers Room Ecl' Elog BH GR FR Wu Wfa.
pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & _).
assert (OKp : art_cls_ok c (art_ca_pre c cl)) by (apply art_cls_ok_ca_pre; assumption).
pose proof OKp as (_ & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (Hmfa0' & Hmfa1') & _).
assert (Emu' : cl_mu cl' = cl_mu (art_ca_pre c cl)) by (rewrite Ecl'; reflexivity).
assert (Emfa' : cl_mfa cl' = cl_mfa (art_ca_pre c cl)) by (rewrite Ecl'; reflexivity).
assert (VIS : forall x : word, (rn_spb rn + c * 2 ^ 32 <= U x < rn_spb rn + c * 2 ^ 32 + cl_mu cl'
\/ rn_spb rn + c * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + c * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false).
{ intros x [Hx|Hx].
- apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(rewrite Emu'; lia) ltac:(right; lia) Wu x Hx).
- apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + c * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(rewrite Emfa'; lia) ltac:(right; lia) Wfa x Hx). }
assert (EVR : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z ->
art_malloc_fp Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) z).
{ intros sfx El z Hz. rewrite Elog in El. apply app_inv_head in El. subst sfx.
apply (art_ca_events_in_fp Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) cl z Hc OK Emu); [|exact Hz].
intros E1 E2. exact (proj2 (Room E1 E2)). }
assert (EVL : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z -> FPL z).
{ intros sfx El z Hz. apply (art_malloc_fp_cases Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) w qz qr z Espb Eris eq_refl Erz16 Ers).
exact (EVR sfx El z Hz). }
split; [|split; [|exact VIS]].
- exact (art_lift_frame A A' M M1 model model' (g_log FSG G) log' BH FPL FR EVL).
- apply (art_lift_grows A A' M M1 model model' (g_log FSG G) log' BH GR). intros sfx El x Hz Hv.
rewrite Elog in El. apply app_inv_head in El. subst sfx. destruct Hz as (ev & Hev & Hz).
unfold art_ca_events, art_refill_events in Hev. destruct (cl_cache cl) eqn:Ec; [|destruct Hev]. destruct (art_cls_needs_populate c cl) eqn:NP; [|destruct Hev].
destruct (Room eq_refl eq_refl) as (R1 & R2).
pose proof (art_ca_pre_mu_pop c cl Ec NP) as Emp. pose proof (art_ca_pre_mfa_pop c cl Ec NP) as Emf.
assert (D : forall a k, 0 <= a -> a + k < 2 ^ 64 -> 0x691000 <= a -> wrA (mrestrict (bhid A' model') M1) a k -> a <= U x < a + k -> mrestrict (bhid A' model') M1 x <> None).
{ intros a k Ha Hk Hoff Wr Hx. pose proof (art_wr_wview ASEGS _ a k Ha Hk Wr x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
destruct Hev as [<-|Hev].
+ cbn [art_ev_range fst snd] in Hz. apply (D (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(rewrite Emu'; lia) ltac:(lia) Wu). rewrite Emu', Emp. lia.
+ match type of Hev with In _ (if ?b then _ else _) => destruct b end; [destruct Hev|]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz.
apply (D (rn_spb rn + c * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(rewrite Emfa'; lia) ltac:(lia) Wfa). rewrite Emfa', Emf. lia.
Qed.
End SE.
End ExitMem.
Section ExitClient.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x691000.
Hypothesis HLst : forall a, 0x20cbc8 <= a < 0x65cbe8 -> hl_rt_static L a.
Section SE.
Local Abbreviation SEC_T_art_wmc_client := (ltac2:(TCodec.tc2 tcn__JatWrapMallocC "YL'QK'8'<'C%2211%411&Q;%611'RLyR0%211':y8%511%311p051!p0>1&QLr<%211&QJr=r;r:r9r7%66584321&R5%13I54&R2r8%2271&A&RMr1%22K1%<11%511'@r2%B11%G12%43M21p061pV0Q31&Q1r6r@%33G21&R4rC%23Q@<1'B'?&R7&6r3%23QGQG1%421C&R8&R6&=%13QLQL6%3261%52I1%<271&Q=%13:5L%@231r>%11>%Q711p041p0F1pTNR81pU0R81z%G21Q;&R<+2+R0%3221%G2Q@1%N261&QI&R1rE%211%421QAp01Bp071pTNRI1&QM%117%Q821QL&R=+TP0%22R<1%Q<21QK%Q82QLR>%Q?221%R511r?%11Q?%R811p041p0<1pTNS91+RPP0%QG21R;+VbTP0%QD2R=1%QK231+RQbn8%QL21R;+V[bo8%QI2R=1%R0231%RF11%R81QO%RH11p031p0:1pTNSI1&Q7&QNrH%211%411%R;21RJ%R62R:RKrI%711%911&Q3%R;221%RB261&QHrJ%QF11r4%4321REp061p0>1pU8T>1pTNT?1%RL2R6RJ%RH2R7RKr5%RI219+Q?%R92R81%S2231&L&R0rM%211+Q5%R@2R?1%S321QO%74SB<41&Q4%11T9%S=21?%S82T;SF+1%R7221%611%SB2D1%SD261rO%RF11%Q331SN7p041p0>1p0G1p0M1p0O1pTNU@1pU<UA1pU>UB1&3rGrF%33UC21%T83UDTG1%QM1Q@%QO11&Q8%11TF%T8231&Q9&Q:%11TJ%311%T7261%T829QN%T?221%T;2SJ4%TB221%TC2:1p0@1pU6V51rA%S=21S<%TG21U;%TC2U<3%TJ221&RK%12V9U:%SL11(2%11V8%U?3V831%UF11p081pTNVF1%QO1R?+Q0%T=2T<1%U0231+@%U2221%U921U@%U42EUArK%R811%U721R5%U>241&R9rB%221:%V23W61TL%U>2TM3&Q2rD%23QF1UJ&Q>%13S@TH3+QoooPP0&R:+XP0&QOrQ1%211%5241%UJ271%V121VD+Q2%U;2U:1%UN241%V02VH1%V7251'4&Q0&I%11VI%32S61(>%VM3621p081pV0WL1(5(;%14X6X6RBRArQ0%43X721rNrL%WI6J3S321T3&Q5vF%TC1M%3421RKRJ&Q<%RN3X>S98%23RNRM1&Q6%1876=S<THUFQET<%W2231%W3271%W42<1p0E1p0Q=1p0Q@1p0QD1p0QF1p0QK1p0R11p0R91p0RH1p0S?1p0TC1p0U:1p0UK1p0V<1p0VM1p0WI1p0WN1p0X<1p0X@1p0XC1p0XK1pU@Y=1pUNY>1pT8Y?1pQ<Y21pQHY51pQFY61p4YA1p2YB1pQBYA1pQ:YB1pQ@YE1pUDYK1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 4%nat 0%nat).
Variable A' : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 5%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 6%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 7%nat 0%nat).
Variable FPL : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 8%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 9%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wmc_client) 11%nat 0%nat).
Lemma art_wmc_client : ltac:(sec_stmt2 constr:(SEC_T_art_wmc_client) 12%nat 0%nat).
Proof using HLlo HLhi HLst rn LB FF LK A A' M M1 FPL Sp u n.
intros ROK CLI INC GRW FRF BA NFPB NFPW NFPS NFPI GFS GSH FSIN SCR Hu1 Hu2 Hu16 Hn DEFu SHu KSH.
pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ FPL a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRF. rewrite art_u_lit by lia. exact N. }
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
assert (FFA : fframes_apart u n (FF ++ LK)).
{ intros f Hf. destruct (FSIN f Hf) as (F1 & F2 & _). unfold apart, FS_BYTES in *. clear - F1 F2 Afk Hu1 Hu2. lia. }
assert (SHA : forall a0 n0, shadow_allowed A a0 n0 -> shadow_allowed A' a0 n0).
{ intros a0 n0 SA x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (SA x Hx). }
assert (SHB : forall b, In b LB -> 0 < snd b -> HAJ.shadow_blkR M (fst b) (snd b) -> HAJ.shadow_blkR M1 (fst b) (snd b)).
{ intros b Hb Hnb SB0.
assert (T : forall j, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M1 (HeapIfaceA.S (fst b) + j) v).
{ intros j Hj0 Hj v B. destruct (CB b Hb) as (B1 & _ & _ & _ & B5 & _).
pose proof (art_S_blk_hi (fst b) (snd b) j Hnb Hj) as H1. pose proof (art_S_ge (fst b) 0 ltac:(lia)) as H0. pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(rewrite HIeq in B5; lia)) as H2.
apply (art_byte_at_eq M M1); [|exact B]. apply EQ; [lia|]. apply (NFPB b _ Hb). right. unfold in_shadow_of. lia. }
exact (shadow_blkR_tby M M1 (fst b) (snd b) Hnb T SB0). }
split; [|split; [|split; [exact FFA|]]].
-
unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
+ intros b [Eb|Hb].
* subst b. cbn [fst snd]. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
split; [unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; lia|]. split; [exact DEFu|]. split; [left; exact SHu|].
split. { intros x Hx. unfold in_shadow_of in Hx. apply KSH.
pose proof (art_S_ge u (8192 * rn_qs rn) ltac:(lia)) as H0. pose proof (art_S_lt (u + n - 1) (8192 * rn_qs rn + 2 ^ 34) ltac:(lia)) as H2.
rewrite art_u_lit by lia. lia. }
split. { cbn [lb_remove fst]. rewrite Z.eqb_refl. exact BA. }
split; [exact FFA|]. split; [unfold apart, FS_BYTES in *; clear - Afk Hu1 Hu2; lia|]. intros _. clear - Hu1 G4. lia.
* destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
split. { intros i Hi. apply GRW. exact (B7 i Hi). }
split; [exact (SHB b Hb B4 B8)|]. split; [exact (SHA _ _ B9)|].
split. { cbn [lb_remove fst]. pose proof (BA b Hb) as AP. destruct (Z.eqb_spec u (fst b)) as [E|NE]; [exfalso; (clear - AP B1 B12 B4 CS1 CS6 E Flo Hn Hu1 Kspb Plo b n rn u; lia)|].
intros b' [Eb'|Hb']; [subst b'; cbn [fst snd]; lia|exact (B10 b' Hb')]. }
split; [exact B11|exact B12].
+ cbn [map fst]. apply NoDup_ListNoDup. constructor; [|apply NoDup_ListNoDup; exact CND]. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
destruct (CB b Hb) as (_ & _ & _ & B4 & _). pose proof (BA b Hb) as AP. lia.
-
unfold ablock_range. rewrite HLlo, HLhi. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. lia.
-
split.
+ intros a Ha CLa. apply EQ; [exact Ha|]. unfold aclient, aclient_g in CLa.
destruct CLa as [(b & Hb & Hr)|[((C1 & C2) & C3)|[((C1 & C2) & C3)|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
* apply (NFPB b a Hb). left. exact Hr.
* apply NFPS; [rewrite <- HIeq; exact C1|exact C3].
* rewrite HLlo in C1. rewrite HLhi in C2. apply NFPI; [lia|]. intros D. apply C3. apply HLst. exact D.
* destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _). apply NFPW; [exact Ha|]. apply (art_gap_out _ a 1); [|lia]. apply GFS; lia.
* apply NFPW; [exact Ha|]. apply (art_gap_out _ a 1); [|lia].
apply (GSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn)) a); [rewrite HIeq; lia|lia|lia|rewrite HIeq; unfold apart; lia|exact SH].
* destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3). apply NFPW; [exact Ha|]. apply (art_gap_out _ a 1); [|lia].
apply (GSH (ff_addr f) (ff_bytes (ff_class f)) a); [lia|exact F3|unfold FS_BYTES in *; lia|unfold apart, FS_BYTES in *; clear - F1 F2 Afk; lia|exact SH].
* apply (NFPB b a Hb). right. exact SH.
+ intros a Ha. apply GRW. exact (SCR a Ha).
Qed.
End SE.
End ExitClient.
