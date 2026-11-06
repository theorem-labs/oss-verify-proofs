(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA As0Tables ArtMem JatLeaf JatAllocG JatPoison JatRzLog JatAllocA JatInitCache JatPopulate1
ArtRuns ArtRunsMem JatCls JatCARSpec JatDepotA JatDepot ArtBridge JatInv JatLift JatFsInv JatFsInvLaws JatIfaceLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatHandoffRi () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLift."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A0"; "1bool"; "1nat"; "1true"; "2and"; "2eq"; "2or"; "3Z"; "4page_base"; "0M"; "5apart"; "5cell"; "5wr"; "6mkH"; "6mrestrict"; "6page_allowedb"]; ["7art_rt_statics"; "7art_rt_thread"; "7rn_blk"; "7rn_ctx"; "7rn_kbase"; "7rn_parr"; "7rn_qs"; "7rn_ris"; "7rn_spb"; "7rn_t"; "8art_vis"; "9loaded_segments"; ":add"; ":le"; ":lt"; ":mul"]; [":of_nat"; ":pow"; "0a"; "0k"; "0lazy"; "0len"; "0lo"; "0n"; "0rn"; ";bv"; ";bv_unsigned"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Handoff.
Variable FSG : Type.
Variables (rn : art_run) (gfs0 : FSG) (k0 : nat) (A0 : list (Z * Z)) (lazy : list (word * word)) (M : word -> option byte).
#[local] Abbreviation G0 := (art_gs0 FSG gfs0 k0).
#[local] Abbreviation H := (mkH lazy A0).
Hypothesis REP : art_alloc_rep FSG rn G0 [] M.
Hypothesis LZ : art_lazy_ok FSG rn G0 A0 lazy.
#[using="LZ"] Lemma hr_vis_nonlazy : forall a n, (forall z, a <= z < a + n -> ~ art_lazy_zone FSG rn G0 z) -> art_vis H a n.
Proof.
intros a n NZ x Hx. destruct (mkH lazy A0 x) eqn:E; [|reflexivity]. exfalso. unfold mkH in E. apply andb_prop in E as [E _].
destruct LZ as (L1 & _). exact (NZ (U x) Hx (L1 x E)).
Qed.
#[using="Type"] Lemma hr_vis_allowed : ltac2:(TCodec.tc2 tcn__JatHandoffRi "Q4'7'Q9yR0%211'4&Mr3&Q:r1%2271%5241&N&Lr2%2281%4261%<261'5'1&?v0&8%119%4231(3%83721p0:1pRJH1&J&=vQ4%221;%431JCp061pR@Q21pR6Q31").
Proof. intros a n AL x Hx. unfold mkH. rewrite (AL x Hx). cbn. apply andb_false_r. Qed.
#[using="FSG rn gfs0 k0 M REP LZ"] Lemma hr_vis_img : ltac2:(TCodec.tc2 tcn__JatHandoffRi "E'7&M+RPP0r2%3221&Lr3%2214+VbTP0%8221&J&=vQ4v0%3221r4%6321:p081p0>1pR@C1pR6D1").
Proof. intros a n Ha Hn. destruct REP as (ROK & _). exact (art_img_vis FSG rn G0 A0 lazy a n ROK LZ Ha Hn). Qed.
#[using="FSG gfs0 k0 LZ"] Lemma hr_vis_obj : ltac2:(TCodec.tc2 tcn__JatHandoffRi "QF'7&Mr4r2%3221&Lr3%2214r5%4217%9231'6r6%8215+QoonlP0%>221+`PQoooPP0%@215%7231&:r7&BvQ8%211&Q1+2+G%3221%948@51r8&D%119+TPPPRTP0%>44=21r9&E%11>%B4381:&J&=vQ4v0%3221%531>Gp071p0<1p0B1p0M1p0Q61p0Q=1pR@QB1pR6QC1pR<QD1pR>QE1").
Proof.
intros lo len a n Ha Hn APP Ab Ak Ap. apply hr_vis_nonlazy. intros z Hz Z. unfold apart in *. destruct Z as [Z|[Z|[[Z|Z] _]]]; lia.
Qed.
#[using="FSG gfs0 k0 M REP LZ"] Lemma hr_vis_thread : ltac2:(TCodec.tc2 tcn__JatHandoffRi ":&J&=vQ4v0%3221&IvQ8%211+TP0%93521").
Proof. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. apply (hr_vis_obj (rn_t rn) 4096); [lia|lia|exact G10| | |]; unfold apart in *; [clear - Abt|clear - Atkb|clear - Apt]; lia. Qed.
#[using="FSG gfs0 k0 M REP LZ"] Lemma hr_vis_ctx : ltac2:(TCodec.tc2 tcn__JatHandoffRi ":&J&=vQ4v0%3221&CvQ8%211+TP0%93521").
Proof. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. apply (hr_vis_obj (rn_ctx rn) 4096); [lia|lia|exact G16| | |]; unfold apart in *; [clear - Abc|clear - Ackb|clear - Apc]; lia. Qed.
#[using="FSG gfs0 k0 M REP LZ"] Lemma hr_vis_ris : ltac2:(TCodec.tc2 tcn__JatHandoffRi ":&J&=vQ4v0%3221&GvQ8%211+TP0%93521").
Proof.
destruct REP as (ROK & _). rok_open ROK. geo_open GEO. apply hr_vis_nonlazy. intros z Hz Z.
destruct Z as [Z|[Z|[Z NC]]]; [clear - Hz Z G4 Eris; lia|clear - Hz Z Abk Eris; unfold apart in *; lia|]. apply NC. left. exact Hz.
Qed.
#[using="Type"] Lemma hr_cell : ltac2:(TCodec.tc2 tcn__JatHandoffRi "Q9'7'2&Mzr3%3221&N&Lr4&Q0%116%4231&Q1+2+R0%3221%:251&J&=vQ4v0%3221r5%>1?%73321&;&Kv9r6%453217E&>%12:4r7%857215;p051p0;1p0D1p0Q01pRHQ61pR@Q61pR6Q81").
Proof. intros a n v Ha Hn V C. exact (proj2 (art_cell_vis H M a n v Ha Hn V) C). Qed.
#[using="FSG rn gfs0 k0 REP LZ"] Lemma hr_cell_img : ltac2:(TCodec.tc2 tcn__JatHandoffRi "Q0'7'2&M+RPP0r3%3221&Lr4&Q0%115%4231+VbTP0%:221&;&Kv9r5%45321:=&>&=vQ4v0%3221%5218r6%<5;219Bp091p0?1p0G1pRHM1pR@M1pR6O1").
Proof. intros a n v Ha Hn C. apply hr_cell; [lia|lia|apply hr_vis_img; lia|exact C]. Qed.
#[using="Type"] Lemma hr_cell_in : ltac2:(TCodec.tc2 tcn__JatHandoffRi "QA'7'2&J&=vQ4v0%3221r5r4%73321&Mzr6%3221&N&Lr7%2215&Q1+2+R0%3221%8251r8%>21<&Q0%11>%<2;1r9%>216%D231&;&Kv9%3521;BF&>%12N3%65519>Ep041p091p0@1p0C1p0M1p0Q21pRHQ<1pR@Q<1pR6Q>1pR<Q?1pR>Q@1").
Proof. intros lo len a n v V Hlo Hhi Ha Hn C. apply hr_cell; [lia|lia|exact (art_vis_sub H lo len a _ V Ha Hn)|exact C]. Qed.
#[using="Type"] Lemma hr_wr : ltac2:(TCodec.tc2 tcn__JatHandoffRi "Q4'7&Mzr2%3221&N&Lr3%2215&Q1+2+R0%3221%8251&J&=vQ4v0%3221r4%6321=&<&Kv9r5%443216&>%1294r6%847215p051p0;1p0C1p0M1pR@Q21pR6Q31").
Proof. intros a n Ha Hn V W. exact (proj2 (art_wr_vis H M a n Ha Hn V) W). Qed.
#[local] Ltac timg := apply hr_cell_img; [first [lia|cbn; lia] | first [lia|cbn; lia] | assumption].
#[using="FSG gfs0 k0 M REP"] Lemma hr_bounds : ltac2:(TCodec.tc2 tcn__JatHandoffRi "QF'4&M+TP0&IvQ8%211%5241&N&L%1247&Q1+2+QO%3221%7251&C%11<%@2?1%:22@%<216z&G%11B%F231%@22F%B21<&H%11G%K281+Q5%D2C1%G241%I21C&F%11N%Q22?1&O+XP0%2214+Q2%N2M1%Q1231+QN%Q12Q01%Q5231%Q=2:1%Q>2>1%Q?2C1%Q@2G1%QA2J1%QB2O1%QC2Q21%QD2Q61%QE2Q?1").
Proof. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. rewrite Eris in *. repeat split; lia. Qed.
#[using="FSG gfs0 k0 REP LZ"] Lemma hr_statics : ltac2:(TCodec.tc2 tcn__JatHandoffRi ":&@vQ8&>&=vQ4v0%3221v9%6221%9281").
Proof.
pose proof REP as (_ & ST & _). destruct hr_bounds as (B1 & B2 & B3 & B4 & _). pose proof hr_vis_ctx as VC.
destruct ST as (PC & L & T & RO & RZ & DR & TG & CS). unfold art_rt_statics.
split. { unfold art_prim_consts in *. decompose [and] PC. repeat split; timg. }
split. { unfold art_layout in *. decompose [and] L. repeat split; timg. }
split. { destruct T as (C1 & C2 & C3 & C4 & C5 & RR). pose proof RR as (R1 & R2 & R3 & R4 & R5 & _).
pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
unfold art_tsd. split; [timg|]. split; [timg|].
split; [apply hr_cell_img; [clear - Htpd; lia|cbn; clear - G20; lia|exact C3]|].
split; [apply hr_cell_img; [clear - G21 Hkey; lia|cbn; clear - G22 Hkey; lia|exact C4]|]. split; [|exact RR].
apply (hr_cell_in (rn_ctx rn) 4096); [exact VC|clear - B3; lia|clear - B4; lia|lia|cbn; lia|exact C5]. }
split. { unfold art_alloc_rodata in *. decompose [and] RO. repeat split; timg. }
split. { unfold art_rz_rodata in *. decompose [and] RZ. repeat split; timg. }
split. { unfold DRoD in *. decompose [and] DR. repeat split; timg. }
split. { destruct TG as (GN & T1 & T2). split; [|split; timg]. intros a Ha. unfold mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|exact (GN a Ha)]. }
decompose [and] CS. repeat split; timg.
Qed.
#[using="FSG gfs0 k0 REP LZ"] Lemma hr_thread_cell : ltac2:(TCodec.tc2 tcn__JatHandoffRi "Q3'7'2&M&IvQ8%211r3%5221&Lr4&Q0%115%4231+TP0%6291%=231&;&Kv9r5%45321;>&>&=vQ4v0%3221%5218r6%<5;219Cp091p0?1p0H1pRHQ01pR8Q01pR6Q21").
Proof. intros a k v Ha Hk C. destruct hr_bounds as (B1 & B2 & _). apply (hr_cell_in (rn_t rn) 4096); [exact hr_vis_thread|lia|lia|exact Ha|exact Hk|exact C]. Qed.
#[using="FSG gfs0 k0 REP LZ"] Lemma hr_thread : ltac2:(TCodec.tc2 tcn__JatHandoffRi ":&AvQ8&>&=vQ4v0%3221v9%6221%9281").
Proof.
pose proof REP as (_ & _ & TH & _). destruct hr_bounds as (B1 & B2 & B3 & B4 & _).
destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold art_rt_thread.
split; [apply hr_wr; [lia|lia|exact hr_vis_thread|exact Wt]|]. split; [apply hr_thread_cell; [lia|cbn; lia|exact C1]|].
split; [apply (hr_cell_in (rn_ctx rn) 4096); [exact hr_vis_ctx|lia|lia|lia|cbn; lia|exact C2]|].
split; [apply hr_thread_cell; [lia|cbn; lia|exact C3]|]. split; [apply hr_thread_cell; [lia|cbn; lia|exact C4]|].
split; [apply hr_thread_cell; [lia|cbn; lia|exact C5]|]. split; [apply hr_thread_cell; [lia|cbn; lia|exact C6]|].
pose proof REP as (ROK & _). rok_open ROK. apply hr_cell_img; [clear - Hloff'; lia|cbn; clear - Hloff''; lia|exact C7].
Qed.
#[using="REP LZ"] Lemma hr_primary : art_rt_primary FSG rn G0 (mrestrict H M).
Proof.
pose proof REP as (_ & _ & _ & (PH & PRIM & Wsh) & _). destruct hr_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). pose proof hr_vis_ris as VR.
split; [|split].
- intros c Hc. destruct (PH c Hc) as (P1 & P2). split; apply hr_thread_cell; first [lia|cbn; lia|assumption].
- intros c Hc. destruct (PRIM c Hc) as (RC & REST). split; [|exact REST]. cbn [art_gs0 g_cls] in *.
destruct RC as ((C0 & CW) & (R0 & R16 & R24 & R32 & R40 & R48 & R56 & R72 & R80 & RF & W1 & W2 & W3)). cbn [art_cls0 cl_cache cl_free cl_mfa cl_mu cl_au length] in *.
assert (RI : forall a (k : nat) v, rn_ris rn + 128 * c <= a -> a + Z.of_nat k <= rn_ris rn + 128 * c + 128 -> cellA M a k v -> cellA (mrestrict H M) a k v).
{ intros a k v Ha Hk C. apply (hr_cell_in (rn_ris rn) 4096); [exact VR|lia|lia|lia|lia|exact C]. }
split; [split|].
+ apply hr_thread_cell; [lia|cbn; lia|exact C0].
+ intros j Hj. exfalso. cbn in Hj. lia.
+ repeat split.
1-9: apply RI; first [lia|cbn; lia|assumption].
* intros j Hj. exfalso. cbn in Hj. lia.
* apply hr_wr; [lia|lia|exact (art_vis_sub H (rn_ris rn) 4096 (rn_ris rn + 128 * c) 128 VR ltac:(lia) ltac:(lia))|exact W1].
* cbn [art_cls0 cl_mfa]. apply hr_wr; [lia|lia|intros x Hx; lia|exact W2].
* cbn [art_cls0 cl_mu]. apply hr_wr; [lia|lia|intros x Hx; lia|exact W3].
- apply hr_wr; [lia|lia| |exact Wsh]. apply hr_vis_allowed. destruct LZ as (_ & _ & L3 & _). intros x Hx. apply L3. lia.
Qed.
#[using="REP LZ"] Theorem art_alloc_rep_restrict : art_alloc_rep FSG rn G0 [] (mrestrict H M).
Proof.
pose proof REP as (ROK & _ & _ & _ & CH & SEC & QU & DEP & IA & BL & _).
split; [exact ROK|]. split; [exact hr_statics|]. split; [exact hr_thread|]. split; [exact hr_primary|].
split. {
intros c Hc. specialize (CH c Hc). cbv zeta in *. cbn [art_gs0 g_cls g_st art_cls0 cl_au cl_mu cl_cache cl_free] in *. destruct CH as (C1 & C2 & C3 & C4).
split; [intros x Hx; exfalso; lia|]. split; [exact C2|]. split; [exact C3|].
intros w Hw. exfalso. destruct (C4 w Hw) as (I1 & _). destruct I1. }
split. {
destruct SEC as (C1 & C2 & C3 & C4 & C5 & C6 & S1 & S2 & SALL & SLIVE & SLEN). unfold art_rt_sec. cbn [art_gs0 g_sec g_sec_committed g_log g_qt g_qg] in *.
split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|]. split; [exact S1|]. split; [intros E; discriminate E|].
split; [intros i s Hi; destruct i; discriminate Hi|]. split; [exact SLIVE|exact SLEN]. }
split. {
destruct QU as ((f1 & l1 & T1 & T2 & T3 & T4 & BL1) & (f2 & l2 & Q1 & Q2 & Q3 & Q4 & BL2) & B1 & B2 & MX & REST). unfold art_rt_quar. cbn [art_gs0 g_qt g_qg] in *.
split. { exists f1, l1. split; [apply hr_thread_cell; [lia|cbn; lia|exact T1]|]. split; [apply hr_thread_cell; [lia|cbn; lia|exact T2]|]. split; [apply hr_thread_cell; [lia|cbn; lia|exact T3]|].
split; [apply hr_thread_cell; [lia|cbn; lia|exact T4]|exact BL1]. }
split. { exists f2, l2. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|exact BL2]. }
split; [exact B1|]. split; [exact B2|]. split; [timg|exact REST]. }
split. {
unfold art_rt_depot in *. apply (DInvD_frame (rn_l2 rn) (rn_blk rn) _ M (mrestrict H M) DEP). intros x Dx. unfold mrestrict.
assert (V : H x = false); [|rewrite V; reflexivity].
destruct DEP as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _). rok_open ROK. unfold dprivD in Dx. destruct Dx as [D|[D|D]].
- apply (hr_vis_img (U x) 1); lia.
- apply (hr_vis_obj (rn_l2 rn) (2 ^ 20) (U x) 1); [lia|lia|clear - Al2s; unfold apart in *; lia|exact DG7|exact Al2kb|clear - Apl; unfold apart in *; lia|lia].
- destruct LZ as (_ & _ & _ & L4). unfold mkH. rewrite (L4 x D). cbn. apply andb_false_r. }
split. {
destruct IA as (C1 & C3 & C4). cbn [art_gs0 g_ia g_qt g_qg] in *. split; [timg|]. split; [intros E; discriminate E|exact C4]. }
split; [exact BL|].
pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (T1 & T23 & T4 & T5)). unfold art_rt_ghost in *. cbn [art_gs0 g_qt g_qg g_cls app] in *.
split; [intros b it []|]. split; [exact T23|]. split; [intros b []|timg].
Qed.
End Handoff.
Lemma art_rt_ghost_gs0 : forall (FSG : Type) rn (gfs0 : FSG) k0 (M : word -> option byte),
cellA M (0x137970 + 72) 8 0xe666661 -> art_rt_ghost FSG rn (art_gs0 FSG gfs0 k0) M.
Proof.
intros FSG rn gfs0 k0 M C. unfold art_rt_ghost. cbn [art_gs0 g_qt g_qg g_cls app]. split; [intros b it []|]. split; [|split; [intros b []|exact C]].
intros c Hc. cbn [art_cls0 cl_au cl_mfa cl_cache length]. split; [intros X; exfalso; lia|]. pose proof (art_ic_mc_range c ltac:(lia)). cbn. lia.
Qed.
Section Top.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
#[using="Type"] Theorem art_handoff_ri : forall rn gfs0 k0 K0 B0 A0 M V,
art_handoff_target FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn gfs0 k0 K0 B0 A0 M V ->
art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn [] [] [] (K0, B0) A0 M V.
Proof.
intros rn gfs0 k0 K0 B0 A0 M V (REP & FS & BV & CRED & CLI & KN & LZ & EG).
exists (art_gs0 FSG gfs0 k0). split; [exact (art_alloc_rep_restrict FSG rn gfs0 k0 A0 (snd V) M REP LZ)|].
cbn [art_gs0 g_fs g_log]. repeat (split; [assumption|]). exact EG.
Qed.
End Top.
