(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AProto ABytes AMalloc_iface AF_fse_iface AF_fse_rd_iface
AHarness_iface AH_fse_kit AH_fse_Eiface AH_fse_Diface AH_fse_cmp AF_fse_rd_asm.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac cl := repeat match goal with H : _ |- _ => clear H end.
Ltac d2_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [cl; lia| reflexivity]) end.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma le4_existsD : forall bs : list byte, length bs = 4%nat -> exists w : word, le4 w = bs.
Proof.
intros bs L. destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try discriminate L.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
exists (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)).
unfold le4. cbn [Z_to_le_bytes]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>11447729963.3130163642507.3837865240588.1063368414635.109311791775.10 00000A00j00m010013S1L1H2H02H42H52H9S1L2R01H2H02H42H52H93H103H142R12R22R33H15S1LS1LS1L".
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
f_equal; [|f_equal; [|f_equal; [|f_equal]]].
- rewrite <- (byte_of_unsigned b0) at 2. apply Z_to_bv8_mod. change (2^8) with 256. Z.div_mod_to_equations. lia.
- rewrite <- (byte_of_unsigned b1) at 2. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia.
- rewrite <- (byte_of_unsigned b2) at 2. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. Z.div_mod_to_equations. lia.
- rewrite <- (byte_of_unsigned b3) at 2. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^24) with 16777216. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma u8arr_mgD : forall (P : Z -> Prop) m m' A bs,
magree bsegs P m m' -> u8arr bsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr bsegs m' A bs.
Proof. intros P m m' A bs MG [HB HW] HP. split; [eapply bytes_at_magree; eassumption| eapply wr_at_magree; eassumption]. Qed.
Section D2P.
Variable AI : AMallocIface.
Variable rng_fs : alayout -> footprint -> Prop.
#[using="Type"] Theorem pD2_proof : pD2_stmt AI rng_fs.
Proof.
unfold pD2_stmt.
intros READ ISERR L RNG gp tp sp FR fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x25 x28 x29 x30 x31
m st LB SPA lo F P B pB pl tl msv dsz bsz rem nc data junk j0 j16 jrt jtl
EA PLB PLL JB JL AH NOF LBH HF HBB SP16 ESPA ST BOT LO SPT TP F2048 FH FC FRA NCA RTC MSVC TLC BA FSHC MI
RSTK RI RFS RF RSF.
pose proof atop_range as ATR.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (spa_props5 (bv_unsigned sp) SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA120).
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
unfold AHARNESS_STACK in LO.
Local Ltac2 Set LiaHints.tbl := fun () => "01V0?10339180819.17710696928713.2  11070687986.2  11097176271.1  11426771698.5  12780937220.1  13682220059.17915344703275.1  15609597663.1  16060046493.15116500284193.0  1668461688.1   1673145678.179 16895918723.1  1733665630.182 17614587087.1  1784423224.1   18021301321.17418032338296.1  18168056401.1751833332163.2   19473350319.3  19863675272.2  19955412260.2  20206155534.1  20966566545.33 23133729424.15423135524303.1  23490659993.10923502931250.13124852019251.1  25711238968.1  2599566318.182 26278433988.1  29021106940.4  30065197581.2  30449811937.17430664140363.3  31524613973.0  31653695134.1  3274984925.2   33715762100.2  33998777463.5  3412478029.1   35212070535.18236798602061.1  36895429096.0  38316814788.1  3832670709.7   38532111530.6  38692635477.0  39188636933.0  39220637093.0  39233079910.1  39587670199.2  39698210859.1  39716460113.18039862739071.16840228640085.0  41982982376.0  42547251748.18142754310803.6  43835966148.1  43872852652.18 43942869578.4  44381293930.1  45604656213.0  45804689888.17545860656981.0  47720504287.1  48330138856.0  50152101189.8  50698078190.1  50812080250.2  51390970281.1  51676463305.0  53028678485.0  53570524895.1  54161625196.6  55560391598.0  55581753195.1  57539263006.1  58616463592.0  59314923118.1  60917651944.1  63573689121.0  64775637746.5  65657744202.4  65694496620.6  66151427842.16 66687115354.3  66775507151.1  6744345055.1   67596179820.6  67680999037.17867680999039.17668670098477.2  7321096235.1   8272026751.168 8948038246.1   9211989531.179 966462368.5    00000A00E00J00K00T00U00f00g00h01901:01;01L01M01a01b01c02402502F02J02N02R02V02W03303D03E03F03N03O03P03a03b03g03l04E04J04K04L04P04U04^04_04`04a04b04c05005705805905:05;05?05@05Q05f05g05h06<06F06G06Y06^06_06`07907:07;07<07I07J07N07O07P07Q07R07\07]07^07_07`07c07d07e07n08308=08U08Y08Z08[08i08j08k08o09009E09F09W09aS2Q43LRJ4LRT03LRTS2Q2S3FH4SS3FH13FH4SS2Q43LRJ4LRT03LRTSSS2Q43LRJ4LRT03LRTSSS2Q43LRJ4LRT03LRTSS2Q22Q43LRJ4LRT03LRTSSS2Q43LRJ4LRT03LRTSS2Q43LRJ4LRT03LRTS2Q2S2HaS2Q1S2Q6SS5F20482K81H2H02H42H52H93H14S2Q43LRJ4LRT03LRTSSS2Q43LTLSSS2Q43LRJ4LRT03LRTSS3DBFS3FH4S3FH13FH42Q43LRJ4LRT03LRTS3Q11SSS2Q2S3FH4S2LO4SPABSFSSSS2LO3SPT4SPABS2JL2Q9SSSSS2Q2SS2Q43LRJ4LRT03LRTS3FH12Q43LRJ4LRT03LRTSSS2Q22Q43LRJ4LRT03LRTS3FH34ASPASS2Q22HX1H2H02H42H5S3DBFSSS3FH13FH42Q43LRJ4LRT03LRTSSSS3BOT2LO4SPABSS2Q6SSSSS3FH34ASPASSSSS1KSSS3FH13FH4S3DBFS3FH34ASPAS5SPA321H2H02H45F20482F8S2HaSSS3SPT4SPAB3LY3FFS2FKSS3FH12Q43LRJ4LRT03LRTSS2Q43LRJ4LRT03LRTS3SPT4SPAB".
assert (LOR : lo <= SPA - FSE_READ_STACK_A) by (unfold FSE_READ_STACK_A; clear - LO SPAB; lia).
assert (SPAT : SPA + 16 < al_top L) by (clear - SPAB SPT; lia).
assert (SPA16 : SPA mod 16 = 0) by (clear - SPA32; Z.div_mod_to_equations; lia).
assert (ASPA : ATOP + 4096 <= SPA) by (clear - LO BOT SPAB; lia).
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
assert (SPAK : SPA + 120 <= 2^47) by (clear - SPAB SPT LY3; lia).
assert (F8 : F mod 8 = 0) by (clear - F2048; Z.div_mod_to_equations; lia).
assert (F64 : F mod 64 = 0) by (clear - F2048; Z.div_mod_to_equations; lia).
assert (FK : F + 2048 + 8 <= KEND) by (unfold KEND; clear - FH4; lia).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (Q1 & Q2 & V & Q4 & _ & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
assert (LBUF : zlen (data ++ junk) = bsz) by (rewrite length_app; unfold FseNCount.Zlength in Q9; clear - Q9 JL; lia).
assert (BYT : Forall (fun c => 0 <= c < 256) (data ++ junk)) by (apply Forall_app; split; [apply all_bytes_Forall; exact Q10| exact JB]).
assert (LRJ : length jrt = 512%nat) by (destruct RTC as [[[Hn _] _] _]; exact Hn).
destruct (u16s_of_bytes 256 jrt ltac:(rewrite LRJ; reflexivity)) as (rt0 & LRT0 & _ & ERT).
assert (RTA : u8arr bsegs m (F + 1184) (u16s (map (Z_to_bv 64) rt0))) by (rewrite <- ERT; eapply u8arr_of_rw_cells; exact RTC).
assert (ZRT0 : zlen rt0 = 256) by (rewrite LRT0; reflexivity).
assert (LTL : length jtl = 4%nat) by (destruct TLC as [[[Hn _] _] _]; exact Hn).
destruct (le4_existsD jtl LTL) as (tl0 & ETL).
assert (TLC' : rw_cells bsegs m (F + 1776) [C4 tl0]).
{ eapply rw_cells_recast; [exact TLC| cbn; repeat split| cbn [cells_bytes cbytes]; rewrite ETL; reflexivity| reflexivity]. }
clear TLC.
pose proof (fseB_round_trip pl (zlen pl) junk rt0 AB ltac:(lia)) as RTT. rewrite EA in RTT.
destruct (RTT ltac:(apply Forall_all_bytes; exact JB) LRT0) as (rt & RD & LRT & AGREE & _).
clear RTT.
pose proof (fsh_unp_rt m F F2048 FH2 FK _ _ _ _ FSHC) as URT.
pose proof (fsh_unp_nc m F F2048 FH2 FK _ _ _ _ FSHC) as UNC.
pose proof (fsh_unp_msv m F F2048 FH2 FK _ _ _ _ FSHC) as UMS.
pose proof (fsh_unp_tl m F F2048 FH2 FK _ _ _ _ FSHC) as UTL.
pose proof (fsh_wr m F _ FSHC ltac:(reflexivity)) as WSH.
assert (SHOFF : forall k, 0 <= k -> k mod 8 = 0 -> shad (F + k) = SHF F + k / 8).
{ intros k Hk K8. rewrite <- SHF_shad. unfold SHF. rewrite !Z.shiftr_div_pow2 by (cl; lia). change (2^3) with 8.
clear - F2048 Hk K8. Z.div_mod_to_equations. lia. }
assert (DBF : F + 2048 <= B \/ B + bsz <= F).
{ assert (NE : mkABlock (ABFake 5) F 2048 <> HB pB B bsz) by discriminate.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HF HBB NE) as D. cbn in D. exact D. }
assert (RFRA : rng RNG SPA 120) by (eapply rng_sub'; [exact RSTK| clear - LO SPAB SPT; lia]).
unfold FRA_E in FRA.
do 9 zstep. zstep.
eapply evtF_cut.
{ refine (READ L RNG _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m st LB SPA (F + 1184) (F + 1760) (F + 1776) B pB
rt0 rt (data ++ junk) 255 msv tl dsz lo tl0
AH NOF LBH RTA MSVC TLC' (proj1 BA) BYT RD ltac:(cl; lia) ltac:(rewrite LBUF; clear - Q11; lia) ltac:(rewrite ZRT0; cl; lia)
_ ltac:(clear - F8; Z.div_mod_to_equations; lia) _ _ ltac:(clear - F8; Z.div_mod_to_equations; lia)
_ ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite LBUF; exact HBB)
ltac:(rewrite ZRT0; left; cl; lia) ltac:(rewrite ZRT0; left; cl; lia) ltac:(rewrite ZRT0, LBUF; clear - DBF; lia)
ltac:(left; cl; lia) ltac:(rewrite LBUF; clear - DBF; lia) ltac:(rewrite LBUF; clear - DBF; lia)
ST BOT LOR SPAT SPA16 MI TP RSTK RI RFS _ _ _ _ _ _ _ _ _ _ _).
-
split; [exists 5, F, 2048; split; [exact HF|]; rewrite ZRT0; repeat split; first [exact FH | exact F8 | cl; lia]|].
rewrite ZRT0. replace (F + 1184 + 2 * 256) with (F + 1696) by (cl; lia). exact URT.
-
exists 5, F, 2048. split; [exact HF|]. rewrite ZRT0. split; [cl; lia|]. split; [cl; lia|]. split; [exact F64|]. split; [reflexivity|].
split; [exact FH2|]. split; [unfold KEND; clear - FH4; lia|]. change (2048 / 8) with 256. split; [exact WSH| exact RSF].
- split; [exists 5, F, 2048; split; [exact HF|]; repeat split; first [exact FH | exact F8 | cl; lia]| replace (F + 1760 + 4) with (F + 1764) by (cl; lia); exact UMS].
- split; [exists 5, F, 2048; split; [exact HF|]; repeat split; first [exact FH | exact F8 | cl; lia]| replace (F + 1776 + 4) with (F + 1780) by (cl; lia); exact UTL].
- rewrite ZRT0. eapply rng_sub'; [exact RF| cl; lia].
- rewrite ZRT0. eapply rng_sub'; [exact RSF|]. rewrite (SHOFF 1184) by (cl; lia). rewrite SHF_shad.
unfold nshad. change (Z.shiftr (2 * 256 + 7) 3) with 64. change (1184 / 8) with 148. cl; lia.
- eapply rng_sub'; [exact RF| cl; lia].
- eapply rng_sub'; [exact RSF|]. rewrite (SHOFF 1760) by (cl; lia). rewrite SHF_shad. change (1760 / 8) with 220. cl; lia.
- eapply rng_sub'; [exact RF| cl; lia].
- eapply rng_sub'; [exact RSF|]. rewrite (SHOFF 1776) by (cl; lia). rewrite SHF_shad. change (1776 / 8) with 222. cl; lia.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite LBUF. reflexivity. }
cbv beta. intros ms' PO.
destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & MG' & AH' & RTA' & MSVC' & TLC2).
d2_retlit.
assert (FRA' : rw_cells bsegs m' SPA [CB 24 j0; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 dsz); C8 (Z_to_bv 64 (SHF F + 148));
C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 msv); CB 16 j16; C8 (Z_to_bv 64 F)]).
{ eapply rw_cells_magree; [exact MG'| exact FRA|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
intros a Ha. apply (pag_stackR AI LB SPA (F + 1184) (F + 1760) (F + 1776) rt0 SPA (SPA + 120)); [cl; lia| exact SPAK| rewrite ZRT0| | | exact Ha];
clear - ASPA FH3 ATR; lia. }
assert (NCA' : u8arr bsegs m' (F + 608) (u16s (map (Z_to_bv 64) nc))).
{ eapply u8arr_mgD; [exact MG'| exact NCA|]. rewrite u16s_length, length_map, Q4. intros a Ha.
apply (pag_blockR AI LB SPA (F + 1184) (F + 1760) (F + 1776) rt0 (mkABlock (ABFake 5) F 2048) (F + 608) 512 HF);
cbn [ab_addr ab_size]; [cl; lia| cl; lia| rewrite ZRT0; cl; lia| cl; lia| cl; lia| clear - Ha; lia]. }
assert (FSH' : rw_cells bsegs m' (SHF F) (FSH Z64 Z64 Z64 B04 B04)).
{ eapply rw_cells_magree; [exact MG'| exact FSHC|]. rewrite FSH_size. intros a Ha.
assert (ABN : ablk (F + 1184) (F + 1184 + 2 * zlen rt0)) by (rewrite ZRT0; eapply ablk_sub; [exact FH| cl; lia| cl; lia]).
assert (ABM : ablk (F + 1760) (F + 1760 + 4)) by (eapply ablk_sub; [exact FH| cl; lia| cl; lia]).
assert (ABT : ablk (F + 1776) (F + 1776 + 4)) by (eapply ablk_sub; [exact FH| cl; lia| cl; lia]).
apply (pag_shadowR AI LB SPA (F + 1184) (F + 1760) (F + 1776) rt0 5 F 2048 HF F8 eq_refl FH2 ltac:(clear - FH4; lia) ABN ABM ABT).
rewrite <- SHF_shad. change (2048 / 8) with 256. change (Z.of_nat 256) with 256 in Ha. clear - Ha. lia. }
clear FRA.
zstep. zstep.
eapply evtF_cut.
{ unfold fse_iserror_stmtA in ISERR.
eapply (ISERR RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dsz); [clear - Q6; lia| reflexivity]. }
cbv beta. intros ms' E. unfold fse_iserror_postA in E. subst ms'.
d2_retlit.
replace (2^64 - 119 <=? dsz) with false by (symmetry; apply Z.leb_gt; clear - Q6; lia). cbn [Z.b2z].
zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|]. clear K.
zstep. zstep. zstep.
zstep. if_cases K. { exfalso. revert K. rewrite bv_eqb_refl. discriminate. } clear K.
zstep. rewrite sx32_small by (clear - Q2; change (2^31) with 2147483648; lia).
zstep. if_cases K. { exfalso. revert K. rewrite bv_eqb_refl. discriminate. } clear K.
zstep. rewrite sx32_small by (clear - Q1; change (2^31) with 2147483648; lia).
zstep. if_cases K. { exfalso. revert K. rewrite bv_eqb_refl. discriminate. } clear K.
do 9 zstep.
assert (CNT : forall X, 0 < X < 2^47 -> msv < Z.land (0 - X) 18446744073709551615 ≫ 1 < 2^63).
{ intros X HX. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (cl; lia). rewrite Z.shiftr_div_pow2 by (cl; lia).
clear - HX Q2. change (2^1) with 2. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
replace (Z_to_bv 64 (Z.land (msv + 1) 4294967295)) with (Z_to_bv 64 (msv + 1 - 0))
by (f_equal; change 4294967295 with (Z.ones 32); rewrite Z.land_ones by (cl; lia); rewrite Z.mod_small; [cl; lia| clear - Q2; change (2^32) with 4294967296; lia]).
replace (Z_to_bv 64 (Z.land (0 - (F + 608)) 18446744073709551615 ≫ 1))
with (Z_to_bv 64 (Z.land (0 - (F + 608)) 18446744073709551615 ≫ 1 - 0)) by (f_equal; cl; lia).
replace (Z_to_bv 64 (Z.land (0 - (F + 1184)) 18446744073709551615 ≫ 1))
with (Z_to_bv 64 (Z.land (0 - (F + 1184)) 18446744073709551615 ≫ 1 - 0)) by (f_equal; cl; lia).
replace (Z_to_bv 64 (F + 608)) with (Z_to_bv 64 (F + 608 + 2 * 0)) by (f_equal; cl; lia).
replace (Z_to_bv 64 (F + 1184)) with (Z_to_bv 64 (F + 1184 + 2 * 0)) by (f_equal; cl; lia).
eapply (cmp_loopB RNG gp tp (Z_to_bv 64 SPA) sp (Z_to_bv 64 SPA) (Z_to_bv 64 (F + 1760)) x20 (Z_to_bv 64 dsz) (Z_to_bv 64 P)
(Z_to_bv 64 (F + 1776)) (Z_to_bv 64 (SHF F)) (Z_to_bv 64 B) FR fc m' (F + 608) (F + 1184) nc rt msv
(Z.land (0 - (F + 608)) 18446744073709551615 ≫ 1) (Z.land (0 - (F + 1184)) 18446744073709551615 ≫ 1) _
Q2 Q4 LRT (proj1 NCA') (proj1 RTA') AGREE
ltac:(split; [lia| split; [unfold KEND in *; clear - FK; lia| clear - F8; Z.div_mod_to_equations; lia]])
ltac:(split; [lia| split; [unfold KEND in *; clear - FK; lia| clear - F8; Z.div_mod_to_equations; lia]])
ltac:(replace (F + 608 + 512) with (F + 1120) by (cl; lia); exact (fsh_unp_nc m' F F2048 FH2 FK _ _ _ _ FSH'))
ltac:(replace (F + 1184 + 512) with (F + 1696) by (cl; lia); exact (fsh_unp_rt m' F F2048 FH2 FK _ _ _ _ FSH'))
ltac:(eapply rng_sub'; [exact RF| cl; lia]) ltac:(eapply rng_sub'; [exact RF| cl; lia])
ltac:(eapply rng_sub'; [exact RSF| rewrite (SHOFF 608) by (cl; lia); rewrite SHF_shad; change (608 / 8) with 76; cl; lia])
ltac:(eapply rng_sub'; [exact RSF| rewrite (SHOFF 1184) by (cl; lia); rewrite SHF_shad; change (1184 / 8) with 148; cl; lia])
(CNT (F + 608) ltac:(clear - FH1 FH4 ATR; unfold ATOP in *; lia)) (CNT (F + 1184) ltac:(clear - FH1 FH4 ATR; unfold ATOP in *; lia))
257%nat 0); [clear - Q2; lia| clear - Q2; lia|].
intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30 y31.
apply evtF_done. unfold pD2_post.
do 23 eexists. exists m'. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [| exact AH'].
rewrite ZRT0 in MG'. replace (F + 1184 + 2 * 256) with (F + 1696) in MG' by (cl; lia).
replace (F + 1760 + 4) with (F + 1764) in MG' by (cl; lia). replace (F + 1776 + 4) with (F + 1780) in MG' by (cl; lia). exact MG'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D2P.
End CANSEC1.
