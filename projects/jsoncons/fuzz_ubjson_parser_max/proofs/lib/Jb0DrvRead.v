(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare MemSplit AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
RefNodes RefMemcpyLib HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvLib
Jb0RegionPoisoned Jb0AsanMemcpy Jb0ReadIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvRead () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvRead."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvRead.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ReadIcpt."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1false"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "2ex"; "2not"; "3add"; "4le"; "4lt"; "5map"; "6Z"; "0E"; "0E'"; "0FF"; "0H"; "0HI"; "0K"; "0L"; "0LB"]; ["0LK"; "7len_word"; "8Fs"; "8file_read"; "8fs_lookup"; "8path"; "9store_ok"; ":mkCfg"; ";FdEntry"; ";FdFile"; ";Model"; ";fd_insert"; ";fd_lookup"; ";m_fds"; ";m_fs"; "<bvmap"]; ["0M"; "0M'"; "0M0"; "0M1"; "0M2"; "0M3'"; "0MV"; "0MV2"; "0Ma"; "0R"; "0R'"; "0R2"; "0R3"; "=mrestrict"; "=range_avoids"; ">msteps"]; ["?find_nz"; "@credit"; "Aahid"; "Abyte_at"; "Acell_is"; "Afframe"; "Ain_shadow_of"; "Ari_inv"; "Ashadow_allowed"; "Avml"; "Avml_of"; "Bret_ok"; "Cdinv"; "Chas_window"; "Csub_blockA"; "Erd_MV2"]; ["DRD_CELLS"; "DSTAGE"; "Dkeep_readA"; "Fc_kept"; "GRIPL"; "Hkeeps_but"; "Igetr"; "Imkst"; "Irdn"; "Iseg_rom"; "JTSet"; "Ksrealizes"; "Lmem_grows"; "Mjunk_vals"; "Msr_after_call_j"; "NEnv"]; ["Nenv"; "Nexpr"; "Nkentry"; "Nridx"; "Oknow_ok"; "Oregs_ok"; "Pkn_vars_lt"; "Psr_vars_lt"; "Pvals_ev"; "Qloaded_segments"; "RIn"; "Sadd"; "Sle"; "Slt"; "Smodulo"; "Sof_nat"]; ["Sopp"; "Spow"; "Ssub"; "Sto_nat"; "0V"; "0a"; "0ar"; "0b"; "0bls"; "0bs"; "0cnt"; "0cr"; "0data"; "0ebs"; "0fx"; "0i"]; ["0k"; "0kn"; "0model"; "0model'"; "0n"; "0nb"; "0off"; "0pth"; "0ra"; "0raw"; "0s"; "0scfg"; "0so"; "0sp0"; "0sr"; "TBV"]; ["TZ_to_bv"; "Tbv"; "Tbv_add"; "Tbv_unsigned"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0w"; "0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition RD_CELLS : list (Z * Z * Z) :=
[(0x13d718, 1, 1); (0x1361f8, 8, 0x12d1e8);
(0x1343a0, 8, 0x13ca38); (0x13ca38, 8, 0x7fff8000); (0x1343a8, 8, 0x13d728); (0x13d728, 8, 0); (0x1343b0, 8, 0x13d730); (0x13d730, 8, 0);
(0x1343b8, 8, 0x13d720); (0x13d720, 8, 0x7fffffffffff)].
Definition STAGE : Z := 0x65f090.
Definition IMG_NOSTAGE : list (Z * Z) :=
[(0x10000, 0x136000); (0x138ac0, 0x139380); (0x66f090, 0x670a68); (0x670a70, 0x670ab8); (0x670ad4, 0x670ae8); (0x670af0, 0x691f78);
(0x691f80, 0x693000)].
Definition keep_readA (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep 0 so 2200 bls vbnd [] IMG_NOSTAGE IMG_RW_A kn.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section ReadMem.
Variable H : word -> bool.
Variable M : word -> option byte.
Variables (s : Z) (raw : word) (R : bvmap 5 word) (bs : list byte).
Hypothesis Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64.
Hypothesis Hbs : Z.of_nat (length bs) <= 65536.
Hypothesis Hvis_fr : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false.
Hypothesis Hvis_st : forall x : word, STAGE <= bv_unsigned x < STAGE + 65536 -> H x = false.
Hypothesis Hfar : STAGE + 65536 <= s - 2200.
Let MV := mrestrict H M.
Let Ma := RDA MV raw s R.
Let M1 := munrestrict H M Ma.
Let M2 := wbytes M1 (Z_to_bv 64 STAGE) bs.
Let MV2 := mrestrict H M2.
Definition rd_M1 := M1. Definition rd_M2 := M2. Definition rd_MV2 := MV2.
Lemma rd_M1_restrict : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "?'@'TAyR0%211':y8%511%311p051&QMvKvQC%3221vQH%>3621").
Proof.
apply mrestrict_munrestrict. intros a Ha. unfold Ma.
destruct (Z_lt_le_dec (bv_unsigned a) (s - 2144)) as [L1|L1]; [rewrite (RDA_out MV raw s Hs R a) by lia; unfold MV, mrestrict; rewrite Ha; reflexivity|].
destruct (Z_lt_le_dec (bv_unsigned a) s) as [L2|L2]; [rewrite (Hvis_fr a) in Ha by lia; discriminate|].
rewrite (RDA_out MV raw s Hs R a) by lia. unfold MV, mrestrict. rewrite Ha. reflexivity.
Qed.
Lemma rd_M2_out : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "Q:'TAyR0%211&B'?&S<&SBvT:+RTH%3221&TCr1%22;1%8241&S=%1238%<231%>11&RAr2%:2C1%@231&S;+RPP0%2261%;251%F251%H11'@':y8%O11%311vQDr3%211vQ@%113%:3631p0<1p0G1pYDQ71").
Proof.
intros x N1 N2. unfold M2. unfold STAGE in *.
rewrite wbytes_out by (rewrite u_small by lia; lia).
unfold M1, munrestrict. destruct (H x) eqn:Hx; [reflexivity|].
unfold Ma. rewrite (RDA_out MV raw s Hs R x) by lia. unfold MV, mrestrict. rewrite Hx. reflexivity.
Qed.
Lemma rd_M2_grows : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "G'TAyR0%211&B'@':y8%711%311vQ@r1%211(1%116%:3631%<11vQDr2%211%?3;16%A11p061pYDD1").
Proof.
intros x Hd. unfold M2. apply wbytes_grows. unfold M1, munrestrict. destruct (H x) eqn:Hx; [exact Hd|].
unfold Ma. apply RDA_grows. unfold MV, mrestrict. rewrite Hx. exact Hd.
Qed.
Lemma rd_MV2_grows : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "4&RLvQFvQG%3221").
Proof.
intros x Hd. unfold MV2, mrestrict. unfold MV, mrestrict in Hd. destruct (H x) eqn:Hx; [exact Hd|]. apply rd_M2_grows. exact Hd.
Qed.
Lemma rd_MV2_frames : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "M'TAyR0%211'?&S<&SBvT:+RTH%3221&TCr1%22:1%8241&S=%1238%<231'@':y8%C11%311vQGr2%211vQH%113%:3631p0<1pYDJ1").
Proof.
intros x Hx. unfold MV2, mrestrict. rewrite (Hvis_fr x Hx). unfold M2, STAGE in *.
rewrite wbytes_out by (rewrite u_small by lia; lia).
unfold M1, munrestrict. rewrite (Hvis_fr x Hx). reflexivity.
Qed.
Lemma rd_MV2_slot : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "Q2'G'?&S<+8r1%3221+RTH%5231%7231'@':'8'TAy8%211%411%611&RH&S9vQG&T@yR0&SBvT:r2%3221%6251u8%;4:921vQH%=4<143%F3?31p0H1pX2Q11").
Proof.
intros k Hk. apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. cbn in Hx.
apply rd_MV2_frames. lia.
Qed.
Lemma rd_stage_bytes : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "F'@':'8'TAy8%211%411%611&RH&S9vQD&T@yR0&RA%3221&7vSI%22<1%:49841(3%12>4%E3>31").
Proof. unfold M2. apply rdn_wbytes_hit. unfold STAGE. rewrite u_small by lia. lia. Qed.
End ReadMem.
Section DrvRead.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hcells : incl RD_CELLS (asc_cells C).
Variable M0 : word -> option byte.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
#[local] Notation dinvA := (dinv ar HI sp0 M0).
Lemma rd_cell : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "QE'8'<'G%2211%411&R5%611&R1'TAyR0%211':y8%511%311p051&R9&R7vLr:r9r8r7r6r5r4%9887654321&S:%K2IJ(;r3%24MM61r2%44NO21&R@%83721&R4&S9&SC%11>%453B@1:p061p0@1pY:Q91pX:Q:1pW<Q;1pW:N1pS2Q01p2Q<1pWHQ:1pR2Q<1pQFQ=1pR0Q@1").
Proof.
intros LB FF LK cr A M V a n v HH Hin.
destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
exact (proj1 (Forall_forall _ _) CS (a, n, v) (Hcells _ Hin)).
Qed.
Lemma avoid_img : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "QI'8'<'G%2211%411&R5%611&R1'TAyR0%211':y8%511%311p051'Q:'9&R7vLr9r8r7r6r5r4&R:r3%211%;8:9876541&S<z%2215&S;&S?%118%32;1+Vb\P0%8221&QN&R2%12DB&T@%12Q2C%5331Cp071p0>1p0B1pX:O1pW<Q?1pX6Q21pS2Q41p2Q@1pWHQ>1pR2Q@1pQFQA1pR0QD1").
Proof.
intros LB FF LK cr A M model a n HH Ha Hn k Hk. unfold woff. rewrite (u_small a) by lia.
apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (a + Z.of_nat k) HH); lia.
Qed.
Lemma vis_of_allowed : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "Q0'8'<'G%2211%411'Q:&R8r5r3r2%43321&R6r4%23154'@'5&R2r7r6&T@yR0%221=%63541(6%:3921p0<1p0@1pYDI1pX:J1pW<K1pX6I1p2K1").
Proof.
intros A model a n x SA Hx. unfold ahid, mkH. rewrite (SA x Hx). apply andb_false_r.
Qed.
Lemma stage_shadow : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "QH'8'<'G%2211%411&R5%611&R1'TAyR0%211':y8%511%311p051'Q:&R7vLr7r6r5r4r3r2&R:r1%211%;8:9876541&R6+V[lT0+RPR@%33216'?&R3z%23?<1'@'5&R2&T@%12Q0A%33FD1(6%73621%<291p0>1pYDQ=1p0D1pX6Q11pS2Q31p2Q?1pWHQ=1pR2Q?1pQFQ@1pR0QC1").
Proof.
intros LB FF LK cr A M model HH x Hx.
destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0x65f080 0x10050) as (Z0 & SA).
- rewrite (dla_img_lo _ _ _ _ DL). lia.
- rewrite (dla_img_hi _ _ _ _ DL). lia.
- lia.
- rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- split; [exact (Z0 x Hx) | exact (vis_of_allowed A model _ _ x SA Hx)].
Qed.
Lemma w_lit : ltac2:(TCodec.tc2 tcn__Jb0DrvRead "A'G'TAyR0%211'@&TCr1%2251r2%53921&T@r3%22:1%93:15p051pYB<1pYF@1").
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.
Section SE.
Local Abbreviation SEC_T_rd_post := (ltac2:(TCodec.tc2 tcn__Jb0DrvRead "VO'8'<'G%2211%411&R5%611&R1'TAyR0%211':y8%511%311p051'Q:&Q?y5%2219%D17'5p0<1&R2r8r6%3221&R?r1r5r4r2%56487321&S?&7r3%22G1%411&R7vLr?r>r=r<r;r:&R:r9%211%;8:9876541&S<+RPP0%22E1'?&SB&TCvT=%22Q@1+TPPP0%5221+TP0%7221%<21A%=2B6%;221'@&Q6&S9&QM%12Q<K&T@+RTH%B2L1%32R01uRTH%948621(=%<3QH21&R;%11Q3&RF(T?+:(>%33R221%52Q81%@2R=QM%F3R=21+2%83R716%:2Q>1+RS0%Q62QC1%G2RD1%M3RD41+1%?3R>1=%A2QF1+QUd`@%B3RJ1@/01RJ%Q43RK41+8%F3RE1D%H2QN1r@%Q42S11%Q:3S131+9%L3RK1J%N2R51+V[lT@%Q:2S71%Q@3S731+D%Q23S11Q0%Q42R<1%Q?2S<F%QE3S<21'A'QO&RGvSNrB+QTmn0%Q<3SD1Q:/01SD&RI%11QM%85763RI1rD%:59S41S73%<3R131%QE2S6QA%R02SMRM%R63SM21%QH2S9Q?rE%R42T11%R:3T131%QL2S=Q<%R<3T31;%QN2S?Q7rC%R021Q9%R@3T731%R22SCQ5%R324Q6%RC3T:21+B%R53T41R3%R72SH1%R8292%RH3T?21+C%R:3T91R8%R<2SM1%R=2>2%RM3TD21%R?2T0Q<%R@2AQ=%S03TG21&RE&RD%231Q9T5&BrF%SA21S0%SA2TOT<%SG221&S=%1235%SG231%811%T;1T?rA%11TA%S@3U331p051pYDU91&RL%12T=TI%T1231%T22C1%T32G1%T42K1%T52Q11%T62Q71%T72Q;1%T82Q@1%T92QC1%T:2QH1%T;2QL1qS<UB1%R;2UC1qSJU@1%R=2UA1p0R?1p0RE1p0RL1p0S31p0S;1p0SC1p0SL1p0SO1p0T=1p0TJ1p0TN1tX:V>U;1tS@V2UA1tQHULUH1pWDUO1pSHV11pSDV21pXDV<1pXFVE1pX6V81pS2V:1p2VF1pWHVD1pR2VF1pQFVG1pR0VJ1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_rd_post) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_rd_post) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_rd_post) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_rd_post) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_rd_post) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_rd_post) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_rd_post) 6%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_rd_post) 7%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_rd_post) 8%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_rd_post) 9%nat 0%nat).
Variable R2 : ltac:(sec_ty2 constr:(SEC_T_rd_post) 10%nat 0%nat).
Variable bs : ltac:(sec_ty2 constr:(SEC_T_rd_post) 11%nat 0%nat).
Lemma rd_post : ltac:(sec_stmt2 constr:(SEC_T_rd_post) 12%nat 0%nat).
Proof.
intros H MV2 n HH Hn Hsr WOK Hret Q10 Q2 Q1 Q8 Q9 Q20.
pose proof Hsp as Hsp'.
assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by lia.
assert (Hbs : Z.of_nat (length bs) <= 65536) by exact Hn.
assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
assert (VST : forall x : word, STAGE <= bv_unsigned x < STAGE + 65536 -> H x = false).
{ intros x Hx. unfold STAGE in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
assert (Hfar : STAGE + 65536 <= s - 2200) by (unfold STAGE; lia).
pose proof (RDA_slots (mrestrict H M) raw s Hs R) as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7).
assert (T1 : rdn ASEGS MV2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 raw)) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 8) by lia; exact SL1).
assert (T2 : rdn ASEGS MV2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 16) by lia; exact SL2).
assert (T3 : rdn ASEGS MV2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 24) by lia; exact SL3).
assert (T4 : rdn ASEGS MV2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr R 18))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 32) by lia; exact SL4).
assert (T5 : rdn ASEGS MV2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr R 19))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 40) by lia; exact SL5).
assert (T6 : rdn ASEGS MV2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr R 20))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 48) by lia; exact SL6).
assert (T7 : rdn ASEGS MV2 (Z_to_bv 64 (s - 2136)) 8 = Some (word_to_le_bytes 8 (0x64f34%bv : word))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 2136) by lia; exact SL7).
destruct (Z.eq_dec n 0) as [Hn0|Hnz].
-
rewrite Hn0 in Q10.
destruct (read_icpt_post0_run (seg_rom ASEGS) raw s Hs Hret R R2 MV2 Q10 Q2 Q1 Q8 Q20 T7 T1 T2 T3 T4 T5 T6)
as (R3 & RUN & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB).
exists R3, MV2. rewrite Hn0. repeat (split; [assumption|]). split; [intros x _; reflexivity | intros x Hx; exact Hx].
- assert (Hnp : 0 < n) by lia.
assert (XO : forall x : word, H x = false -> ~ (s - 2200 <= bv_unsigned x < s) -> ~ (STAGE <= bv_unsigned x < STAGE + 65536) -> MV2 x = M x).
{ intros x Hx N1 N2. unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact (rd_M2_out H M s raw R bs Hs Hbs x N1 N2). }
assert (CV2 : forall a v, In (a, 8, v) RD_CELLS -> rdn ASEGS MV2 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v))).
{ intros a v Hin. rewrite <- (rd_cell _ _ _ _ _ _ _ a 8 v HH Hin).
assert (RA : 0x12d000 <= a /\ a + 8 <= 0x13e280).
{ unfold RD_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; try lia|]); try destruct Hin.
all: try discriminate. }
apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. cbn in Hx.
apply XO; [| lia | unfold STAGE; lia].
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
assert (SHZ : forall x, 0x7fff8000 + 0xcbe10 <= x <= 0x7fff8000 + 0xcde19 -> MV2 (Z_to_bv 64 x) = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct (stage_shadow _ _ _ _ _ _ model HH x) as (BZ & VZ).
- unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB. change (0x65f080 / 8) with 0xcbe10. change ((0x65f080 + 0x10050 - 1) / 8) with 0xcde19. lia.
- rewrite XO; [exact BZ | exact VZ | rewrite u_small by lia; lia | rewrite u_small by lia; unfold STAGE; lia]. }
assert (DV : (0x65f090 + n - 1) / 8 <= 0xcde11).
{ change 0xcde11 with ((0x65f090 + 65536 - 1) / 8). apply Z.div_le_mono; lia. }
assert (DL0 : 0xcbe12 <= (0x65f090 + n - 1) / 8).
{ change 0xcbe12 with (0x65f090 / 8). apply Z.div_le_mono; lia. }
destruct (read_icpt_post_run MV2 (seg_rom ASEGS) raw 0x65f090 n s 0 _ _ _ _ eq_refl eq_refl eq_refl eq_refl) with (regs0 := R) (regs := R2) (M := MV2)
as (R3 & M3' & RUN & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB & (OA & GR & _)).
1: lia.
1: { left. unfold LOWEND. lia. }
1: exact Hs.
1: { unfold Jb0RegionPoisoned.SB. lia. }
1: { apply (store_ok_mono ASEGS _ (mrestrict H M) MV2); [exact (rd_MV2_grows H M s raw R bs) | exact WOK]. }
1: exact Hret.
1: { unfold rt_layout_globs.
rewrite <- (w_lit 0x1343a0 (0x1343a0%bv : word) eq_refl), <- (w_lit 0x13ca38 (0x13ca38%bv : word) eq_refl),
<- (w_lit 0x1343a8 (0x1343a8%bv : word) eq_refl), <- (w_lit 0x13d728 (0x13d728%bv : word) eq_refl),
<- (w_lit 0x1343b0 (0x1343b0%bv : word) eq_refl), <- (w_lit 0x13d730 (0x13d730%bv : word) eq_refl),
<- (w_lit 0x1343b8 (0x1343b8%bv : word) eq_refl), <- (w_lit 0x13d720 (0x13d720%bv : word) eq_refl).
repeat split; apply CV2; unfold RD_CELLS; cbn [In]; tauto. }
1: { intros _ x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply SHZ. unfold Jb0RegionPoisoned.SB in Hx. change (6680720 / 8) with 0xcbe12 in Hx. lia. }
1: { intros _. apply SHZ. unfold Jb0RegionPoisoned.SB. lia. }
1: { left. reflexivity. }
1: { intros Hn64. unfold Jb0RegionPoisoned.SB.
set (fS := 2147450880 + 6680720 / 8). set (lS := 2147450880 + (6680720 + n - 1) / 8).
assert (FA : fS - fS mod 8 = 0x7fff8000 + 0xcbe10) by reflexivity.
assert (LA : 0x7fff8000 + 0xcbe10 <= lS - lS mod 8 /\ lS - lS mod 8 + 8 <= 0x7fff8000 + 0xcde19).
{ assert (D1 : (6680720 + n - 1) / 8 <= 0xcbe19) by (change 0xcbe19 with ((6680720 + 64 - 1) / 8); apply Z.div_le_mono; lia).
pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as MB. pose proof (Z.div_mod lS 8 ltac:(lia)) as DM.
assert (L0 : 0x7fff8000 + 0xcbe12 <= lS) by (unfold lS; lia).
assert (L1 : lS <= 0x7fff8000 + 0xcbe19) by (unfold lS; lia).
assert (Q : 0x100187c2 <= lS / 8) by (change 0x100187c2 with ((0x7fff8000 + 0xcbe12) / 8); apply Z.div_le_mono; lia).
lia. }
exists (repeat (Z_to_bv 8 0) 8), (repeat (Z_to_bv 8 0) 8). split.
- apply (rdn_of_bytes_at sp0 Hsp); [reflexivity | rewrite u_small by lia; cbn; lia |].
intros j Hj. rewrite u_small by lia. rewrite FA.
replace (nth j (repeat (Z_to_bv 8 0) 8) (Z_to_bv 8 0)) with (Z_to_bv 8 0) by (symmetry; apply nth_repeat).
apply SHZ. lia.
- apply (rdn_of_bytes_at sp0 Hsp); [reflexivity | rewrite u_small by lia; cbn; lia |].
intros j Hj. rewrite u_small by lia.
replace (nth j (repeat (Z_to_bv 8 0) 8) (Z_to_bv 8 0)) with (Z_to_bv 8 0) by (symmetry; apply nth_repeat).
apply SHZ. lia. }
1: { unfold c2_pre. repeat split; assumption. }
1: { unfold FR. split; [intros x _; reflexivity|]. split; [intros x Hx; exact Hx|]. unfold slots_ok. repeat split; assumption. }
1: exact T7.
exists R3, M3'. repeat (split; [assumption|]). split; [|exact GR].
intros x Nx. apply OA. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_aread_site := (ltac2:(TCodec.tc2 tcn__Jb0DrvRead "\2'8'TAyR0%211%411'9y8%611%811p041'S1%;11'S2%=11&Q?y5%221=':%11;p0@1'Q:'<'G%2211%H11&R5%J11&R1&Q5%82H7%N11&RJ'S0(RO&S8rD%211rC%5221&S5r1rA%33251&S4&S9r2&QM&R2r<r@%3221%521:%94871?'@'5&S7&7rG%22QG1rE%5221(=%93821&S6rH%92QN1%3217%>3=16'Du1rI%?2R41%4231rJ(2%Q9221vT=%H3R:21&R=%11?%K3J1C&RF(T?+2(>%33R621%52F1&T@&S;&TC%12RH>r=%4221%62RK1%Q93RK81'?&S<&S@&SA+F%22A1%411r>%7221z%9231%;231&S>r?+@%3221%QJ3RI17rK+:%Q03S31N%Q2231+3%N2SC1%R13SC31rL+;%Q73S:1Q5%Q9231&RA%Q52SJ1%R83SJ31rM+<%Q>3SA1Q<%Q@231rF%Q<2T11%R?3T131+1%Q621R=+RPP0%Q82R?1%Q:231rO%QI3SL6QG%QK221%QF2T;S4%RI3T;21rB%Q@2Q81&S=+R0%QA2R01%3251%QF251%Q;2SAR3%S23T11Q?'R<vSFvLvQBrNrQ1rQ0%7:65RC4E3Q1Q821'Q8%T@11&Q<&Q=%117%321Q@(3(Q9%12QHRO%3291%SE3951%TJ1U3&Q4&Q>rQ2%211%421QI%;2U9S8%SM3721%U21TM&R0%12T8R5%@2U0T>%T23421&Er3rQ<%T32UH1%4231&R>vNrQ5%TN267%S82UO1%554Q931TE%S4271p0=1pX<U?1pX0V11rQ=%T@2V51%A2@1%U823A%SB2V91%S<21TO%S>241p0G1pW@UI1pY:V;1&Q3rQ3%SL2VA1%33QFQG1&4rQ?&RMr4%211%53VG41%UI1UC%UK216%U52VJU@&CrQA%U82VM1uQ0%4221%U>3VN61rQB%U=2W21u:%9221%V62Q?1&Q1%12W3B%UF3W831&RN&F%W=1VO&S3&RC%443W<21rQC%UK2W@1%83E31r8%V?3QM21rQ:r7%V:221%V<215&RBrQ4%24QN1Q;N%VC4VBQ641rQ>rQ;r9%S::S9S8UFS73QKR821=%W>2X0S3%X411%S214&Q;rQ@%S511&TBrQ9%Q22X4F%33X:21%S62F1%836TI1%VJ3;:1&Q2r:%S511%S61QD%VO3421&RH%VN2X?5%24W;W7TK1%SB2X@7%W43S>21%UJ2UBWB%T:2WCT8%UM221&B&SB%V72V5S5+RTH%3221%V221WE%TB2WF4%V5221%811%V62U;S=%V?2U<U0%TG2S?1%V:231%=11%VD2Y9RC%X311rQH%113%WJ3XM31p061p0<1p0F1pW<XM1'RKvT;(Q7&RGvSNrQ8%W32YH1&RI%11X@%655VA3VG1%821W3rQ7%<4XD;21p0>1p0Q91p0Q?1p0QE1p0R31p0R81p0RA1p0RM1p0S61tQDY:S>1tY>Z7SA1tWDZ4SH1pX8YI1pS4YK1pSFYO1+\[X8%WJ2Z?1%K5JI1CFrQ6%N221%Q14Y9Q01X?p071p0T71p0TB1p0U71p0U@1p0UL1p0V51p0V81p0V@1p0VF1p0VL1p0W41p0W<1p0WD1p0WJ1p0X71p0XF1p0XJ1p0Y01p0Y61p0Y<1p0YG1p0Z21tQBZ=Z71pQLZ?1pXBZI1pY@ZB1pWBZC1pXJZL1pWJ[;1pX>[A1pX@ZI1pWF[01p2ZO1pWHZM1pR2ZO1pR0[21pX6[71pS2[91pSD[=1pX4[A1pXN[D1pWL[G1pY<[M1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_aread_site) 0%nat 0%nat).
Variable ebs : ltac:(sec_ty2 constr:(SEC_T_aread_site) 1%nat 0%nat).
Variable sr : ltac:(sec_ty2 constr:(SEC_T_aread_site) 2%nat 0%nat).
Variable kn : ltac:(sec_ty2 constr:(SEC_T_aread_site) 3%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_aread_site) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_aread_site) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_aread_site) 6%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_aread_site) 7%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_aread_site) 8%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_aread_site) 9%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_aread_site) 10%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_aread_site) 11%nat 0%nat).
Variable pth : ltac:(sec_ty2 constr:(SEC_T_aread_site) 12%nat 0%nat).
Variable off : ltac:(sec_ty2 constr:(SEC_T_aread_site) 13%nat 0%nat).
Variable data : ltac:(sec_ty2 constr:(SEC_T_aread_site) 14%nat 0%nat).
Variable so : ltac:(sec_ty2 constr:(SEC_T_aread_site) 15%nat 0%nat).
Variable bls : ltac:(sec_ty2 constr:(SEC_T_aread_site) 16%nat 0%nat).
Variable vbnd : ltac:(sec_ty2 constr:(SEC_T_aread_site) 17%nat 0%nat).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_aread_site) 18%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_aread_site) 19%nat 0%nat).
Lemma aread_site : ltac:(sec_stmt2 constr:(SEC_T_aread_site) 20%nat 0%nat).
Proof.
intros E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R10 R11 R12 Hcnt R1 Hra Hra2 DI Hfd Hfsl Hbl Hvb CONT.
pose proof Hsp as Hsp'. unfold STAGE in *.
set (s := bv_unsigned sp0 + so) in *. set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
destruct (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HOFF & HLC & HAWF & _ & _). fold H in HOFF, HLC.
assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by (unfold s; lia).
assert (WOK : store_ok ASEGS MV (Z_to_bv 64 (s - 2200)) 2200 = true).
{ replace (s - 2200) with (bv_unsigned sp0 + (so - 2200)) by (unfold s; ring).
apply (window_store_ok sp0 vals ebs MV kn (so - 2200) 2200 HK Hiw P0); lia. }
assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); unfold s in Hx; lia. }
assert (VST : forall x : word, 0x65f090 <= bv_unsigned x < 0x65f090 + 65536 -> H x = false).
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
assert (CV : forall a n v, In (a, n, v) RD_CELLS ->
rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
{ intros a n v Hin. unfold MV, H. rewrite rdn_mrestrict_eq; [exact (rd_cell _ _ _ _ _ _ _ a n v HH Hin)|].
apply (avoid_img _ _ _ _ _ _ _ a (Z.to_nat n) HH);
unfold RD_CELLS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]); destruct Hin. }
destruct (wrap_read_pre_run MV (seg_rom ASEGS) (Z_to_bv 64 s) (Z_to_bv 64 ra) s 3 0x65f090 cnt
ltac:(apply u_small; lia) Hs WOK ltac:(lia) ltac:(lia) ltac:(lia)) with (regs := R)
as (Ra & RUN1 & A17 & A10 & A11 & A12 & _ & _ & _ & _ & A2 & A1 & A8 & A9 & A18 & A19 & A20 & KB1).
1: { rewrite <- (w_lit 0x13d718 (0x13d718%bv : word) eq_refl). exact (CV 0x13d718 1 1 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
1: { rewrite <- (w_lit 0x1361f8 (0x1361f8%bv : word) eq_refl). exact (CV 0x1361f8 8 0x12d1e8 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
1: exact R10. 1: exact R11. 1: exact R12. 1: exact R2. 1: exact R1.
rewrite (w_lit 0x62d08 (0x62d08%bv : word) eq_refl).
apply (rz_msteps_lz ASEGS scfg H A R _ M Ra _ _ model K HOFF asegs_wx HLC HAWF HMI Hh RUN1).
intros model1 MI1 SBM1 EQV1.
destruct (sbm_fds _ _ SBM1) as (F1 & F2).
eapply (rz_read_file_lz ASEGS scfg Ra _ _ model1 ECALLW (Z_to_bv 64 3) pth off data cnt K); try apply is_ecall_ECALLW.
- vm_compute. reflexivity.
- rewrite (sbm_halted_eq _ _ SBM1). exact Hh.
- exact A17.
- exact A10.
- rewrite u_small by lia. lia.
- rewrite F1. exact Hfd.
- rewrite F2. exact Hfsl.
- exact A12.
- lia.
- lia.
- lia.
- rewrite A11.
apply (store_ok_window ASEGS _ (Z_to_bv 64 0x65f090) (Z_to_bv 64 0x65f090) 65536%nat (Z.to_nat cnt) 0x65f090 0x66f090);
first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
- rewrite A11, u_small by lia. unfold TASK_SIZE. lia.
- rewrite A11, (sbm_lazy_eq _ _ SBM1).
apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ model _ _ HH); [rewrite u_small by lia; lia|].
intros k Hk. left. rewrite u_small by lia. lia.
- cbv zeta. rewrite A11, A12.
set (bs := file_read data off (Z_to_bv 64 cnt)).
set (n := Z.of_nat (length bs)).
assert (Hn : 0 <= n <= 65536).
{ unfold n, bs. rewrite length_file_read. unfold word_to_nat. rewrite (u_small cnt) by lia. lia. }
replace (v_addi (0x1277bc%bv : word) 4) with (0x1277c0%bv : word) by (apply bv_eq; reflexivity).
set (raw := Z_to_bv 64 ra) in *.
set (M2 := wbytes (munrestrict H M (RDA MV raw s R)) (Z_to_bv 64 6680720) bs).
set (R2' := regupd Ra 10 (len_word bs)).
set (model2 := with_fds (fd_insert (m_fds model1) (Z_to_bv 64 3) (FdFile pth (off + len_word bs))) model1).
assert (EL2 : m_vm_lazy model2 = m_vm_lazy model) by (unfold model2; rewrite with_fds_vm_lazy; exact (sbm_lazy_eq _ _ SBM1)).
assert (EH2 : ahid A model2 = H) by (unfold H; apply ahid_same_lazy; exact EL2).
assert (Hh2 : m_halted model2 = None) by (unfold model2; rewrite with_fds_halted'; rewrite (sbm_halted_eq _ _ SBM1); exact Hh).
assert (MI2 : MInv A model2) by (apply (minv_same_vm A model1 model2); [unfold model2; apply with_fds_vm | exact MI1]).
assert (Hbs : Z.of_nat (length bs) <= 65536) by (fold n; lia).
destruct (rd_post LB [] LK cr A M model s raw R R2' bs HH Hbs ltac:(unfold s; lia) WOK ltac:(apply ret_ok_even; unfold raw; rewrite u_small by lia; exact Hra2))
as (R3 & M3' & RUN3 & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB3 & OUT3 & GR3).
1: { unfold R2'. rewrite getr_same by discriminate. reflexivity. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A2. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A1. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A8. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A9. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A20. }
unfold rd_MV2 in RUN3, OUT3, GR3. fold H in RUN3, OUT3, GR3. fold MV in RUN3, OUT3, GR3. unfold STAGE in RUN3, OUT3, GR3. fold M2 in RUN3, OUT3, GR3.
apply (rz_msteps_lz ASEGS scfg H A R2' _ M2 R3 _ M3' model2 K HOFF asegs_wx ltac:(rewrite EL2; exact HLC) HAWF MI2 Hh2 RUN3).
intros model3 MI3 SBM3 EQV3.
set (M3 := munrestrict H M2 M3') in *.
assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (s - 2200 <= a < s) -> ~ (0x65f090 <= a < 0x65f090 + 65536) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N1 N2. unfold M3, munrestrict.
assert (E2 : M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ unfold M2, MV. apply (rd_M2_out H M s raw R bs Hs Hbs); rewrite u_small by lia; unfold STAGE; lia. }
destruct (H (Z_to_bv 64 a)) eqn:Hx; [exact E2|].
rewrite OUT3 by (rewrite u_small by lia; lia). unfold mrestrict. rewrite Hx. exact E2. }
assert (GRW : forall x : word, M x <> None -> M3 x <> None).
{ intros x Hd. unfold M3, munrestrict.
assert (E2 : M2 x <> None) by (unfold M2, MV; apply (rd_M2_grows H M s raw R bs); exact Hd).
destruct (H x) eqn:Hx; [exact E2|]. apply GR3. unfold mrestrict. rewrite Hx. exact E2. }
assert (EV3 : vml_of model3 = vml_of model).
{ rewrite (sbm_vml _ _ SBM3). unfold model2. rewrite (vml_same_vm model1 _ (with_fds_vm _ model1)). exact (sbm_vml _ _ SBM1). }
assert (Hh3 : m_halted model3 = None) by (rewrite (sbm_halted_eq _ _ SBM3); exact Hh2).
assert (EH3 : ahid A model3 = H) by (rewrite (ahid_sbm A model2 model3 SBM3); exact EH2).
assert (DI3 : dinvA LB LK cr A M3 model3).
{ apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M3 model model3 DI); [ | exact GRW | exact EV3 | exact MI3 | exact Hh3].
intros a Ha NC. apply FRM; [exact Ha | |]; intros Hr; apply NC; unfold CWA.
- right. left. unfold s in Hr. lia.
- right. right. exists 0x65f090, 0x670a68. split; [unfold IMG_W_A; cbn [In]; tauto | lia]. }
assert (HL' : length (vals ++ junk_vals R3) = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R3) 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (KEPT : forall r : reg, In r c_kept -> getr R3 r = getr R r).
{ assert (KK : forall r : reg, In r callee_saved -> ~ In r Jb0ReadIcpt.RIPL -> getr R3 r = getr R r).
{ intros r Hr Hn'. rewrite (KB3 r Hr Hn'). unfold R2'. rewrite getr_other; [exact (KB1 r Hr Hn')|].
intros ->. clear - Hr. cbv in Hr. intuition discriminate. }
intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
- rewrite O2, R2. reflexivity.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- exact O8.
- exact O9.
- exact O18.
- exact O19.
- exact O20.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate. }
apply (CONT R3 M3 model3 HL').
+ rewrite (vals_ev_junkA vals R3 10) by lia. exact O10.
+ exact (regs_after_keeps vals ebs sr R R3 c_kept Hsv HR KEPT c_kept_no0A).
+ rewrite EH3. unfold keep_readA.
pose proof (env_app_know ASEGS vals (junk_vals R3) ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 2200 bls vbnd [] IMG_NOSTAGE IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R3)) ebs)
(fun a => H (Z_to_bv 64 a) = false /\ ~ (s - 2200 <= a < s) /\ ~ (0x65f090 <= a < 0x65f090 + 65536))
(fun a => s - 2200 <= a < s)
_ MV (mrestrict H M3) _ _ kn HK1).
* assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x693000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) -> H (Z_to_bv 64 a) = false)
by (intros a Ha Hc; exact (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha Hc)).
constructor; cbn [ev]; rewrite ?P0'.
-- lia.
-- lia.
-- intros z Hz Hnot. split; [apply VIS; lia|]. unfold s. split; lia.
-- intros z Hz. right. unfold s. lia.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & SBk). rewrite vals_ev_app_l by exact Hi32.
pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ SBk) as (Z1 & Z2 & Z3).
destruct SBk as (cap & Hnb & Hin & HB).
split; [lia|]. intros z Hz. split; [|unfold s; split; lia].
apply VIS; [lia|]. right. right. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin | cbn [fst snd]; lia].
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros i [].
-- intros lo hi Hin. unfold IMG_NOSTAGE in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; (split; [apply VIS; lia | unfold s; split; lia])|]).
destruct Hin.
-- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
intros Mx d m Hd Hm.
apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x65f090) (Z_to_bv 64 d) 65536%nat m 0x65f090 0x66f090);
first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
* intros a Ha (V1 & N1 & N2). unfold MV, mrestrict. rewrite V1. apply FRM; assumption.
* intros a Ha. unfold mrestrict. rewrite (VFR (Z_to_bv 64 a)) by (rewrite u_small by (unfold s in Ha; lia); exact Ha).
apply GRW. apply (window_defined sp0 Hsp vals ebs H M kn HK Hiw P0). unfold s in Ha. lia.
+ exact DI3.
+ rewrite (proj1 (sbm_fds _ _ SBM3)). unfold model2. rewrite with_fds_fds, F1. reflexivity.
+ rewrite (proj2 (sbm_fds _ _ SBM3)). unfold model2. rewrite with_fds_fs. exact F2.
+ fold bs. rewrite <- (rd_stage_bytes H M s raw R bs Hbs). unfold STAGE. fold MV. fold M2.
apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
unfold M3, munrestrict. rewrite (VST x) by lia. rewrite OUT3 by lia. unfold mrestrict. rewrite (VST x) by lia. reflexivity.
+ exact FRM.
Qed.
End SE.
End DrvRead.
End FPX_1.
