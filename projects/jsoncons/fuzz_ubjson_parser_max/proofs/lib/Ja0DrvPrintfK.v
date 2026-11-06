(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib Ja0DrvRead Ja0DrvPiece Ja0DrvStdio.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require L5Defs L5KnA ArtMem JatFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ja0DrvP_dpA2 Ja0DrvP_dpA3 Ja0DrvP_dpA4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvPrintfK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvPrintfK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.Ja0DrvP_dpA2.AS0DRVP_dpA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.Ja0DrvP_dpA3.AS0DRVP_dpA3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.Ja0DrvP_dpA4.AS0DRVP_dpA4."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0K"]; ["0LB"; "0LK"; "4store_ok"; "4word_to_le_bytes"; "5mkCfg"; "6Model"; "7bvmap"; "0M"; "0M0"; "0M1"; "0MV"; "0R"; "0R'"; "8mrestrict"; "8same_but_materialized"; "9credit"]; [":ahid"; ":fframe"; ";dinv"; "<Wpf"; "<stdoutA"; "=FPState"; "=getr"; "=mkst"; "=rdn"; "=seg_rom"; ">TSet"; "?srealizes"; "@KS_dpA2"; "AKS_dpA3"; "BKS_dpA4"; "Cloaded_segments"]; ["0S"; "DIn"; "Eadd"; "Ele"; "Elt"; "Emodulo"; "Eof_nat"; "Epow"; "Esub"; "0a"; "0ar"; "0canz"; "0cr"; "0d"; "0fx"; "0fx'"]; ["0i"; "0k"; "0model"; "0model1"; "0n"; "0scfg"; "0sp0"; "FBV"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Definition SOBUF : Z := 6878624.
Definition stdoutA (j : Z) (MV : word -> option byte) : Prop :=
rdn ASEGS MV (Z_to_bv 64 1273648) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5))
/\ rdn ASEGS MV (Z_to_bv 64 1273744) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))
/\ rdn ASEGS MV (Z_to_bv 64 1273680) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (SOBUF + 1024)))
/\ rdn ASEGS MV (Z_to_bv 64 1273688) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (SOBUF + 2 * j)))
/\ rdn ASEGS MV (Z_to_bv 64 1273704) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))
/\ rdn ASEGS MV (Z_to_bv 64 1273788) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn ASEGS MV (Z_to_bv 64 1273792) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ (forall a n, 1273648 <= a -> a + n <= 1273648 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
/\ (forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
/\ (forall i, 0 <= i < j -> rdn ASEGS MV (Z_to_bv 64 (SOBUF + 2 * i)) 1 = Some [Z_to_bv 8 48] /\ rdn ASEGS MV (Z_to_bv 64 (SOBUF + 2 * i + 1)) 1 = Some [Z_to_bv 8 10]).
Definition Wpf (S j a : Z) : Prop :=
S - 3232 <= a < S \/ 1273648 <= a < 1273652 \/ 1273688 <= a < 1273696 \/ SOBUF + 2 * j <= a < SOBUF + 2 * j + 2.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section PrintfK.
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
Hypothesis Hpr : incl PR_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
#[local] Notation rom := (seg_rom ASEGS).
Section SE.
Local Abbreviation SEC_T_printf2_run := (ltac2:(TCodec.tc2 tcn__Ja0DrvPrintfK "XD'4'7'=%2211%411&Q1%611&O'R9yR0%211'6y8%511%311p051'E&Fy5%2219&Q:'Q2vQJv>vR6vHr:r9r8r7r6r5%;::987654321&M&Q0%1275%3217&QC&QH&R:%12O@+TP0%4221%621<&QB+Q0%22@1%:217';&QE+@%22F1z%53QC21':%B23J&QD&QG+2+R0%3221%52Q01%8271&Q6(R7+1(9%33QA21%52Q:1&R8+dmb0%22QN1%H3QN41r;%:3QH@8%<221%72R3QB%M3R321r<+:%@3QN1>%B231+Rcf<%>2R:1%Q43R:31r=+;%G3R51E%I231+H%Q>2<1%F2RB1%Q<3RB41+XPPP0%QH2QF1r2%QK221r3%QF213%QN21QK'5%R02QA6&QF%118%QL271%R421R;'3&B&Q?rAr4%R32RC1%Q;2S71%64541@(8%R33921p0;1p0@1pT4B1pSLSE1p0E1p0I1pT:SH1pSDSI1+RPP0r1%RI221+QV`P0%R8231%R;231%QM2SIQ3%QE11(1%11SH%RF3SH31p061pT2T61%T91SL%SO11&Q8+Vak^0%R82T41u8%44Q3R621(2&Cr>%R>2T:1%3261%52<1%S63<71r@%S<21QO%RD2T@1u4%@4Q?R=21%RG2TCS8%<231%>2E1%S?3E41&Q4%12S=R<'Q5rMrLrKrJ%TB:TAT@T?T>4321R8Q:&NrI%221R;&QA&Q<%23R9Q@1%S92TLR7%S@2TB1%SA2;2%T13U721p051pTHR?1%SE2TFS4%S@2U<SK%T63U<21rN%TF21TI%TH21TK%J2SI1%TF2T7QN%T42QOT0%T7221&<&Q3%13MT<S1%311%SM2UIS1%U911rQ1%113%TF3UH31p061p0;1pSDV71%;3CTFS;%=11rQ3%U;21UC%U=31T5<%Q:1=%U03V221p061p0E1pSDVA1%Q>1RG%U53V71R@%H11%UF3:T>SH%U83V:1RC%K11p041pSDVA1'Q;vR5(D&Q7&Q9%11SE%35TDTITKV81%521V8%84SH71R0p0:1p0C1p0N1p0Q>1p0QC1p0QG1p0R11p0R51pT8VM1pQDVO1pQJVL1pT0R>1vQNrD+\ZbD%U?2W;1rF%G55421ErE%J221%M4T=L1T<p0:1p0RJ1p0RM1p0S71p0SF1p0T41p0U41p0U=1p0UE1p0UK1p0V61p0V@1p0VG1p0VL1tQFWIW41p0W91pQ0WF1pSHX91pS2X:1pQHWJ1pT6WN1pQ@X01p2X<1pSJX:1pQ4X<1pQ2X?1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 6%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 7%nat 0%nat).
Variable canz : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 8%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_printf2_run) 9%nat 0%nat).
Lemma printf2_run : ltac:(sec_stmt2 constr:(SEC_T_printf2_run) 10%nat 0%nat).
Proof using L C IL HIok ICok ILY Hsp DL Hpr LB LK cr A M model R S canz K.
intros D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
destruct (AS0DRVP_dpA2.dpA2_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
all: cbn [V].
all: try assumption.
all: try (clear - Hsp' HS1 HS2 Hcan; lia).
- intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
- intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
-
intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
-
apply JatFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14ec0 64 _ D); [lia | lia | lia | | lia].
rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply JatFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x68f580 64 _ D); [lia | lia | lia | | lia].
rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- intros d k Hd Hk. apply (FW 1273648 4); lia.
- intros d k Hd Hk. apply (FW 1273688 8); lia.
- intros d k Hd Hk. apply (BW 6878624 1); unfold SOBUF; lia.
- intros d k Hd Hk. apply (BW 6878625 1); unfold SOBUF; lia.
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- exact (PC 0x13acf8 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x1344c0 8 0x1224a8 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x1344c8 8 0x11c1c4 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- exact (PC 0x134640 8 0x1249ac ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x134648 8 0x124db0 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
-
unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x62a54) R' (Z_to_bv 64 0xa7640) MV' (Wpf S 0) K D MS GR FRW).
+ intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
* exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
* exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
* exists 0x66edb0, 0x690238. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
+ intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
rewrite VIS. unfold stdoutA.
assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 0 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [exact O2|].
split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
intros i Hi. destruct (Z.eq_dec i 0) as [->|N]; [split; [exact O4 | exact O3]|].
destruct (BC i ltac:(lia)) as (B1 & B2).
split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
Qed.
End SE.
#[using="L C IL HIok ICok ILY Hsp DL Hpr"] Lemma printf3_run : ltac2:(TCodec.tc2 tcn__Ja0DrvPrintfK "XD'4'7'=%2211%411&Q1%611&O'R9yR0%211'6y8%511%311p051'E&Fy5%2219&Q:'Q2vQJv>vR6vHr:r9r8r7r6r5%;::987654321&M&Q0%1275%3217&QC&QH&R:%12O@+TP0%4221%621<&QB+Q0%22@1%:217';&QE+@%22F1z%53QC21':%B23J&QD&QG+2+R0%3221%52Q01%8271&Q6(R7+1(9%33QA21%52Q:1&R8+dmb0%22QN1%H3QN41r;%:3QH@8%<221%72R3QB%M3R321r<+:%@3QN1>%B231+Rcf<%>2R:1%Q43R:31r=+;%G3R51E%I231+H%Q>2<1%F2RB1%Q<3RB41+XPPP0%QH2QF1r2%QK221r3%QF213%QN21QK'5%R02QA6&QF%118%QL271%R421R;'3&B&Q?rAr4%R32RC1%Q;2S71%64541@(8%R33921p0;1p0@1pT4B1pSLSE1p0E1p0I1pT:SH1pSDSI1+RPP0r1%RI221+QV`P0%R8231%R;231%QM2SIQ3%QE11(1%11SH%RF3SH31p061pT2T61%T91SL%SO11&Q8+Vak^0%R82T41u8%44Q3R621(2&Cr>%R>2T:1%3261%52<1%S63<71r@%S<21QO%RD2T@1u4%@4Q?R=21%RG2TCS8%<231%>2E1%S?3E41&Q4%12S0R<'Q5rMrLrKrJ%TB:TAT@T?T>4321R8Q:&NrI%221R;&QA&Q=%23R9Q@1%S92TLR7%S@2TB1%SA2;2%T13U721p051pTHR?1%SE2TFS4%S@2U<SK%T63U<21rN%TF21TI%TH21TK%J2T01%TF2T7QN%T42QOT0%T7221&<&Q3%13MSOS1%311%SM2UIS1%U911rQ1%113%TF3UH31p061p0;1pSDV71%;3CT9S;%=11rQ3%U;21UC%U=31T5<%Q:1=%U03V221p061p0E1pSDVA1%Q>1RG%U53V71R@%H11%UF3:T>SH%U83V:1RC%K11p041pSDVA1'Q;vR5(D&Q7&Q9%11SE%35TDTITKV81%521V8%84SH71R0p0:1p0C1p0N1p0Q>1p0QC1p0QG1p0R11p0R51pT8VM1pQDVO1pQJVL1pT0R>1vQNrD+\ZbD%U?2W;1rF%G55421ErE%J221%M4T=L1T<p0:1p0RJ1p0RM1p0S71p0SF1p0T41p0U41p0U=1p0UE1p0UK1p0V61p0V@1p0VG1p0VL1tQFWIW41p0W91pQ0WF1pSHX91pS2X:1pQHWJ1pT6WN1pQ@X01p2X<1pSJX:1pQ4X<1pQ2X?1").
Proof.
intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
destruct (AS0DRVP_dpA3.dpA3_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
all: cbn [V].
all: try assumption.
all: try (clear - Hsp' HS1 HS2 Hcan; lia).
- intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
- intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
-
intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
-
apply JatFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14ec0 64 _ D); [lia | lia | lia | | lia].
rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply JatFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x68f580 64 _ D); [lia | lia | lia | | lia].
rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- intros d k Hd Hk. apply (FW 1273648 4); lia.
- intros d k Hd Hk. apply (FW 1273688 8); lia.
- intros d k Hd Hk. apply (BW 6878626 1); unfold SOBUF; lia.
- intros d k Hd Hk. apply (BW 6878627 1); unfold SOBUF; lia.
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- exact (PC 0x13acf8 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x1344c0 8 0x1224a8 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x1344c8 8 0x11c1c4 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- exact (PC 0x134640 8 0x1249ac ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x134648 8 0x124db0 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
-
unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x62a54) R' (Z_to_bv 64 0xa7640) MV' (Wpf S 1) K D MS GR FRW).
+ intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
* exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
* exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
* exists 0x66edb0, 0x690238. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
+ intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
rewrite VIS. unfold stdoutA.
assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 1 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [exact O2|].
split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
intros i Hi. destruct (Z.eq_dec i 1) as [->|N]; [split; [exact O4 | exact O3]|].
destruct (BC i ltac:(lia)) as (B1 & B2).
split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
Qed.
#[using="L C IL HIok ICok ILY Hsp DL Hpr"] Lemma printf4_run : ltac2:(TCodec.tc2 tcn__Ja0DrvPrintfK "XE'4'7'=%2211%411&Q1%611&O'R9yR0%211'6y8%511%311p051'E&Fy5%2219&Q:'Q2vQJv>vR6vHr:r9r8r7r6r5%;::987654321&M&Q0%1275%3217&QC&QH&R:%12O@+TP0%4221%621<&QB+Q0%22@1%:217';&QE+@%22F1z%53QC21':%B23J&QD&QG+2+R0%3221%52Q01%8271&Q6(R7+1(9%33QA21%52Q:1&R8+dmb0%22QN1%H3QN41r;%:3QH@8%<221%72R3QB%M3R321r<+:%@3QN1>%B231+Rcf<%>2R:1%Q43R:31r=+;%G3R51E%I231+H%Q>2<1%F2RB1%Q<3RB41+XPPP0%QH2QF1r2%QK221r3%QF213%QN21QK'5%R02QA6&QF%118%QL271%R421R;'3&B&Q?rAr4%R32RC1%Q;2S71%64541@(8%R33921p0;1p0@1pT4B1pSLSE1p0E1p0I1pT:SH1pSDSI1+RPP0r1%RI221+QV`P0%R8231%R;231%QM2SIQ3%QE11(1%11SH%RF3SH31p061pT2T61%T91SL%SO11&Q8+Vak^0%R82T41u8%44Q3R621(2&Cr>%R>2T:1%3261%52<1%S63<71r@%S<21QO%RD2T@1u4%@4Q?R=21%RG2TCS8%<231%>2E1%S?3E41&Q4%12S7R<'Q5rMrLrKrJ%TB:TAT@T?T>4321R8Q:&NrI%221R;&QA&Q>%23R9Q@1%S92TLR7%S@2TB1%SA2;2%T13U721p051pTHR?1%SE2TFS4%S@2U<SK%T63U<21+3rN%TG21TJ%TI21TL%K241%TG2T8QO%T52R0T1%T8221&<&Q3%13NT7S2%311%SN2UJS2%U:11rQ1%113%TG3UI31p061p0;1pSDV81%;3CTAS<%=11rQ3%U<21UD%U>31T6<%Q;1=%U13V321p061p0E1pSDVB1%Q?1RH%U63V81RA%H11%UG3:T?SI%U93V;1RD%K11p041pSDVB1'Q;vR5(D&Q7&Q9%11SF%35TETJTLV91%521V9%84SI71R1p0:1p0C1p0N1p0Q>1p0QD1p0QH1p0R21p0R61pT8VN1pQDW01pQJVM1pT0R?1vQNrD+\ZbD%U@2W<1rF%G55421ErE%J221%M4T>L1T=p0:1p0RK1p0RN1p0S81p0SG1p0T51p0U51p0U>1p0UF1p0UL1p0V71p0VA1p0VH1p0VM1tQFWJW51p0W:1pQ0WG1pSHX:1pS2X;1pQHWK1pT6WO1pQ@X11p2X=1pSJX;1pQ4X=1pQ2X@1").
Proof.
intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
destruct (AS0DRVP_dpA4.dpA4_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
all: cbn [V].
all: try assumption.
all: try (clear - Hsp' HS1 HS2 Hcan; lia).
- intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
- intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
-
intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
-
apply JatFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14ec0 64 _ D); [lia | lia | lia | | lia].
rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply JatFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x68f580 64 _ D); [lia | lia | lia | | lia].
rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- intros d k Hd Hk. apply (FW 1273648 4); lia.
- intros d k Hd Hk. apply (FW 1273688 8); lia.
- intros d k Hd Hk. apply (BW 6878628 1); unfold SOBUF; lia.
- intros d k Hd Hk. apply (BW 6878629 1); unfold SOBUF; lia.
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- exact (PC 0x13acf8 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x1344c0 8 0x1224a8 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x1344c8 8 0x11c1c4 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
- exact (PC 0x134640 8 0x1249ac ltac:(unfold PR_CELLS; cbn [In]; tauto)).
- exact (PC 0x134648 8 0x124db0 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
-
unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x62a54) R' (Z_to_bv 64 0xa7640) MV' (Wpf S 2) K D MS GR FRW).
+ intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
* exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
* exists 0x136e40, 0x137140. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
* exists 0x66edb0, 0x690238. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
+ intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
rewrite VIS. unfold stdoutA.
assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 2 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [exact O2|].
split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
intros i Hi. destruct (Z.eq_dec i 2) as [->|N]; [split; [exact O4 | exact O3]|].
destruct (BC i ltac:(lia)) as (B1 & B2).
split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
Qed.
End PrintfK.
End FPX_1.
