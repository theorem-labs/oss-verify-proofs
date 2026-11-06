(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP FpBound FpReal FpSiteB ExpfModelB ExpfTablesB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk D_iface D_defs Bi_iface Bi_iface2 Bi_fktw BiV_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_BiV_iface () := "I47Corelib5Lists7ListDef6Forall00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib;ExpfTablesB<bil_gauss_FBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B029BiV_iface6gcellVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7FpBound2FBC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv3Fpu:fmt_singleC69OSSVerify5KrLib2K53Lib;ExpfTablesB@bil_gauss_centreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6FpReal7p_one_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib;ExpfTablesB=bil_range1_FBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B029BiV_iface6rcellVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib;ExpfTablesBAbil_range1_centreC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B029BiV_iface5kflipC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gcellV (kk q : Z) : Z := gauss_cell DEN_GAUSS_D p_one_s ((kk - 20) * (kk - 20) + (q - 20) * (q - 20)).
(* [comment removed for export] *)
Definition rcellV (kk q : Z) : Z := bil_cell DEN_RANGE1 q.
(* [comment removed for export] *)
Definition kflip (sy sx : Z) (f : Z -> Z -> Z) (i j : Z) : Z := f (sy - 1 - i) (sx - 1 - j).

Lemma gcellV_FB : forall kk q, 0 <= kk < 41 -> 0 <= q < 41 -> FB fmt_single 1 (gcellV kk q).
Proof.
ltac2:(KReplay.run1 (kr_t_BiV_iface ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with64__x2h71xh81Ah91Bh:1Hh;2Hkh<2Hqh=2Hxh>2SQh?2kkh@1qp;1p;2p;4p;3p;6p;7p;8p-1p10000p4p710p8g000Qj12Tg0016j1>Tg001[j1;Tg0029j2GTg002Uj21Tg0030j2:Tg003Mj28Tg003jj2?Tg004Gj1TTg004ej24Tg005Aj2RTg005jj2ITg006Kj4jTg006lj2OTg007Uj1ATg0084j2=Tg008]j3[Tg009>j2ETg009jj1YTg00:Jj3DTg00:jj1XTg00;Jj2JTg00;hj1WTg00<Fj4VTg00<dj1UTg00=Bj1STg00=mj2KTg00>Pj2<Tg00?3j1QTg00?Uj3@Tg00@8j2PTg00@Zj2iTg00A4j2hTg00A`j3gTg00B:j3fTg00BYj4eTg00CKj3MTg00Cnj3FTg00DQj4cTg00E<j4bTg00EWj2^Tg00F[j2]Tg00GWj3_Tg00HMj3\Tg00I6j3`Tg00I_j6aTg00JCj4NTg00Jnj7LTg00KRj7dTg00L6j8ZTg00LZR0f0R1'4p=3g00M8R2f1R3;\1p=7A`231p=6P3g00MVR4g00N5R5P5g00NUR6P1Eap=HP2P3g00O5P1CNp=CP3P4P5P5P6P1g00O\R7FLp=Bf2R8P4P5P5P6P3P1Fdp=5P8P4P5P5P6P2P3g00P<P1CNP7FLp=0f3R7P4P5P5P6P8P3P1GZp=9%33g00PcR4#2R9#>#2#2R:#>#;R;,G3R<'1R=%;:R>,:7R?/8?R?1:8>R@/8@R@'?%T:RA/41RB141>RC'1RD1833RE#3RF%>4#2#2#>#2#2#2#2RG#;RH,4EREp-0RIg00QHRJ%2:#2#;,R2R:P2%;4RK,I2P41I20CjRL,O2RMg00R4RN#ARO,=2RP'7'7A[24L,O2RL/7M1=2NRN,7L17PP17PN,7:'6'6'6'6g00RSR:'E%YJRL3D%XJRMP21J28P3%W2CVRQ%U2RR%S2RSf4RT,HS1K29R91<2;RU'C,BS55S%Q5R51<20RV1K24R4=@24RW50SC91PS6R6P1P8g00S?RXg00S_RY'i1h18=gXYdAf203CeR0b2b4b5X02X62W3118<PF[^02^62^3IP1f6R<#3P<P8PTO4b11?3>RY1:>3RXPLPM1J23RZPRPS1<2AR[=0S41HS7R\55SP51<2>R]9M24R^90SVC9P6P0b2b4b5X02X3I11B3%3Y[^02^3IP1148>P8P3O3b1PLPMPZPRPSA0S4]95S\P5AF2]4R\90SVC9P6P0b2b4b5X02X3I113C%3X[^02^3IP114A8P8P3O3b1Cc18YX#3PLPMPZPRPSA@2^\90SVP51<2HR\90SWC9P6P0b2b4b5X021?1>1:>1'8#3PE[^02P1P7P3O2b1b:CbW=X7211FE\D^72P11:T>RTPLPMPZPRPSA0SV41C4U,BS55SP5AF24]R490S[A0S4]55SC9P6P0b2b4b5X02%311G1;'11:3>R;,4A14;>'1[^02P1f5P7O2b1R>O218TTRA#314AH'1RAP3PTP>O2PA%AORO#ARA#A,=21=2O/6N'6/E:1=2A16PN'6/E:=DJL5DJPMPQPRPSAF29]R]=@2]R]90SVA0S]\55SP5PSA@244R490SVA0S4\55SP5AM24]R490SV%>G#;RG,<2,C4,BS55SC9C9P6P0b2b4b5X02X6218;;R;#314;H'1R;1?@?R@#31G@G'1\;[^02^62P1P<f7P3P8O4b1b9b8b>'^g00T?1]787_KeX<=W;X@2X?2o"). Qed.
Lemma gcellV_centre : gcellV 20 20 = p_one_s.
Proof.
ltac2:(KReplay.run1 (kr_t_BiV_iface ()) [] "p;1p;2p;3g000Qj10Tg0016j14Tg001[j12Tg00F[j21Tg00A`j33Tg00Tlg00M8g00Pc#0#4#0#0#2R0/10g00V433eo"). Qed.
Lemma rcellV_FB : forall kk q, 0 <= q < 256 -> FB fmt_single 1 (rcellV kk q).
Proof.
ltac2:(KReplay.run1 (kr_t_BiV_iface ()) [] "h02Hqh12kkh21qp;2p;1p;3g004ej27Tg000Qj10Tg001[j11Tg0029j22Tg002Uj26Tg00Vnj25Tg00X3j24Tg00GWj33Tg00M8R0g00LZf0R1'7g00PcR2#0#0#0#0#0#0#0#0#1,21'6f1R3/51g00T?%12f2/4333eW0X20W1o"). Qed.
Lemma rcellV_centre : forall kk, rcellV kk 0 = p_one_s.
Proof.
ltac2:(KReplay.run1 (kr_t_BiV_iface ()) [] "h02kkp;2p;3g00X3j21Tg00A`j30Tg00M8R0g00Xof0g00LZ'1g00V4500eW0o"). Qed.
Lemma kflip_centre : forall f, kflip 41 41 f 20 20 = f 20 20.
Proof.
ltac2:(KReplay.run1 (kr_t_BiV_iface ()) [] "h01fp;1p;2p;5p;3g000Qj10Tg0016j12Tg001[j11Tg00@Zj23Tg00Z8j55Tg00A`j34Tg00M8R0P0\0[f0R1g00Pc#0#2#0#0R2#1R3P3O2R4,30%22#1R2P2P1P3P3D5=404eW0o"). Qed.

Section BiVIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition expf_cpsV : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w : bv 32),
  fdfs_only PMc -> mat_stable PMc -> lenv RT Σ m sp lo (LSTK 1) -> reg_get F r_fa0 = nan_box w ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_expf m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v F m' ms
          /\ reg_get (ms_fregs ms) r_fa0 = nan_box (Z_to_bv 32 (expf_model w))
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition kernelSetElement_cpsV : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kel sy sx cy cx data i j rp : Z) (x0 : word) (v : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kel -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 j ->
  0 <= i < sy -> 0 <= j < sx -> sy < 2^31 -> sx < 2^31 ->
  rw_cells asegs m kel (kel_cells sy sx cy cx data) -> chunk (rt_live RT Σ) kel 24 ->
  rw_cells asegs m (data + 8 * i) [C8 (Z_to_bv 64 rp)] -> chunk (rt_live RT Σ) data (8 * sy) ->
  rw_cells asegs m (rp + 4 * j) [C4 x0] -> chunk (rt_live RT Σ) rp (4 * sx) ->
  0 <= v < 2^32 -> reg_get F r_fa0 = nan_box (Z_to_bv 32 v) ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelSetElement m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(rp + 4 * j, rp + 4 * j + 4)] m m'
          /\ rw_cells asegs m' (rp + 4 * j) [C4 (Z_to_bv 64 v)]) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition makeRangeKernel_cpsV : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  reg_get F r_fa0 = fs32 F_1_0 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 3 (km_cost 1 256) ->
  sec_bytes (rt_live RT Σ) + 8 * 1 + 4 * (256 * 1) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeRangeKernel m)))
    (fun c => exists (Σ' : rts RT) (kel data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' kel 1 256 0 0 data rows /\ kel_vals m' 256 rows rcellV) c
       /\ rt_live RT Σ' = km_live kel data 1 256 rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - km_cost 1 256 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition makeGaussianKernel_cpsV : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 20 -> a1 = Z_to_bv 64 20 -> reg_get F r_fa0 = fs32 F_10_0 -> reg_get F r_fa1 = fs32 F_1_0 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 (2 * 20 + 3) (km_cost (2 * 20 + 1) (2 * 20 + 1)) ->
  sec_bytes (rt_live RT Σ) + 8 * (2 * 20 + 1) + 4 * ((2 * 20 + 1) * (2 * 20 + 1)) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeGaussianKernel m)))
    (fun c => exists (Σ' : rts RT) (kel data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' kel 41 41 20 20 data rows /\ kel_vals m' 41 rows gcellV) c
       /\ rt_live RT Σ' = km_live kel data 41 41 rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - km_cost (2 * 20 + 1) (2 * 20 + 1) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition kernelInvert_cpsV : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kels sy sx cy cx datas : Z) (rowss : list Z) (vs : Z -> Z -> Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kels -> kel_obj (rt_live RT Σ) m kels sy sx cy cx datas rowss -> kel_vals m sx rowss vs ->
  1 <= sy <= 20000 -> 1 <= sx <= 20000 -> sy * sx <= 2^26 -> 0 <= cy < sy -> 0 <= cx < sx ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 (sy + 2) (km_cost sy sx) ->
  sec_bytes (rt_live RT Σ) + 8 * sy + 4 * (sx * sy) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelInvert m)))
    (fun c => exists (Σ' : rts RT) (keld data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 keld) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' keld sy sx (sy - 1 - cy) (sx - 1 - cx) data rows /\ kel_vals m' sx rows (kflip sy sx vs)
          /\ kel_obj (rt_live RT Σ') m' kels sy sx cy cx datas rowss /\ kel_vals m' sx rowss vs) c
       /\ rt_live RT Σ' = km_live keld data sy sx rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - km_cost sy sx <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixBilateralGrayExact_cps2V : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (ks datas kr datar : Z) (rowss rowsr : list Z) (ras : list Z) (ksf rsf : Z -> Z -> Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 ks -> a2 = Z_to_bv 64 kr ->
  pix8 (rt_live RT Σ) m pix v -> kel_obj (rt_live RT Σ) m ks 41 41 20 20 datas rowss -> kel_obj (rt_live RT Σ) m kr 1 256 0 0 datar rowsr ->
  kel_vals m 41 rowss ksf -> ksf 20 20 = p_one_s -> kel_vals m 256 rowsr rsf -> rsf 0 0 = p_one_s ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: RA_BGE_DESTROY :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS ->
  In (PMCOPY_CALLOC1 :: 0x9fdc0 :: 0xa028c :: RA_BGE_AMB :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 8 50 (3 * RASTER_COST + 2^20) ->
  sec_bytes (rt_live RT Σ) + 2 * 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixBilateralGrayExact m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix8 (rt_live RT Σ') m' pix v /\ kel_obj (rt_live RT Σ') m' ks 41 41 20 20 datas rowss /\ kel_vals m' 41 rowss ksf
          /\ kel_obj (rt_live RT Σ') m' kr 1 256 0 0 datar rowsr /\ kel_vals m' 256 rowsr rsf
          /\ (pixd <> 0 -> pix8 (rt_live RT Σ') m' pixd vd /\ p_w vd = p_w v /\ p_h vd = p_h v)) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (3 * RASTER_COST + 2^20) <= rt_credit RT Σ').

End BiVIface.
(* [comment removed for export] *)
