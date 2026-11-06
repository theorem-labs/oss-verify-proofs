(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells ABytes AF_fse_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_pure AH_fse_calls AH_fse_fill AH_fse_B1 AH_fse_B2 AH_fse_B2a.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
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

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Lemma land_ones32B : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof.
intros x H. change 4294967295 with (Z.ones 32). Local Ltac2 Set LiaHints.tbl := fun () => "0020=44021460374.253493744851.2000001004SS1H".
rewrite Z.land_ones by lia.
apply Z.mod_small. change (2^32) with 4294967296. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC1. Context {rc : runConstT}.
Section BG.
Hypothesis U32R : prod_u32r_stmtA.
Hypothesis I32R : prod_i32r_stmtA.
Hypothesis WBOUND : fse_wbound_stmtA.
Hypothesis WRITE : fse_write_stmtA.
Hypothesis ISERR : fse_iserror_stmtA.
Variables (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (SPA lo F P D : Z) (pl : list Z) (RNG : footprint).
Notation SP := (bv_unsigned sp).
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis SPT : SP + 16 <= 2^47.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis ESPA : SPA = (SP - 224) - (SP - 224) mod 32.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
Hypothesis FH : ablk F (F + 2048).
Hypothesis FC : F + 2048 <= ATOP.
Hypothesis F2048 : F mod 2048 = 0.
Hypothesis RF : rng RNG F 2048.
Hypothesis RSF : rng RNG (shad F) 256.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis P16 : P mod 16 = 0.
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis PF : P + 16 <= F \/ F + 2048 <= P.
Hypothesis DLOC : (pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl).
Hypothesis D8 : D mod 8 = 0.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis DF : D + zlen pl <= F \/ F + 2048 <= D.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis SZ26 : zlen pl < 2^26.
Lemma gap_B : forall (POST : machine_state -> Prop) (m1 : amem)
(y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (tl msv : Z) (jb jc jd : list byte),
0 <= msv <= 255 -> 0 <= SPA -> rng RNG SPA 120 ->
rw_cells bsegs m1 SPA [CB 24 jb; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); CB 16 jc;
C8 (Z_to_bv 64 (SHF F + 148)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 msv); CB 16 jd;
C8 (Z_to_bv 64 F)] ->
(forall a0 : word, evtF bsegs RNG POST
(MS (mkR (Z_to_bv 64 0x80f28) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) a0 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (F + 608 + 2 * 0)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl - 1)) (Z_to_bv 64 (0 + 1)) (Z_to_bv 64 msv)
(Z_to_bv 64 P) (Z_to_bv 64 (F + 608)) (Z_to_bv 64 257) (Z_to_bv 64 (SHF F)) (Z_to_bv 64 (F + 608 + 2 * 0))
y28 y29 y30 y31)
FR (Z_to_bv 64 0x80f60) fc None m1 (seg_rom bsegs))) ->
evtF bsegs RNG POST
(MS (mkR (Z_to_bv 64 0x80f28) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 tl) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (2^tl - 1)) (Z_to_bv 64 msv) (Z_to_bv 64 F)
(Z_to_bv 64 P) (Z_to_bv 64 (F + 608)) (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F)) (Z_to_bv 64 (SHF F + 76))
y28 y29 y30 y31)
FR (Z_to_bv 64 0x80f44) fc None m1 (seg_rom bsegs)).
Proof using D F FR P RNG SPA fc gp pl rc sp tp.
intros POST m1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 tl msv jb jc jd MSV SPA0 RFRA FRA K.
pose proof (rng_bounds _ _ _ RFRA) as RB.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>10702835955.722597469165.79 27364998816.7945164762014.797612119636.79 9211989531.83 00000500600700<00A00BS3MSVSFS3MSVS3MSVS".
zstep. zstep. zstep. zstep.
zstep. zstep. zstep.
rewrite land_ones32B by lia.
specialize (K (Z_to_bv 64 (msv ≪ 32))). rewrite Z.mul_0_r, Z.add_0_r in K. change (0 + 1) with 1 in K. exact K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma pB_all : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2v s4v s5v s7v s8v x28 x29 x30 x31 : word) (m : amem)
(jb jc jd njunk jdata jmsv : list byte),
mem_inv bsegs m -> stk bsegs m lo SPA ->
prod_atA m P D (zlen pl) -> bytes_at bsegs m D (map (Z_to_bv 8) pl) -> fse_rt m ->
unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) ->
rw_cells bsegs m SPA [CB 40 jb; C8 (Z_to_bv 64 F); CB 16 jc; C8 (Z_to_bv 64 (SHF F + 148)); CB 40 jd; C8 (Z_to_bv 64 F)] ->
rw_cells bsegs m (F + 32) [CB 512 jdata] ->
rw_cells bsegs m (F + 608) [CB 512 njunk] ->
rw_cells bsegs m (F + 1760) [CB 4 jmsv] ->
rw_cells bsegs m (SHF F) (FSH F8S F8S F8S BF8 BF8) ->
evtF bsegs RNG (phaseB_postA gp tp sp FR fc SPA lo F P D pl m)
(MS (mkR (Z_to_bv 64 0x80ec0) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17
s2v (Z_to_bv 64 ASHOFF) s4v s5v (Z_to_bv 64 F) s7v s8v (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F))
(Z_to_bv 64 (SHF F + 76)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x80ec0) fc None m (seg_rom bsegs)).
Proof using All.
intros until jmsv. intros MI ST PR PAY RT UNP UND FRA DATAC NCJ MSVC SH.
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
destruct (fseA_unfold pl (zlen pl)) as (tl & r1 & msv & r2 & pre & rw & r3 & v' & r4 & bsz & r5 & E1 & E2 & E3 & EC0 & EC1 & EB).
cbv zeta in EB. destruct EB as [EB EA].
Local Ltac2 Set LiaHints.tbl := fun () => "00m0?14252587283.10315043033658.10616000752653.6  1837195233.2   1952185541.2   23492641683.10123492641683.10325711238968.1  26492336164.16 26507473801.13 27229898287.5  27242066989.16227719924594.10328573892092.5  29788721223.12630716771743.8  31653695134.1  32189337881.23 32421787638.14 33715762100.2  3522744003.104 3699646368.3   37934716299.16237945121459.10637947221643.1063832947422.7   3920259420.5   39583537813.2  40003882986.2  40081792849.10440517057895.7  41422282358.10541860211210.2  42151085669.4  4292559652.106 45450798590.10548647284925.13349107703395.17 52544056194.6  52564984551.15 5377903808.7   55144173634.10455511318164.4  55581753195.1  55911207192.16656043687309.10 56184997634.5  57011364998.3  57017755931.2  57104778514.4  59308628433.16859860646032.16861876085661.1  62708484519.9  63111278787.16764401800182.10565090233367.12866151427842.16 66775507151.1  7606134511.167 8806423751.5   00000100200;00A00F00G00H00I00h01>01E02F02G02K02X02b02c03803R03W03X03\03m04204504@04K04Q04V04Z04e04f04l05505905=05M06106:06\06d06e06i06j07707E07K07Q07W07`08308C08D08[08m09109B09U09V09f09jSSS3LOC3FH3S4MSVPS3PL1SSSS3LOC4SPAB3ATR4LOS'3BSF3FBD3PBDS3LOC2PF3FH34SPAB4LOS'S2S12S2S3LOC2PF2DP2DF2F12S12S23FI13FI23FH23PL23RSP4SPAB3ATR4LOS'2D04LENPSS2HxS3FI23FH23PL2S2B12B32DBSS5F20481H2H02H42H52H9S3LOC2PF3FH33PL34SPAB4LOS'S3FH4SS2PFS3RW03FI23FH23PL2S3RW0S1HS4SPAB4LOS'S4SPAB4LOS'S4MSVPS3FH2S2S1S2S12S23FI6SS4RSPAS3LOC3ATRS2S2S2F1S3FI23FH23PL22H0S3LOC2DP2DF4SPAB3ATR4LOS'3BSF2DT3DBDS3LOC3PL3S3LOC2PF3FH34SPAB3ATR4LOS'3BSF3FBDS3LOC2DTSS2DFSS3FI23FH23PL2S3FH13FH41H2H0S4SPABS2F21KS4MSVPS3RW03FI3S2F13FI23FH23PL22K2S2F13FI23FH23PL2SS3LOC3RSP4SPAB3ATR4LOS'S2F23FI23FH23PL21KS2F1S3FI23FH23PL23ATRS5F20481H2H02H43P16SS2F23FI23FH23PL2S2Hx".
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & _).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
pose proof (uint32Range_spec pl (zlen pl) 5 12 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S1.
rewrite E1 in S1. destruct S1 as (_ & S1 & _).
pose proof (uint32Range_spec pl r1 0 255 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S2.
rewrite E2 in S2. destruct S2 as (_ & S2 & _).
assert (RW0 : 0 < 2^tl - 1 <= 4095).
{ assert (2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia). change (2^5) with 32 in *. change (2^12) with 4096 in *. lia. }
pose proof (fse_fill_inv 256 pl r2 0 msv (2^tl - 1) [] pre rw r3 AB ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(constructor) E3)
as (sF & FI1 & FI2 & FI3 & FI4 & FI5 & FI6).
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
pose proof atop_range as ATR. pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
assert (SBF : SHF F = F / 8 + ASHOFF) by (unfold SHF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (BSF : 2147450880 <= SHF F /\ SHF F + 256 <= 17594333495296) by (rewrite SBF; unfold ASHOFF; clear - FH1 FH4; Z.div_mod_to_equations; lia).
pose proof (ablk_disj_band _ _ FH) as FBD. pose proof (ablk_disj_band _ _ BLKP) as PBD. unfold KLS in FBD, PBD.
assert (D0 : 0 < D /\ D + zlen pl <= ATOP /\ (D + zlen pl <= 2147450880 \/ 17594333495296 <= D)).
{ destruct DLOC as [[-> ->]|B]; [unfold AEMPTY; cbn; lia| pose proof (ablk_lin _ _ B) as (B1 & B2 & B3 & B4); unfold AIMG_HI in B1].
pose proof (ablk_disj_band _ _ B) as DB. unfold KLS in DB. clear - B1 B2 B3 DB. lia. }
destruct D0 as (D0 & DT & DBD).
assert (BLKD : 0 < zlen pl -> ablk D (D + zlen pl)).
{ intros H0. destruct DLOC as [[-> _]|B]; [cbn in H0; lia| exact B]. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
destruct RT as (GOT & RIC & REAL & SHB & INI & LAY & GOTM).
eapply evtF_cut.
{ exact (pB1 U32R gp tp sp FR fc SPA lo F P D pl RNG LOS LOC SPT SP16 ESPA RSTK RI FH F2048 RF RSF BLKP P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ26
x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2v s4v s5v s7v s8v x28 x29 x30 x31 m tl r1 msv r2 jb jc jd njunk
E1 E2 MI ST PR PAY GOT RIC SHB INI LAY REAL GOTM UNP UND FRA NCJ SH). }
cbv beta. intros ms1 (m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & jb' & jd' & -> & MU1 & WM1 & MI1 & ST1 & PR1 & FRA1 & NC1 & SH1).
assert (RT : fse_rt m) by exact (conj GOT (conj RIC (conj REAL (conj SHB (conj INI (conj LAY GOTM)))))).
clear GOT RIC REAL SHB INI LAY GOTM.
assert (SUB1 : sub_fp [(P + 8, P + 16); (SPA - 2208, SPA + 120); (F + 608, F + 1120); (SHF F, SHF F + 256)] (W_B SPA F P)).
{ unfold W_B. intros x Hx. cbn [outside] in *. clear - Hx. lia. }
pose proof (munch_weaken _ _ _ _ SUB1 MU1) as MUB1.
pose proof (rw_cells_transport _ _ _ _ _ _ DATAC MU1 WM1
ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PF FBD BSF FH2 FH3 ATR LOC LOS' SPAB; lia)) as DATA1.
pose proof (rw_cells_transport _ _ _ _ _ _ MSVC MU1 WM1
ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PF FBD BSF FH2 FH3 ATR LOC LOS' SPAB; lia)) as MSV1.
pose proof (bytes_at_transport _ _ _ _ _ _ PAY MU1 ltac:(rewrite LENP; cbn [disjoint_from]; clear - DP DF DBD DT BSF ATR LOC LOS' SPAB; lia)) as PAY1.
zstep. if_cases K; zify_cond K.
-
assert (MSV0 : msv = 0) by (rewrite ?unsigned_lit in K by lia; lia). subst msv.
rewrite (fse_fill_stop 256 pl r2 0 0 (2^tl - 1) []) in E3 by lia. injection E3 as <- <- <-.
apply u8arr_of_rw_cells in NC1. change 512%nat with (2 * 256)%nat in NC1. rewrite <- u16s_zero in NC1.
change (Z_to_bv 64 ASHOFF) with (Z_to_bv 64 2147450880).
exact (pB2 U32R WBOUND WRITE ISERR gp tp sp FR fc SPA lo F P D pl RNG LOS LOC SPT SP16 ESPA RSTK RI FH F2048 RF RSF BLKP
P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ26
(Z_to_bv 64 0x80f28) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 tl) (Z_to_bv 64 0) (Z_to_bv 64 F)
(Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F + 76)) y28 y29 y30 y31 m m1 tl 0 (2^tl - 1) r2 v' r4 bsz r5 []
_ _ _ jdata jmsv EC0 EC1 EB EA ltac:(lia) ltac:(lia) NC1 PR1 FRA1 DATA1 MSV1 SH1 ST1 MI1 RT PAY UNP UND MUB1 WM1).
-
zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
assert (MSVP : 0 < msv <= 255) by (rewrite ?unsigned_lit in K by lia; clear - K F2; lia). clear K.
assert (RFRA : rng RNG SPA 120) by (eapply rng_sub'; [exact RSTK| clear - SPAB SPA88 LOS' RSP; lia]).
assert (RSPA : 0 <= SPA < 2^64) by (clear - SPAB LOS' LOC ATR RSP; lia).
assert (LO32 : lo <= SPA - 32) by (clear - SPAB LOS'; lia).
assert (LOK : KHIGH <= lo) by (unfold KHIGH; clear - LOC ATR; lia).
assert (PLO : P + 16 <= lo) by (clear - PL3 LOC; lia).
assert (DLO : D + zlen pl <= lo) by (clear - DT LOC; lia).
assert (NCB : ablk (F + 608) (F + 608 + 512)) by (eapply ablk_sub; [exact FH| clear; lia| clear; lia]).
assert (NC8 : (F + 608) mod 8 = 0) by (clear - F2048; Z.div_mod_to_equations; lia).
assert (NCLO : F + 608 + 512 <= lo) by (clear - FH3 LOC; lia).
assert (NCP : F + 608 + 512 <= P \/ P + 16 <= F + 608) by (clear - PF; lia).
assert (DNC : D + zlen pl <= F + 608 \/ F + 608 + 512 <= D) by (clear - DF; lia).
assert (P0 : 0 < P) by (clear - PL1; lia).
assert (P8 : P mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
assert (RSTKA : rng RNG lo (SPA - lo)) by (eapply rng_sub'; [exact RSTK| clear - SPAB LOS'; lia]).
assert (RNC : rng RNG (F + 608) 512) by (eapply rng_sub'; [exact RF| clear; lia]).
assert (RNCS : rng RNG (shad (F + 608)) 64).
{ replace (shad (F + 608)) with (shad F + 76) by (rewrite !shad_div; clear - F2048; Z.div_mod_to_equations; lia).
eapply rng_sub'; [exact RSF| clear; lia]. }
pose proof (unp_P_WB sp SPA lo F P D pl LOS LOC SPT SP16 ESPA FH F2048 BLKP P16 PF m m1 UNP MUB1) as UNP1.
pose proof (unp_D_WB sp SPA lo F P D pl RNG LOS LOC SPT SP16 ESPA FH FC F2048 BLKP PF DLOC D8 RD RDS DP DF PLB SZ26 m m1 UND MUB1) as UND1.
pose proof (fsh_unp_nc m1 F F2048 ltac:(clear - FH2; lia) ltac:(unfold KEND; clear - FH4; lia) _ _ _ _ SH1) as UNC1.
replace (F + 1120) with (F + 608 + 512) in UNC1 by (clear; lia).
pose proof (rt_WB sp SPA lo F P D pl LOS LOC SPT SP16 ESPA FH BLKP m m1 RT MUB1 WM1) as RT1.
pose proof RT1 as (GOT1 & _ & _ & SHB1 & _).
apply u8arr_of_rw_cells in NC1. change 512%nat with (2 * 256)%nat in NC1. rewrite <- u16s_zero in NC1.
eapply (gap_B _ m1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 tl msv _ _ _ ltac:(clear - MSVP; lia)
ltac:(clear - RSPA; lia) RFRA FRA1).
intros a0.
eapply (fill_loopA I32R RNG gp tp sp (Z_to_bv 64 (SHF F)) FR fc m1 SPA (F + 608) P D pl msv lo _
RSPA LO32 LOK PLO DLO DP NCB NC8 NCLO NCP DNC P0 P8 D0 D8 BLKP BLKD ltac:(clear - MSVP; lia) RI RSTKA RP RPS RD RDS RNC RNCS
UNP1 UND1 UNC1 256%nat 0 (2^tl - 1) r2 [] m1
(Z_to_bv 64 0x80f28) y5 y6 y7 a0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31
ltac:(clear - MSVP; lia) RW0 eq_refl ltac:(clear - MSVP; lia) PLB ltac:(clear - S1 S2; lia)).
+
split; [exact NC1|]. split; [exact PR1|]. split; [exact PAY1|]. split; [exact GOT1|]. split; [exact SHB1|].
split; [exact ST1|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI1].
+
intros m2 pre' rwF r3' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z27 z28 z29 z30 z31 EF FIV RWF.
rewrite E3 in EF. injection EF as <- <- <-.
destruct FIV as (NCA2 & PR2 & PAY2 & GOT2 & SHB2 & ST2 & MU2 & WM2 & MI2).
assert (SUB2 : sub_fp [(P + 8, P + 16); (F + 608, F + 608 + 512); (SPA - 32, SPA)] (W_B SPA F P)).
{ unfold W_B. intros x Hx. cbn [outside] in *. clear - Hx. lia. }
pose proof (munch_trans _ _ _ _ MUB1 (munch_weaken _ _ _ _ SUB2 MU2)) as MUB2.
pose proof (wmono_trans _ _ _ _ WM1 WM2) as WMB2.
pose proof (rw_cells_transport _ _ _ _ _ _ FRA1 MU2 WM2
ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PF FH2 FH3 PL3 ATR LOC LOS' SPAB; lia)) as FRA2.
pose proof (rw_cells_transport _ _ _ _ _ _ DATA1 MU2 WM2
ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PF FH2 FH3 ATR LOC LOS' SPAB; lia)) as DATA2.
pose proof (rw_cells_transport _ _ _ _ _ _ MSV1 MU2 WM2
ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PF FH2 FH3 ATR LOC LOS' SPAB; lia)) as MSV2.
pose proof (rw_cells_transport _ _ _ _ _ _ SH1 MU2 WM2
ltac:(rewrite FSH_size; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; clear - PBD FBD BSF FH2 FH3 PL3 ATR LOC LOS' SPAB; lia)) as SH2.
change (Z_to_bv 64 (F + 608)) with (Z_to_bv 64 (F + 608)).
exact (pB2 U32R WBOUND WRITE ISERR gp tp sp FR fc SPA lo F P D pl RNG LOS LOC SPT SP16 ESPA RSTK RI FH F2048 RF RSF BLKP
P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ26
z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 (Z_to_bv 64 msv) (Z_to_bv 64 257) z27 z28 z29 z30 z31 m m2
tl msv rw r3 v' r4 bsz r5 pre _ _ _ jdata jmsv EC0 EC1 EB EA ltac:(clear - FI3 RW0; lia) ltac:(clear - FI6 S1 S2; lia)
NCA2 PR2 FRA2 DATA2 MSV2 SH2 ST2 MI2 RT PAY UNP UND MUB2 WMB2).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End BG.
End CANSEC1.
