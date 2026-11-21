(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (fmt_d_bytes, fmt_toobig_bytes, fmt_usage_bytes and 7 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ShadowTac F_irt F_rip I_printf_lib I_printf_common.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_I_printf_formats () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats3zb8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats5FMT_DC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats;FMT_D_charsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5BothW@I_printf_formats:FMT_TOOBIGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats@FMT_TOOBIG_charsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow<shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats;fmt_d_bytesC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW?I_printf_common7intconvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW?I_printf_commonBprintf_common_int1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib5BothW@I_printf_formats@fmt_toobig_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW@I_printf_formats9FMT_USAGEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats?FMT_USAGE_charsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats<FMT_CANTOPENC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsBFMT_CANTOPEN_charsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats;FMT_READERRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsAFMT_READERR_charsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formats?fmt_usage_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5BothW?I_printf_common5sconvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW?I_printf_commonBprintf_common_str1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsDprintf_common_s_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsBfmt_cantopen_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsAfmt_readerr_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsDprintf_common_d_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW@I_printf_formatsIprintf_common_toobig_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition zb8 (l : list Z) : list byte := map (Z_to_bv 8) l.

(* [comment removed for export] *)
Definition FMT_D : Z := 0x147a8.
Definition FMT_D_chars : list Z := [37; 100; 10]%Z.
(* [comment removed for export] *)
Definition FMT_TOOBIG : Z := 0x196a5.
Definition FMT_TOOBIG_chars : list Z :=
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]%Z.

End CANSEC1.
Ltac img_strz A B :=
  intros m MI; apply ro_bytes_at; [exact MI| unfold A; lia| unfold A, B, zb8; cbn; lia|];
  apply ro_bytes_b_sound; vm_compute; reflexivity.
Section CANSEC2. Context {rc : runConstT}.
Lemma fmt_d_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_D (zb8 FMT_D_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_D FMT_D_chars. Qed.
Lemma fmt_toobig_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_TOOBIG (zb8 FMT_TOOBIG_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_TOOBIG FMT_TOOBIG_chars. Qed.

End CANSEC2.
Ltac norm_len CH :=
  unfold zb8, CH; repeat match goal with |- context [Z.of_nat (length ?l)] => let n := eval cbv in (Z.of_nat (length l)) in change (Z.of_nat (length l)) with n end.
Ltac pci A BY CH :=
  lazymatch goal with
  | |- _ = Z_to_bv 64 _ => eassumption
  | |- bytes_at _ _ _ _ => first [apply BY; assumption | eassumption]
  | |- Forall _ _ => first [assumption | unfold zb8, CH; cbn [map app]; noz_tac]
  | |- _ = zb8 _ ++ _ => unfold zb8, CH; cbn [map app]; reflexivity
  | |- shadow_bytes _ _ _ _ => norm_len CH; assumption
  | |- rng _ (shad _) _ => norm_len CH; assumption
  | |- intconv _ => unfold intconv; cbv; first [left; reflexivity | right; reflexivity]
  | |- sconv _ => unfold sconv; cbv; reflexivity
  | |- bv_unsigned _ = _ => cbv; reflexivity
  | |- _ <> [] => discriminate
  | |- rw_cells _ _ _ _ => eassumption
  | |- _ /\ _ => first [eassumption | norm_len CH; unfold A; lia]
  | |- _ => first [assumption | eassumption]
  end.
Ltac pc_inst A BY CH PRE :=
  intros; eapply printf_common_int1 with (pre := zb8 PRE); pci A BY CH.

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Definition printf_common_int_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44394) fc None m (seg_rom bsegs)).

Theorem printf_common_d_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> a1 = Z_to_bv 64 FMT_D ->
  shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44394) fc None m (seg_rom bsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_I_printf_formats ()) ["CANSEC3"] "p'0h03H10h12Hbh23H11h31bi001bh41eh51Ah61Ph77__arithh84__ffh98__varmaph:5__with;1li011lh<1xh=1Fh>3RNGh?2a0h@2a1hA2a2hB2a3hC2a4hD2a5hE2a6hF2a7hG2fchH2gphI2lohJ1mhK2rahL2s0hM2s1hN3s10hO3s11hP2s2hQ2s3hR2s4hS2s5hT2s6hU2s7hV2s8hW2s9hX2sphY2t0hZ2t1h[2t2h\2t3h]2t4h^2t5h_2t6h`2tpi028bv_is_wfi03;bv_unsignedi041pi051zp;1p;2p;4p;3p;6p;op;7g0000j10Tg000Uj1PTg0013R0j1STg008Xj11Tg00Ogj2pTg001Vj1jTg0028j2fTg00PSj26Tg00Q=j4bTg00Qoj2JTg00=Yj28Tg003kj27j1wTg00RLj1DTg004Qj1QTg00SAj4[Tg00;nj32Tg009=j1BTg00T7j1TTg00?;j2@Tg00Toj4ZTg00Ulj3MTg002lj1YTg00V_j2aTg005nR1j1RTg00Wfj3?Tg00XGj34Tg00X^j3`Tg0051j3FTg00Y@j2xTg00Y_j6CTg00@5j4_Tg006Nj1vTg006lj1uTg007Jj1tTg00:Fj2oTg00:hj2OTg00;Bj2mTg00<Hj3lTg00<gj4kTg00Z;R2j2KTg00@Qj2iTg00A1j1hTg00>5j3\Tg005Qj3]Tg00ZVj1ITg00Zoj3gTg00[IR3j2nTg00[cj1eTg00\elodTg0085j2qTg009[j4cTg00DAj7rTg00^2j7sTf0R4#0#0p=<%14#0p=;%04#0#0#Bp=3%04#1p=A%04#0#0#0p=:%14#1p=U%04#1#0#1p=H%14#1#1#1p=5%04#1#1#1p==g00^VR5f1R6;F4p=Eg00KPR7g00JFR8724#Ip=>%04#Bp=XA2748p=WP7f2R9P6g00_KR:P8P4ECp=V1q74p=GP7P6g00KnP4Ccp=LP6g00DeR;g00EDR<P<g00EdR=P4g00FDFrp=NP9P;P<P<P=P6P4Fsp=^A2764p=9g00_gg00FdR<#0R;#0R>#0R?#<R@#0RA#PRB#SRC%1;R;#P/pC%P@#S%P?R?#SR@#j\Cg00GIRD/f6PDP9P6fRRE,6BCbfSRF,6B%;>R>#<#;#3'J,89g00``f3RG'8PDf5RH%A<#;#A#:#;#<#U#3%0<#;#H#5#<#H#3,7B#D%A<#;#5#H#5#3,7B#D%=<#A#<#H#5#3RI,7B#D%=<#A#=#5#A#3,7B#D%=<#A#=#5#;#3,7B#D%=<#A#=#5#<#3,7B#D%Q5R5'E'E'E'E'E'EC[PDf6RDPI%1<RI#1RJ#URK#1#U#5#5#:#:#:#3,7B#D/E5C[fNR5g00H>RL,7B52Cf8RM%BARN,JL#TRO%BIRP,@LRQ/@N#TRRP8V7RSCZf[RT%0A#<#:#3RA%0<#5#5#;#:#:#33Mf\RUf9RVfZRW,6B/JV3Mf]RB1JRO7MOf^RRPBPUPTPWfYfXfWfVfUfTPFPEfQfPfOP5fMfLfKfJfIfHfGfFfEfDfCfBfAf@f?f>f=f<R5f;PLg00I?#YREf:RFPVPMf7RVPDPHf4RW1a5Fg00aVp4p710RFp-0RT\4RU%R6RBP2A?964A4W49PWP6O1[^<GR2[A4G46PGP6O1[^<9A?G96[RXA?WG9\2A`964P4n2001000000120000000W;W6W5R2PX^;B^6U^5FRFP4P@16?4RU#>X3@RB%1>#BR>,7?RX%<I#;#XRI,7?RY%0;R;#BRZ,7?R[%Q@R\5F@R]5F@R^5F@R_A4@4_P3A2@X6A4@6^16?9R`#>P4A2@X9P@PXPBP0P?P7PXP6n101100000120103102Ra#WP7PTP4g00b3Rbg00bPRcPbn011050003001000010000X47Rd=Va4Pb1xb4Rab2W016?XRe#>ePGP4ECW0P4O1A4@9^P3A2@YGA4@G]16?WR^#>P4A2@YWP@PYPBP0P?P7PYP6n101100000120103102Rf#WAVfd4PbPab2W016?YRg#>ePHP4ECW0P4O1A4@W]P3A2@[HA4@H\16?D#>P4A2@[DP@P[PBP0P?P7P[P6n101100000120103102R0#WAV0d4PbPab2W016?[Rd#>ePVP4ECW0P4O1A4@D\Pb16?M#>P4n010000000W1P4O1n200100000021000010000W1P4O1n200100000021000011000W1P4O1n200100000021000011000W1X3@O4b0P7P@%w?R?%Q7RM9F7Z9F7I9F7>C_RZ9?@BeA?@BEeg00JdRB#QRD%RBRB%v7RV%u7RH%t7RW%B<Rh#GRi%GPRj'L,NW%XKRK#G,Lj,NW3^1oW=R=P4P9g00LURkg00M5Rl'O1m49=2kldAl786CkR8b8b9b:18hP18PK'KRlP4b7Ple1i@E#hRl,8h18lK'KePDPBPVPH%GA%<;#5#H#3R;#GRH'L,NWA\7Hj=\7i%1<#:#=#;#:#:#3R<#G'L,NW5^WP=P8b8b9b:18A;1@;P/@h/8<'KP4b718ALRA1@Qh/8<'Ke1@LlRl/@h/8<,KAePGP5PO1@lN#TRlPSCZeP9P6P41JlO9MROe%YMRRPXPYP]%R@RY/O_P7P@P?PMC_RM=]@_92YZeA]@R_92YEeP2PFP4P@19U>#IX3@RUP\A4@4\Pb19`>#IR`P4n010000000W1X3@O4b0A?@UMeA?@UReP2PFP4P@PUP]A4@4]P3A2@[6A4@6\P`P4A2@[9P@P[PU190>P7P0P7PTP4Pbg00blPTP4PbPcPbn011040003100001000000Pbn011050003001010410104X47P:P>P4ECPbPab2W019d>#IePGP4ECW0P4O1A4@9\Pb19^>#IP4n010000000W1P4O1n200100000021000010000W1X3@O4b0A?@U]RUePUe1O7>19e>e19fI%HJ#BRJ,9f1O7I3g19gI19gJ'ne%egeA2Y]\RgPYP]P1P@PTP4PbPcn10110100020020000000X4YP:P\P4ECPbPab2W0%IgeModUUUUUUUUUUUXI7WJWGW=X_CX^CX]CX\CXOCXNCXWCXVCXUCXTCXSCXRCXQCXPCXFCXECXDCXCCXBCXACX@CX?CXMCXLCX[CXZCXYCX`CXHCXXCWKW>o"). Qed.

Theorem printf_common_toobig_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> a1 = Z_to_bv 64 FMT_TOOBIG ->
  shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44394) fc None m (seg_rom bsegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_I_printf_formats ()) ["CANSEC3"] "p'0h03H10h12Hbh23H11h31eh41bi001bh51Ah61Ph77__arithh84__ffh98__varmaph:5__with;1li011lh<1xh=1Fh>3RNGh?2a0h@2a1hA2a2hB2a3hC2a4hD2a5hE2a6hF2a7hG2fchH2gphI2lohJ1mhK2rahL2s0hM2s1hN3s10hO3s11hP2s2hQ2s3hR2s4hS2s5hT2s6hU2s7hV2s8hW2s9hX2sphY2t0hZ2t1h[2t2h\2t3h]2t4h^2t5h_2t6h`2tpi028bv_is_wfi03;bv_unsignedi041pi051zp%0p%1p;1p;2p;4p;3p;6p;op;7g0000j17Tg000Uj1YTg0013R0j1[Tg008Xj18Tg00Ogj2|Tg001Vj1tTg0028j2mTg00PSj24Tg00Q=j4gTg00Qoj2PTg00=Yj2DTg003kj29j1}Tg00RLj1MTg004Qj1WTg00SAj4bTg00;nj31Tg009=j1JTg00T7j1\Tg00?;j2ITg00Toj4^Tg00Ulj3UTg002lj1]Tg00cQj2fTg005nS00j1ZTg00Wfj3HTg00XGj30Tg00X^j3eTg0051j33Tg00Y@j2~Tg00Y_j62Tg00@5j4dTg006Nj1{Tg006lj1zTg007Jj1xTg00:Fj2vTg00:hj2VTg00;Bj2sTg00<Hj3rTg00<gj4qTg00Z;R1j2QTg00@Qj2pTg00A1j1oTg00>5j3_Tg005Qj3`Tg00d]j3lTg00[IR2j2kTg00[cj1uTg00ZVj1STg00\elojTg0085j2wTg009[j4iTg00DAj7hTg00^2j7yTf0R3#7#7p=F%83#7p=@%73#7#7#Jp=?%73#8p=G%73#7#7#7p=E%83#8p=c%73#8#7#8p=R%83#8#8#8p=C%73#8#8#8p=Lg00^VR4f1R5;33p=Ng00KPR6g00JFR7713#Sp=5%83#Jp=K%73#Jp=BA1637p=;P6f2R8P5g00_KS01P7P3E2p=<1453=167#Sp=>f4R9f3R:A36539368536536p=A1w63p=OP6P5g00KnP3Cip=XP5g00DeR;g00EDR<P<g00EdS02P3g00FDFhp=TP8P;P<P<Q02P5P3Fyp=aA36539368p=nA1653#Sp=6A1653p=:P6P:P8Q01P5P3E2p==g00_gg00FdR<#7R;#7R=#7R>#FR?#7R@#YRA#[RB%8;R;#Y/|B%Y?#[%Y>R>#[RC#t\Bg00GIRD/m5PDP8P5fRS03,4ACgfSS04,4A%@=R=#F#@#?'P,D8g00``/D:PDf5RE%G<#@#G#E#@#F#c#?%7<#@#R#C#F#R#?,9A#M%G<#@#C#R#C#?,9A#M%L<#G#F#R#C#?RF,9A#M%L<#G#L#C#G#?,9A#M%L<#G#L#C#@#?,9A#M%L<#G#L#C#F#?,9A#M%W4R4'N'N'N'N'N'NCbPDf6RDPF%8<RF#8RG#8RH#8RI#8#c#C#C#E#E#E#?,9A#M/N4CbfNR4g00MURJ,9A51Bf8RK%J@S05,PJ#\RL%J?R?,IJS06Q05'I#\RMP7V6S07C^f[S08%7@#F#E#?S09%7<#C#C#@#E#E#?3Uf\S0:f9R@fZS0;,4A/P@3Uf]S0<1PML7ULf^RMQ0<Q0:Q08Q0;fYS0=fXS0>fWS0?fVS0@fUS0AfTS0BQ04Q03fQS0CfPRAfORNP4fMROfLRPfKRQfJRRfIRSfHRTfGRUfFRVfERWfDRXfCRYfBRZfAR[f@R\f?R]f>R^f=R_f<R`f;RaPJg00N[#]S0Df:RbP@PKf7RcPDPEP91f`bg00aVp4p710Rdp-0Re\3Rf%Z5RgP1AH853A0938P9P5O1[^<:R1[A0:35P:P5O1[^<8AH:85[RhAH9:8\1Ae853P3n2001000000120000000W;W6W5S0EPh^;g^6f^5dS0FP3PC14>3S0G#5X4CRd%7FRF#7Rf#GRg#KS0H,9>Rh%8FRF#8R1#7#BS0I,9>Ri%FF#KS0J,9>RF%7GRG#@Rj#JS0K,9>Rk19>?Rl%81#BS0L,9>R1%7GRG#7#BS0M,9>Rm%KjRn,9>Ro%BjS0N,9>Rj%BIRI,9>Rp%7HRH#KS0O,9>Rq%K=R=,9>Rr%BgS0P,9>Rg%7H#KS0Q,9>RH%8fRf#7Rs#8S0R#JS0S,9>Rt%8GRG#KS0T,9>Ru%@;#BS0U,9>Rv%BGS0V,9>RG%8f#BS0W,9>Rf%BsS0X,9>Rs%B;S0Y,9>R;%WCRw53CS0Z53CS0[93CtS0\93CuS0]93CoS0^53CS0_93CtS0`53CS0a93ClS0b53CS0c53CS0d53CS0e93CjS0f53CS0g53CRx93ClRy93CoS0h53CRz93ClS0i53CS0j53CS0k93ClS0l53CS0m53CS0n53CS0o53CS0p93CFS0q53CS0r53CS0s53CS0t53CR{53CS0uQ0u90C3P2A1Ch5S0vA0C5{14>8S0w#5P3A1Ch8S0xPCPhPdP0P>P6PhP5n101100000120103102S0y#;Q0yP6PeP3g00b3R|g00bPS0zP|n011050003001000010000X36R};<3P|1~|3R~b2W014>hS0{#5eP:P3E2W0P3O1A0C8{P2A1Ci:S0|Q0t90C:14>9S0}#5P3A1Ci9S0~PCPiPdP0P>P6PiP5n101100000120103102S10#;Q10?<}3P|P~b2W014>iS11#5ePEP3E2W0P3O1Q0t90C9P2A1CFES0tQ0s90CE14>DS12#5P3A1CFDS13PCPFPdP0P>P6PFP5n101100000120103102S14#;Q14?<}3P|P~b2W014>FS15#5eR{PcP3E2W0P3O1Q0s90CDP2A1CkcS0sQ0r90Cc14>KS16#5P3A1CkKS17PCPkPdP0P>P6PkP5n101100000120103102S18#;Q18?<}3P|P~b2W014>kS19#5eP@P3E2W0P3O1Q0r90CKP2A1Cl@S0rQ0q90C@14>bS1:#5P3A1ClbS1;PCPlPdP0P>P6PlP5n101100000120103102S1<#;Q1<?<}3P|P~b2W014>lS1=#5eS1>PaP3E2W0P3O1Q0q90CbP2A1CFaS0qQ0p90Ca14>`S1?#5P3A1CF`S1@PCPFPdP{P_P3E2W0P3O1Q0p90C`P2A1C1_S0pQ0o90C_14>^S1A#5P3A1C1^S1BPCP1PdP0P>P6P1P5n101100000120103102S1C#;Q1C?<}3P|P~b2W014>1S1D#5eP]P3E2W0P3O1Q0o90C^P2A1Cm]S0oQ0n90C]14>\S1E#5P3A1Cm\S1FPCPmPdP0P>P6PmP5n101100000120103102S1G#;Q1G?<}3P|P~b2W014>mS1H#5eP[P3E2W0P3O1Q0n90C\P2A1Co[S0nQ0m90C[14>ZS1I#5P3A1CoZS1JPCPoPdP0P>P6PoP5n101100000120103102R{#;A<{}3P|P~b2W014>oS1K#5eS1LPYP3E2W0P3O1Q0m90CZP2A1CjYS0mQ0l90CY14>XS1M#5P3A1CjXS1NPCPjPdP0P>P6PjP5n101100000120103102S1O#;Q1O?<}3P|P~b2W014>jS1P#5eS1QPWP3E2W0P3O1Q0l90CXP2A1ClWS0lQ0k90CW14>VS1R#5P3A1ClVS1SPCPlPdQ1>PUP3E2W0P3O1Q0k90CVP2A1CpUS0kQ0j90CU14>TS1T#5P3A1CpTS1UPCPpPdP0P>P6PpP5n101100000120103102S1V#;Q1V?<}3P|P~b2W014>pS1W#5ePSP3E2W0P3O1Q0j90CTP2A1CqSS0jQ0i90CS14>RS1X#5P3A1CqRS1YPCPqPdP0P>P6PqP5n101100000120103102S1Z#;Q1Z?<}3P|P~b2W014>qS1[#5ePQP3E2W0P3O1Q0i90CRP2A1ClQS0iA0CQz14>PS1\#5P3A1ClPS1]PCPlPdQ1>POP3E2W0P3O1A0CPzP2A1CrOQ0h90CO14>4S1^#5P3A1Cr4PCPrPdP0P>P6PrP5n101100000120103102S1_#;Q1_?<}3P|P~b2W014>rS1_#5ePNP3E2W0P3O1Q0h90C4P2A1CoNA0CNy14>AS0h#5P3A1CoAPCPoPdQ1LQ0CP3E2W0P3O1A0CAyP2Q0C91ClQ0C=0CxQ03,4>S1`#5P3Q0391ClPCPlPdQ1>Q04P3E2W0P3O1Q03=0CxP2Q0491CgQ04Q0g50CQ0B,>>P3Q0B91CgPCPgPdP0P>P6PgP5n101100000120103102S04#;Q04?<}3P|P~b2W014>gS03#5eQ0AP3E2W0P3O1Q0BQ0g50CP2Q0A91CHQ0AQ0f50CQ0@,>>P3Q0@91CHPCPHPdP0P>P6PHP5n101100000120103102S0A#;Q0A?<}3P|P~b2W014>HS0B#5eQ0?P3E2W0P3O1Q0@Q0f50CP2Q0?91CjQ0?Q0e50CQ0>,>>P3Q0>91CjPCPjPdQ1QQ0=P3E2W0P3O1Q0>Q0e50CP2Q0=91CtQ0=Q0d50CQ0;,>>P3Q0;91CtPCPtPdP0P>P6PtP5n101100000120103102S0=#;Q0=?<}3P|P~b2W014>tS0>#5eS1QQ08P3E2W0P3O1Q0;Q0d50CP2Q0891CuQ08Q0c50CQ0:,>>P3Q0:91CuPCPuPdP0P>P6PuP5n101100000120103102S08#;Q08?<}3P|P~b2W014>uS0;#5eS0?Q0<P3E2W0P3O1Q0:Q0c50CP2Q0<91CvQ0<Q0b50C1>>MP3A1CvMPCPvPdP0P>P6PvP5n101100000120103102S0<#;Q0<?<}3P|P~b2W014>vS0:#5ef_S0@P3E2W0P3O1Q0b90CMP2Q0@91ClQ0@Q0a50Cf`S0@,>>P3Q0@91ClPCPlPdQ1>faS1>P3E2W0P3O1Q0@Q0a50CP2Q1>91CGQ1>Q0`50CfbS1>,>>P3Q1>91CGPCPGPdP0P>P6PGP5n101100000120103102S0@#;Q0@?<}3P|P~b2W014>GS1a#5efcS1bP3E2W0P3O1Q1>Q0`50CP2Q1b91CtQ1bQ0_50CfdS1b,>>P3Q1b91CtPCPtPdQ1QfeS1>P3E2W0P3O1Q1bQ0_50CP2Q1>91CfQ1>Q0^50CffS1>,>>P3Q1>91CfPCPfPdP0P>P6PfP5n101100000120103102S1b#;Q1b?<}3P|P~b2W014>fS1c#5efgS1dP3E2W0P3O1Q1>Q0^50CP2Q1d91CoQ1dQ0]50CfhS1d,>>P3Q1d91CoPCPoPdQ1LfiS1LP3E2W0P3O1Q1dQ0]50CP2Q1L91CuQ1LQ0\50CfjS1L,>>P3Q1L91CuPCPuPdQ0?fkS0?P3E2W0P3O1Q1LQ0\50CP2Q0?91CtQ0?Q0[50CflS0?,>>P3Q0?91CtPCPtPdQ1QfmS1QP3E2W0P3O1Q0?Q0[50CP2Q1Q91CsQ1QQ0Z50CfnS1Q,>>P3Q1Q91CsPCPsPdP0P>P6PsP5n101100000120103102S0?#;Q0??<}3P|P~b2W014>sS1L#5efoS1dP3E2W0P3O1Q1QQ0Z50CP2Q1d91C;Q1d=0CwfpS1d,>>P3Q1d91C;PCP;PdP0P>P6P;P5n101100000120103102R0#;A<0}3P|P~b2W014>;S1Q#5efqP3E2W0P3O1Q1d=0CwP|fr,>>P3n010000000W1P3O1n200100000021000010000W1P3O1n200100000021000011000W1P3O1n200100000021000011000W1P3O1n200100000021000011000W1P3O1n200100000021000011000W1P3O1n200100000021000011000W1P3O1n200100000021000011000W1P3O1n200100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1P3O1n201100000021000011000W1X4CO4b0P6PC%}>S1dQ0HQ0IQ0JQ0KP?Q0JQ0LQ0MPnQ0NP?PIQ0OP?P=PnP?Q0PQ0QQ0NQ0SQ0TQ0UP?Q0VQ0SQ0WPnQ0TQ0SQ0XQ0Y%W6S0YDADADADADADADADACdS0S9HCdeQ0D9HCdeg00JdRd#WS0T%ZdS0W%{6S0V%z6S0U%x6Rd%J<R>#OS0Q%O?S0P'X,TdQ0P%OI'X,Td3aQ02,vdS02P3P8g00LUS1>g00M5R}'VQ1>1s38;1}dAr675CqS1>b8b9b:1D>?1D?I'QR7P3b7P7eQ0D,pC#oR7,D>1D7I'QeQ0TQ0WQ0VQ0UQ09#OQ0R#8#R#F#@#KR}#OS0R'X,TdQ0RQ0P5_6Q0Q5_6%8<#E#L#@#E#E#?R<#O'X,Td5adQ02Q1>b8b9b:Q09/D}1I}?/I>/D<'QP3b7Q09/DJR}Q06/I>/D<'Qe1IJ7R7/I>/D<,Q}eP:P`PLQ05,I7#\R7Q07C^eP8P5P31P7L9UMLeQ0HQ0IQ0JQ0KP?Q0JQ0LQ0MPnQ0NP?PIQ0OQ0Y7n?DADADAR?#]S0YPrPoPy%ZCRrQ0u'VQ0SP6PCQ1dP?CdS1d=`Cz51reQ0DQ0Y=`Cz51reQ0EQ0FP3PCQ0G/6=X4CRzA3ClwS0G93CqS0D93CpS0S93ClR?93CjRI93CoRM93CmRL93C1R793CFR}93ClR<93CkR>93CFRJ93CiRd93ChS0uQ0u90C3P2Q0vA0C5dQ0w/6=S0wP3Q0xPCPhPzQ0y/:=Q0yP6PeP3P|g00blRhPeP3PhPeP3Q0zP|P|n011040003100001000000S0yP|P|n011040003101041010400S0vP|n011050003001010410104X36S0uP=P3C=P|P~b2W0Q0{/6=eP:P3E2W0P3O1A0C8dP2Q0|A0C:JQ0}/6=S0}P3Q0~PCPiPzQ10/:=Q10P6PeP3P|PhPeP3P|Q0zP|n011040003100001000000RiP|n011050003001010410104X36RdP=P3C=P|P~b2W0Q11/6=ePEP3E2W0P3O1A0C9JP2Q0tA0CE>Q12/6=S12P3Q13PCPFPzQ14/:=Q14P6PeP3P|PhPeP3PhPeP3P|PiP|n011040003101041010400P|P|n011040003101041010400P|n011050003001010410104X36RiP=P3C=P|P~b2W0Q15/6=eRJPcP3E2W0P3O1A0CD>P2Q0sA0Cc<Q16/6=R>P3Q17PCPkPzQ18/:=Q18PdP=P3C=P|P~b2W0Q19/6=eP@P3E2W0P3O1A0CK<P2Q0rA0C@}Q1:/6=R<P3Q1;PCPlPzQ1</:=Q1<PdP=P3C=P|P~b2W0Q1=/6=eRkPaP3E2W0P3O1A0Cb}P2Q0qA0Ca7Q1?/6=R}P3Q1@PCPFPzPJP_P3E2W0P3O1A0C`7P2Q0pA0C_LQ1A/6=R7P3Q1BPCP1PzQ1C/:=Q1CPdP=P3C=P|P~b2W0Q1D/6=eP]P3E2W0P3O1A0C^LP2Q0oA0C]MQ1E/6=RLP3Q1FPCPmPzQ1G/:=Q1GPdP=P3C=P|P~b2W0Q1H/6=eP[P3E2W0P3O1A0C\MP2Q0nA0C[IQ1I/6=RMP3Q1JPCPoPz1:{=P{P6PeP3P|PhPeP3PhPeP3P|PhPeP3PhPeP3P|Q0yP|n011040003101041010400RmP|P|n011040003101041010400P|n011040003101041010400P|P|n011040003101041010400P|n011050003001010410104X36P=P3C=P|P~b2W0Q1K/6=eS0yPYP3E2W0P3O1A0CZIP2Q0mA0CY?Q1M/6=RIP3Q1NPCPjPzQ1O/:=Q1OPdP=P3C=P|P~b2W0Q1P/6=eR1PWP3E2W0P3O1A0CX?P2Q0lQ0S90CWQ1R/6=R?P3Q1SPCPlPzPkPUP3E2W0P3O1Q0S90CVP2Q0kQ0D90CUQ1T/6=RJP3Q1UPCPpPzQ1V/:=Q1VPdP=P3C=P|P~b2W0Q1W/6=ePSP3E2W0P3O1Q0D90CTP2Q0jQ0G90CSQ1X/6=RpP3Q1YPCPqPzQ1Z/:=Q1ZP6PeP3P|PhPeP3PhPeP3P|Q0vP|n011040003101041010400P|P|n011040003101041010400P|n011050003001010410104X36P=P3C=P|P~b2W0Q1[/6=ePQP3E2W0P3O1Q0G90CRP2Q0iA0CQwQ1\/6=RqP3Q1]PCPlPzPkPOP3E2W0P3O1A0CPwP|Q1^/6=RFP3n010000000W1P3O1n200100000021100010000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1X4CO4b0Q1d9HCzeQ0Y9HCzeQ0EQ0FP3PCPzPyA0C3yP2A1Cl5A0C5xQ0wP3A1Cl8PCPlPzPkP:P3E2W0P3O1A0C8xP2A1Cg:Q0g90C:Q0}P3A1Cg9PCPgPzQ04/:=Q04PdP=P3C=P|P~b2W0Q03/6=ePEP3E2W0P3O1Q0g90C9P2A1CHEQ0f90CEQ12P3A1CHDPCPHPzQ0A/:=Q0APiP=P3C=P|P~b2W0Q0B/6=ePcP3E2W0P3O1Q0f90CDP2A1CjcQ0e90CcP>P3A1CjKPCPjPzP1P@P3E2W0P3O1Q0e90CKP2A1Ct@Q0d90C@P<P3A1CtbPCPtPzQ0=/:=Q0=P6PeP3P|PhPeP3PhPeP3P|PhPeP3PhPeP3P|PmP|n011040003101041010400P|P|n011040003101041010400P|n011040003101041010400P|P|n011040003101041010400P|n011050003001010410104X36P=P3C=P|P~b2W0Q0>/6=eRmPaP3E2W0P3O1Q0d90CbP2A1CuaQ0c90CaP}P3A1Cu`PCPuPzQ08/:=Q08Q0uP=P3C=P|P~b2W0Q0;/6=eR}P_P3E2W0P3O1Q0c90C`P2A1Cv_Q0b90C_P7P3A1Cv^PCPvPzQ0</:=Q0<PdP=P3C=P|P~b2W0Q0:/6=eP]P3E2W0P3O1Q0b90C^P2A1Cl]Q0a90C]PLP3A1Cl\PCPlPzPkP[P3E2W0P3O1Q0a90C\P2A1CG[Q0`90C[PMP3A1CGZPCPGPzQ0@/:=Q0@PdP=P3C=P|P~b2W0Q1a/6=ePYP3E2W0P3O1Q0`90CZP2A1CtYQ0_90CYPIP3A1CtXPCPtPzPmPWP3E2W0P3O1Q0_90CXP2A1CfWQ0^90CWP?P3A1CfVPCPfPzQ1b/:=Q1bPdP=P3C=P|P~b2W0Q1c/6=ePUP3E2W0P3O1Q0^90CVP2A1CoUQ0]90CUPJP3A1CoTPCPoPzQ0yPSP3E2W0P3O1Q0]90CTP2A1CuSQ0\90CSPpP3A1CuRPCPuPzP}PQP3E2W0P3O1Q0\90CRP2A1CtQQ0[90CQPqP3A1CtPPCPtPzPmPOP3E2W0P3O1Q0[90CPP2A1CsOQ0Z90COPFP3A1Cs4PCPsPzQ0?/:=Q0?PdP=P3C=P|P~b2W0Q1L/6=ePNP3E2W0P3O1Q0Z90C4P2A1C;NA0CNwQ0h/6=P3A1C;APCP;Pz1:0=P0PdP=P3C=P|P~b2W0Q1Q/6=eQ0CP3E2W0P3O1A0CAwP|Q1`/6=P3n010000000W1P3O1n200100000021000010000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n200100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1P3O1n201100000021100011000W1X4CO4b0AHCzyRzePze1V6=Q1_/:=eQ0X,:{1:{n1V6n3lQ1KQ0X':Q1K/:n'keQ1K#ueA1rywRnPrPyQ00PCPeP3P|Q0zn10110100020020000000X3rQ01PwP3E2P|P~b2W0%SneMojUUUUUUUUUUUXI6WJWGW=X_BX^BX]BX\BXOBXNBXWBXVBXUBXTBXSBXRBXQBXPBXFBXEBXDBXCBXBBXABX@BX?BXMBXLBX[BXZBXYBX`BXHBXXBWKW>o"). Qed.

(* [comment removed for export] *)
Definition FMT_USAGE : Z := 0x15836.
Definition FMT_USAGE_chars : list Z := [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10]%Z.  (* [comment removed for export] *)
Definition FMT_CANTOPEN : Z := 0x1d671.
Definition FMT_CANTOPEN_chars : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10]%Z.  (* [comment removed for export] *)
Definition FMT_READERR : Z := 0x1d686.
Definition FMT_READERR_chars : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10]%Z.  (* [comment removed for export] *)
Lemma fmt_usage_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_USAGE (zb8 FMT_USAGE_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_USAGE FMT_USAGE_chars. Qed.
Lemma fmt_cantopen_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_CANTOPEN (zb8 FMT_CANTOPEN_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_CANTOPEN FMT_CANTOPEN_chars. Qed.
Lemma fmt_readerr_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_READERR (zb8 FMT_READERR_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_READERR FMT_READERR_chars. Qed.

End CANSEC3.
Ltac pcs_inst A BY CH PRE :=
  intros; eapply printf_common_str1 with (pre := zb8 PRE); pci A BY CH.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Definition printf_common_s_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (Sa : Z) (sstr : list byte) (RLO RHI : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_layout m -> a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  rw_cells bsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)] ->
  (bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z ->
  bytes_at bsegs m Sa (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
  (Sa + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z ->
  app_blk Sa (Sa + (Z.of_nat (length sstr) + 1)) -> (0 < Sa)%Z ->
  unpoisoned m Sa (Sa + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
  (RLO <= Sa /\ Sa + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  rng RNG (bv_unsigned a2) 8 -> rng RNG Sa (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44394) fc None m (seg_rom bsegs)).

Theorem printf_common_usage_spec : printf_common_s_stmt FMT_USAGE 16.
Proof. unfold printf_common_s_stmt. pcs_inst FMT_USAGE fmt_usage_bytes FMT_USAGE_chars ([117; 115; 97; 103; 101; 58; 32]%Z). Qed.
Theorem printf_common_cantopen_spec : printf_common_s_stmt FMT_CANTOPEN 20.
Proof. unfold printf_common_s_stmt. pcs_inst FMT_CANTOPEN fmt_cantopen_bytes FMT_CANTOPEN_chars ([99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]%Z). Qed.
Theorem printf_common_readerr_spec : printf_common_s_stmt FMT_READERR 22.
Proof. unfold printf_common_s_stmt. pcs_inst FMT_READERR fmt_readerr_bytes FMT_READERR_chars ([99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]%Z). Qed.

Corollary printf_common_d_stmt : printf_common_int_stmt FMT_D 3.
Proof. exact printf_common_d_spec. Qed.
Corollary printf_common_toobig_stmt : printf_common_int_stmt FMT_TOOBIG 32.
Proof. exact printf_common_toobig_spec. Qed.
End CANSEC4.
