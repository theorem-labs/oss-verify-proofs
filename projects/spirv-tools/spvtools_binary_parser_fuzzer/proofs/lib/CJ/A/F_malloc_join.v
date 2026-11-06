(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_malloc_join () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapC69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2CJ1A9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C69OSSVerify5KrLib2CJ4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2CJ4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC69OSSVerify5KrLib2CJ4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2CJ4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2CJ4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib2CJ4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree3memC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI69OSSVerify5KrLib2CJ4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI69OSSVerify5KrLib2CJ4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2CJ4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2CJ3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2CJ3Lib3Mem2waC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2CJ3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2CJ3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2CJ3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2CJ3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib2CJ1A=F_malloc_join7enf_hypC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree5implTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revK69OSSVerify5KrLib2CJ1A9Malloc_fp4mrel01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_le".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition glue_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a3 a7 t3 t4 t5 t6 nw idxw ctrw gw s0v rav : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) (junk : list byte) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 nw s1
                  (Z_to_bv 64 MLOCK) a1 idxw a3 ctrw (wz 0) gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17014) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 idxw; C8 gw; C8 ctrw; C8 idxw; CB 16 (skipn 32 junk); C8 s0v; C8 rav].

Lemma unk_agree_ext st st' o m :
  unk_agree st o m -> s_regions st' = s_regions st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_groups st' = s_groups st -> unk_agree st' o m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["AC_1"] "p'0h02ghh11Hh21bh32Hch42Hrh51gh63ridh72EGh82ERh92ESh:2Hbh;2Hfh<2Hkh=2Hoh>2Hxh?2NGh@2UAhA1hhB1mhC1ohD3offhE1rhF1shG2sthH3st'i001xp;3p;4p;1p;2p;6g0000R0p4p70R1p1000hp4p710p8P1p1001FR2p4p710p8P1P2p4p7210p8P1p1001_p4p73110p8p10021p4p70g002iR1p4p710p8g003Gj3OTg004Dj4LTg004Xj19Tg005Uj30Tg005oj2;Tg006mj4XTg007Kj6WTg007lj11Tg008hj1FTg009Jj4ITg009cj25Tg00:Ej1STg00;?j1[Tg00<8j1ZTg00=7j27Tg00=Sj2CTg00>Pj1BTg00?Mj3MTg00@Lj1KTg00@ej6HTg00AAj2VTg00Aaj1UTg00BFj1DTg00Bkj1TTg00CIj2JTg00CfR2j2?Tg00D@R3j26Tg00D[j4GTP1j6RTg00E6j4ETg00EPj6QTg00Edj2PTg00F@j3NTg00F]j3YTg00G:R1g00GXR4f3R5f2R6f1R7f0R8EQp=@1P67/68p==f6R9f5R:g00HTR;f4R<P5P6P7EQ;08p=2g00INR==N18p=<A0178p=AAY1=8p=31678,66p=8AN1=7=018p=:1P<51J78,76'6p=4A0167/68p=>g00IlR>g00JhR?AO578P1g00K`R@g00L9RAP4CLRB%95%9<30g00LWRC1;:81;9830^61P0P1P@P=g00MSRDCXREP1P@PAP=PDg00MlEWRDP;CLRF%1:%1930%F4RGPBP1P@PAP4CIRAP5f:R@#9C@154630g00NJ%S5g00OE30g00P@%[<#Z,757=5g00P^RHf=RI/;9/C<%B530f>RJf7RK;M:#KPBf?RL#9PBPAf9RMP8C@f8RN,5450GX5BP<f@RO#9RPf;RQEHPBPAPNPPC@154K50GPC1;OM1C8N%BK50HXFCP6fARC/;MRGPQPMO1EH1CGK%B950HPJP@PMPNPKP7P:P<P8fBRH?M@NRGP21V1=RP%F;RAPPPFP0PEPDP;CIRDP7fERE#115;8R0F2%<7RB/AI%37RRg00Q[#U#D#D#TRS,JRRT,7Q7=Q38X0;,?;X2Pg00R@RUP8PAPPPFPDP7fGRV#1P0F21ABL17IT9=RI38X0;,?;P2P;PAPPPFPDP6fHR2#1P0F21:6O%36R6PJPJP6PSD438X0;PUP8PAPPPFPDP<fJR6#1P0F21:<H%3<RHPOPOPHPSD438P3PAPPPFPDP:fKRH#115;7F2%<:fCRO%3:RLPCPCPLPSD43>PUP8PAPPPFPDPKfMRK#115;5F2%<NfF%3NRNfDR5P5PNPSD43>P31:MV%3MRVPEPEPVPSD4PUP8fIRU,:Qf<#3RQP2P2PQPSD4POPPPAPPPFPDP7fT#1P0F21ABK17HT9=RH38X0;,?;X2PPIP;PAPPPFPDPJfS#1RRP0F2%<JfLR0%3JRTP6P6PTPSD43>RT'6X0;PMPFPRPAPPPFPDPJP815;@F2/6TX5FPAPPPFPDPIPR15;MF21:IHRH%3IRIPUPUPIPSD4RS'6P:PHPSP7P8CGCGfR#1P0ERCECEO1W>W;P7P8O2n2001000000121000000W1W:P7P8O2n2001000000121000000W1X0;P7P8O2n2001000000121100000W1X2PP7P8O2n2001000000121100000W1%KGeO9b3b4W?W3W=W<W4XA=XD=XE4X61AO9:<eW7W9W8W@XB?WCXH>WGo"). Qed.

Lemma unk_agree_munch st o m m' W :
  unk_agree st o m -> munch W m m' ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> disjoint_from W (r_base r) (round_up_pg (r_len r))) ->
  (forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
  unk_agree st o m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["AC_1"] "h06__sat3h14__x1h24__x2h34__x3h41rh53ridh62Hah77__arithh84__ffh96__sat2h:8__varmaph;5__with<1oh=2B0h>2B1h?2HBh@2HDhA2HchB2HkhC2HohD2HrhE2MUhF2NGhG2UAhH1WhI1ahJ1hhK1mhL2m'hM3offhN2sthO1zp;1p;3p;4p;2p;6p;7p;8g00BFj19Tg00R]j1RTg00S;j1PTg008hj1GTg00S^j1UTg003Gj3KTg00T>j3hTg004Dj4eTg009Jj4`Tg004Xj1@Tg009cj2FTg005Uj33Tg00:Ej1TTg00U5j12Tg00Uoj3sTg00CIj20Tg00Bkj1LTg00Vnj2gTg00Edj26Tg00D@R0j27Tg00=7j28Tg005oj2aTg00=Sj2_Tg00>Pj1^Tg00?Mj3]Tg00@Lj1\Tg00WKj1?Tg00X=j2ITg00Xgj2HTg00Y`j2[Tg00ZHj3ZTg00Zlj2YTg00[Mj2OTg00[gj1XTg00\Gj2ETg00\ej4WTg00]Cj1VTg00]aj1wTg00^Lj2STg00^oj2CTg00Aaj1vTg00_Rj1uTg00`4j3QTg00`Wj2rTg00a9j2qTg00aej3pTg00bDj4oTg00c6j6lTg00d8j1=Tg00dWj2:Tg00e@j3>Tg00eij2JTg00fUj3MTg00g5j3iTg00gXj2jTg002ij6kTg00@ej6fTg00EPj6mTg00;?j1nTg00<8j1dTg00hSj4NTg00i>j7cTg00ibj7bTg00jFj8tTg00G:R1g00GXR2f3R3f2R4f1R5f0R6Emp=B%n6#dp=4g00P@R7/66p=1g00INR8P5g00jjP6CNp=;P5g00kQR9g00l0R:P:g00lPR;P6g00m0Fcp=5P8P5g00mPP6CNp=DP4P9P:P:P;P5P6Fbp=AP3P9P:P:P;P4P5P6Gtp=<g00Ilg00JhR9g00Q[R<#9R=#9#9R>#9#9#9R?#RR@#P%R>#P#GR>[g00n7#Uf4RA?K34Ah534%G2RBP1g00K`RCg00L9RDP2CeREP1PCPDP2C`RDP5f8RC#@CB1F26RF33g00NJRG%T5g00OERH33f6RI%24%443s[[^42^51PEPDP5f9RJ#@CB=3BF%25RF#1%45,0F%L=RF%L?R?'gRK'6'7[^42^51PEPDP3f<RD#@CB1F2453B%T3=3GH%13RH%4A,83'7g00P^f?RG/aI/_A%^333f@RBf7REf5RL3]#\P>PG%2ERM/0I#?RNO1PG%2CRO/0E#?O1=3>6X<>f;R>PNPJPCPEPAO3%1M%4E,0M/6K'7P0%1O%4C,0O/6K%2J/0C#?,I@,HGP6f:#2#1%2>%4>'0/6KP8%2DRO/0>R0fC/H6XO8fBPO%4DP0PGf=PDPJPCO41[F?RJ187FRO%1?187K[RM[RP%1FRQg00nlRRAZF?5UW6R?%1K\R^6QRQP5g00oH1Y7F'OPOeO1ROPMg00onRR#XRS%URRTP81E84P51E83CWRU%V8RV%w8RW1S87RX1C8=R=';,5W%v<,C8RY,D=,5W5AWRZ%u:R:1C8<R<AQ8<=R=';,5WAQ8<YRY,D=,5W5AWC<1rW;R;P6P4g010ZR[g011:R\'O1q64=3[\dAp875CoR7b8b:b;X18X28X38%15R\1854'71054R[,651053,8['7[^18^28^38P6%4BR[PG%2BR]P>O4b7b0b9b0El%?0,I@PJPPP?PQPOPMg011ZRM#=RO#=RQ#=R?#=,:81:8O1:8MRM5>85>8g0129RO'J1:8?1:8Q=>8M5>8/JO=MRS5MRPTPUPVPW1S8F=i8@R@,;Y,5WP:PW1;X<,5WP:PWPZP:1;X=,5W1D=@,5W5AWC<C<C<P;P7b8b:b;X18X28X381064/6K183A,7H103ARH#118HK'7[\\[^18^28^38P6P[PGP]PAPLP>O6b7b0b9b0,j0EkW>W=P5P6O2n2001000000121000000bIO2PBPNO1PDPCPEPIPLPAP3P4P5P6O9EfWFWAWCWBWDXJ8XM8X42X51AKCELeW?W@WEWGWHWLXK9W<WNo"). Qed.

Definition enf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (junk : list byte) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a3 a5 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64)
       [C8 (wz idx); C8 (pw st2 (Some g)); C8 (wz (sxv (c_mmap_counter (ctx st2)))); C8 (wz idx); CB 16 junk; C8 s0v; C8 ra] ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       malloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1
                   a0 a1 (wz idx) a3 (wz (sxv (c_mmap_counter (ctx st2)))) a5 (pw st2 (Some g)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17014) fc None m1 (seg_rom asegs)).

Lemma mrel_same st st' :
  s_regions st' = s_regions st -> s_next_rid st' = s_next_rid st -> s_reserved st' = s_reserved st -> mrel st st'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["AC_1"] "h03EN0h17__arithh24__x1h34cstrh45cstr0h52ENh62ERh72ESh81Hh94__ffh:8__varmaph;5__with<1gh=1nh>1rh?2r'h@3ridhA2sthB3st'hC1xhD1yp;4p;1p;3p;2p;7p;6p;5p;<p1012ep60621002R0p1013dp4p710p8P0p1014Yp4p7210p8g004Dj4\Tg004Xj1:Tg005Uj30j1DTg015Sj12Tg00AAj2[Tg00S^j1ETg016Qj1BTg008hj1TTg009Jj4STg009cj2=Tg00:Ej1<Tg00U5j1>Tg00;?j19Tg00EdR0j21Tg00D@j24Tg00[Mj25Tg017OR1j13Tg017mj2VTg018Nj3UTg018kj4@Tg019Rj17Tg00[gj1RTg00\Gj2QTg00]Cj1PTg00]aj1MTg00^oj2LTg00hSj4KTg00i>j7JTg00`Wj2ITg00a9j2NTg00aej3HTg00bDj4OTg00D[j4;Tg002ij6?Tg00E6j4GTg01:5R2j2CTg01:Qj4YTg01;<j5XTg00EPj6WTg01<6l<FTg00G:R3g00GXR4f3R5f2R6f1R7f0R8EWp=8g00INR9?078p=6P3P9P8P1P7P6P5f4R:f5R;f6R<f7R=f8R>M<Fp=AP3P9P2P1P0g01<[P;P:P5P6P7P8M<Fp=Zg00IlR0P3g00K`R1g00L9R2P4C\R?%:8%:730%27%265031[99#E%B6%B530P:P5%T4R@P?P3P1P2P4CSR2P7%:<R1C81=48RA30P4P?P2P5%:=RBC8=0@Ag00NJRA%<8%<6RC30%>8%>6RD'6%96RE%98'1'4'4'4X?4P7P?PBP?P2P5P8C81=4650@A0ACC16DD11EE'4'4'4X<?P?P2P6PBC81=4750@%<7R@=0A@RB%>7R2/62R?%97RE/1ERE'4RD'4P8PBPD15A@P?PE1592%2<R<%2=R=503%3<R2%3=RE'6R?%D3R@%D9RA%37%38'6A03781V783UXD3XC3RDP<P21592P=PE159EM9AP:C@P?%7=g00P@R=/1Ef9#2RE#7%3E,1=g00onRE#R%EE1Q97%P9%M9REg00kQg00l0R?P?g00lPR?P9g00Q[,L9RBg00jjPBCKg00m0FJ1IE?P8P6g010ZR?g011:RE'51N86=0?EdAH9=7COb9b:b;X29RE1188^29R?P8%9;O1b1b4b3b0C;C;C;P1P;E?CGW8X>4X@3P3%2:R:%2;/C8X=31C::%3:R;/1;P:P;159;R4P:P;P4EZ%25R5=03:%35R3/6;R1P@PAPDP5P31593P:P;P4M9AP7C@P1%7:11=;%7<11=2PEP?P8%2>#3O1b1b4b3b0CYP5P7E?P8DXW7W5W6XB0WAo"). Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End FASTCORE.

Definition fail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)).

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis MED0 : rw_cells asegs m0 MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

End ASCALL.

End AC_1.
