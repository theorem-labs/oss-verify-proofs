(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptStderr O23LeptBase O23LeptErr O23LeptCmap O23CmapFill.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.OL Require LeptCmapDeser.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocOL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23RelocMusl O23LeptEnv O23LeptG.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptCmapDeser () := "C79OSSVerify5KrLib6Common9Leptonica2OL=LeptCmapDeser6cdepthC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic2or00C79OSSVerify5KrLib6Common9Leptonica2OL=LeptCmapDeser<cdepth_casesC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC79OSSVerify5KrLib6Common9Leptonica2OL=LeptCmapDeser;cdepth_fitsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL=LeptCmapDeser7blk_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs4lctx00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9Leptonica2OL8LeptBase3LLGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs3Cok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs1W00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL8o23_leptC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib3O238O23LeptG9o23_pinsGC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common9Leptonica8LeptDefs5c_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4c_A0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib6Common8Mallocng9AllocSure5aroomC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9Leptonica8LeptDefs7cs_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs5POSTMC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL=LeptCmapDeser9cmapd_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib3O23@O23LeptCmapDeser9cmapd_newC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC79OSSVerify5KrLib6Common9Leptonica2OL=LeptCmapDeserDpixcmapDeserialize_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL;o23_code_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL<o23_sites_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL:o23_img_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocMusl6o23_rwC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4LSTKC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL8LeptBase3LSFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptRoom7RK_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptRoom7RB_cmapC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib3O23;O23LeptBase4LL16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptBase3LSFC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cdepth (nc : Z) : Z := if (16 <? nc)%Z then 8 else if (4 <? nc)%Z then 4 else if (nc <? 3)%Z then 1 else 2.
Lemma cdepth_cases : forall nc, (cdepth nc = 1 \/ cdepth nc = 2 \/ cdepth nc = 4 \/ cdepth nc = 8)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCmapDeser ()) [] "h03RLTh12ncp;1p;3p;2g0000j14Tg001=j11Tg001[j30Tg0025j12Tg002Zj23Tg0034g004GR0f0R1#4R2g004eR3#1500%23R3#19002%23R3#19002%23#19002'3'3'3]1P1b0o"). Qed.

Lemma cdepth_fits : forall nc, (1 <= nc <= 256)%Z -> (nc <= 2 ^ cdepth nc)%Z /\ (2 <= 2 ^ cdepth nc <= 256)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCmapDeser ()) [] "h03RLTh12ncp;1p;2g001=j13Tg005Jj21Tg0025j10Tg005fj22Tg0000j15Tg006Aj24Tg006^g004Gg004eR0#3f0R1'1%00R0#0#0#0#0#0#0#0#3R2,11'2f1R3%30R0%53'4R3'111031132'2'2[]1P1b0o"). Qed.

Section CmapDeser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition cmapd_new (C : lctx) (A A' : AS) (m' : word -> option byte) (cm arr nc : Z) : Prop :=
  (1 <= cm)%Z /\ (cm + 24 <= alloc_top (c_vm C))%Z /\ (cm mod 16 = 0)%Z /\
  (1 <= arr)%Z /\ (arr + 4 * 2 ^ cdepth nc <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ cm <> arr /\
  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (4 * 2 ^ cdepth nc)%Z /\
  (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  CMAPat m' cm (CMAPV arr (cdepth nc) (2 ^ cdepth nc) nc 0).
Lemma blk_rdn : forall C A m md (p : word) (n a : Z) (k : nat), Cok C -> W C A m md -> live A p = Some n ->
  (u p <= a)%Z -> (a + Z.of_nat k <= u p + n)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCmapDeser ()) ["CmapDeser"] "h01Ah11Ch23RLTh31ah42bsh51kh61mh72mdh81nh91pp;6p;3p;2p;1p;5p;8p;4g0080j6GTg009>j3FTg00:Gj3?Tg00;Lj3<Tg00<Uj2ETg0025j10Tg00=Vj12Tg00>4j17Tg00>Wj11Tg00?9j2=Tg00@>j5;Tg00ABj8:Tg00BDj49Tg00CGj28Tg001[j34Tg00Cij26Tg005Jj25Tg00DSj1CTg00E3j23Tg00EPj1@Tg00F0j1ATg00Foj2BTg00GUj4>Tg00HMj2DTg00HgR0g00IbR1p,2ALR2p,2CLR3p,3ASRR4p,4PINSEGAF234R49?23A<234R5,E2g004e#0#0#0R6#0#0#0#2R7#7R8%26#7R6#1[g00J^g004GR9g00KTP2P3P41=01R1f7R:D;P2P3P4P1f8R1P:f6R4f5R3G:%19P2P5P1P3C9f4R1,89341674/51%C1,33167:/34'5%@6R6%16%A0f;1B7:P4C>f0R4,8634X46'D[[[[[]5^39]8^98]7]6]0]1P4b2o"). Qed.

Theorem pixcmapDeserialize_W : forall C A m md regs (s dp nc : Z) (pb : word) (kb : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 4 -> getr regs 12 = Z_to_bv 64 nc -> (1 <= nc <= 256)%Z ->
  live (c_A0 C) pb = Some kb -> (u pb <= dp)%Z -> (dp + 4 * nc <= u pb + kb)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmap <= kR)%Z -> (RB_cmap <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists cm arr, getr regs' 10 = Z_to_bv 64 cm /\ cmapd_new C A A' m' cm arr nc)) ->
     aroom A' vm' (kR - RK_cmap) (bR - RB_cmap) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x71f08 : word) m al_rom) md) S.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCmapDeser ()) ["CmapDeser"] "h01Ah12A'h21Ch31Hh41Sh53arrh62b1h72b2h82bRh92cmh:2dph;2kRh<2kbh=1mh>2m'h?2mdh@1nhA2nchB2pbhC4regshD5regs'hE3rethF1shG3vm'hH3RLThI1bhJ1qp;3p;2p;1p;5p;8p;4p;7p;9p;:p;6p;=g00L3j3kTg009>j3ZTg00:Gj3XTg00;Lj3iTg00<Uj2aTg0025j12Tg00=Vj1GTg00>4j1<Tg00>Wj1LTg00Lnj13Tg00MSj2VTg00?9j2hTg00@>j5PTg00ABj8ETg001=j1@Tg00N?j2?Tg00Nbj3=Tg00Foj2:Tg00OEj2[Tg001[j34Tg00Oej4MTg00Pij2HTg00E3j2ATg005Jj26Tg00QFj1YTg00R>j2KTg00S>j2NTg005fR0j2BTg00T8j4WTg00BDj4FTg00CGj2UTg00Cij27Tg00U;j2TTg00UXj1gTg00VOj7STg00WSj2RTg00XMj2fTg00YSl9QTg00ZWl:eTg00HMj2DTg002Zj2OTg00F0j1bTg00[gj1`Tg00\dj5JTg00]]j2ITg00^Rj3CTg00_Qj3_Tg00`5j2^Tg00`Oj7cTg00aRj6dTg00anl=]Tg00cIj2\Tf5R1g00HgR2g00dBg00eAg00IbR3g00fAg00g?g00h<f4R4f3R5f2R6f1R7f0R8M=]p=j%28#2p=11\67=458p=0%28#@p=8%38#2p=5%28#3p=9%38#3p=>g00i8R99=78p=;p,2fxR:p,2ALR;p,2CLR<p,3ASRR=p,4PINSp,3P169k;<EjAZ;<=R>9X;<R?Ai;<>R@,a;RAg004eRB#2RC#2RD#2RE#2RF#1RG#GRH#<RI%GE#<#L[REg00J^RJ%3CRK#GRL/VIRMg004GRNg00iTROP;P<P>1h23R3f;RPDPP;P<P>P3f<RQPPf:RRf9RSGEPIPS%@CRCP91?LCd5=Lf8RT,:HRUC0%@F,[Sg00jMRF54NRVP;P<P>f?RWCMg00jk'H%3DRX#2#1RY#8'ARZg00kn'A/6RP;P<P>f@R[CM,6PR\PIf=R]%@BR^P91?L^d5=Lf7R_C0%YTR`PIPW%@DRDP91?LDd5=L%3X#5#5#9#9,K2%3KRX#3#5#>#>#9#>#1#8'NC0PIP[%8KRKP91?LKd5=LRaf>,:HRbC0PIfARc%@XRXP91?LXd5=L1:HDRdC0PIfBRe%5BRf#8RgP91?Lgd5=L1:HWR9C016^[%2G#8,6['BRG%LNRhP;P@P;P<P>fHCWP[CF1UNW34Ri17HcfCRj'6RkfD1TDj'A17He/Ac'6RjP;P<P=fLfJ#gP7P8FSRlg00m3Rm/66Rng00n9Ro/66Rpg00o?RqP;P<P>P3fTRrP5P6fQRs,R7RtGE1fs7RuP;P<P>P3fVR3fURvPsPrP4M9QPIP5Pa1:HFRFC0P;P@P_P8CFP;P@fWP8CF54h^JIRh'BPIP1Pa1:H7RaC0P;P<P=fYR@fXRwPTP_P7P8fRRxM:e'BX5N,DNX9N,DN'OP;P<P=P_P11HQm1HPoFSRo%b2RmP:P1fOR=P_%`;RyDJf6/R3'IRzfNR{3C[[[[[^DM]G^>E^1AP:fMR|%3f#1#1,K2%5Y#9#1#>#1#8'NP=PyDJ/I{fFRY5Cm[[[[^8N^;N[[[[[[[[[[[[[[[[]4^EI^<N^BI^AN^:N]F]C]?]=]0]2g0106Rm%<8R2%<7RfP0%<6?4781756175754NR0[1767176854N%<5?467[R}%<4?456\0A_678P8n2001000000120000000W7W6W@P}^7f^62^@mP8PH%3B#5#1#>#>#5#1#9#1#8Rm,:HR21;HmRf1^Nm17H217Hf54NdO4b3A4I2fPIP2P;P<P>g010TR2PPDPP;P<P>P2PQPPPRPSGEPIPS1;LCPUC0g011M,AZ/6RPIP]1;L^P_C0PIPW1;LD%2B#9#1#9#>#5#5#9#1#1#8,:HC0PIP[1;LKRKPbC0PIPc1;LXPdC0PIPe1;LgP9C0P;P<P>P2PrP5P6PtGEP;P<P>P2P3PvPsPrP4M9QPIP5PKPFC0/BhPIP1PKPaC0P@PwPTP_P7P8PxFc'BX5N,DNX9N,DN'Og012ER_?Cz{\o[[\u[^DM^Gq^>E^1AP:P|PxP=PyDJ/I{=C_Y[\p\n\l^8N^;N\j\k\i\G[[[[\`[\\[\V[[[^4O^EI^<N^BI^AN^:N^FN^CM^?J^=E^0A^2?XIIP7PfP8Edb3bHo"). Qed.

End CmapDeser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
