(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2LeptStderr O2LeptBase O2LeptErr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.OL Require LeptCmap.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocCode O2RelocSites O2RelocImg O2RelocOL.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2RelocMusl O2LeptEnv O2LeptG.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2LeptCmap () := "K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec6v_sllwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC79OSSVerify5KrLib6Common9Leptonica2OL8LeptCmap6sllw_1C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib2O27O2LeptG8o2_pinsGC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL8LeptCmap@pixcmapDestroy_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs4lctx00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib6Common9Leptonica2OL8LeptBase3LLGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs3Cok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs1W00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common9Leptonica8LeptDefs5c_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common9Leptonica;LeptStructs6CMAPatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica;LeptStructs5c_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4c_A0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9Leptonica8LeptDefs7cs_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs5POSTMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib6Common9Leptonica8LeptRoom6roomtrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL:o2_code_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL;o2_sites_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2RelocOL7o2_leptC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib6Common9Leptonica;LeptStructs5cmapv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4LSTKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib2O2:O2LeptBase4LL16C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptCmap ()) [] "h03RLTh11dp;1p;3p;2g0000j12Tg000Nj31Tg000hj10Tg001Mj23Tg001gj18Tg002Ej17Tg002hj24Tg003Nj25Tg004Ij26Tg004fg005nR0f0R1g006LR2#2R3510%02R2#2R49101%02R2#29101%02R2#29101'3'3'3%02#0#0#8R2#71423f1R3,42'51643,4231[]1P1b0o"). Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x49840 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cm) ->
  CMAPat m cm cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some k ->
  live (c_A0 C) (Z_to_bv 64 cm) = None -> live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None -> cm <> c_arr cv ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 cm) = None -> live A' (Z_to_bv 64 (c_arr cv)) = None ->
     (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1c9d0 : word) m al_rom) md) S.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptCmap ()) ["Cmap"] "h01Ah12A'h21Ch31Hh41Sh52b1h62b2h72cmh82cvh91kh:1mh;2m'h<2mdh=1nh>2pph?4regsh@5regs'hA3rethB1shC3vm'hD3RLThE1bhF1qp;3p;:p;2p;1p;5p;8p;4p;9p;6g0071j3jTg007il:iTg009;j3\Tg00:Dj3YTg00;Ij3hTg00<Rj2bTg000hj14Tg001gj1HTg002Ej1;Tg00=Sj1FTg00>5j16Tg00>Zj2VTg00?Fj2UTg00@Kj5RTg00AOj8ATg0000j13Tg00BQj2CTg002hj22Tg00C4j2^Tg000Nj30Tg00CTj4NTg00DXj2[Tg00E5j2@Tg00ERj2GTg00Enj1ZTg00Ffj2MTg00Gfj2LTg00H`j1XTg00I@j1WTg00J?j19Tg00J^j4DTg00KVj2KTg00LSj2?Tg00M5j3TTg00N=j48Tg00O@j1>Tg00PGj4STg00QJj1gTg00Qlj1ETg00REj2QTg00S?j2fTg00TEl9PTg00UIj1dTg00V@l9cTg00WEj1aTg00XBj5JTg00Y;j2ITg00Z0j3BTg00Zoj2=Tg00[Yj3`Tg00\=j3OTg00\`j2_Tg00]:j6eTg00]Vj2]Tf5R0f4R1f3R2f2R3f1R43O']f0R530p=7%65#4p=:%45#6p=5%65#6p=<%45#4p=1p,2fxR6g00^OR7g00_Gg00`Cg00a@R8p,2ALR9p,2CLR:p,3ASRR;p,4PINSp,3P169j9:M:iA\9:;R<9Y9:R=Ah9:<R>,b9R?g006LR@#4RA#4RB#4RC#4RD#4RE#4#HRF#;RG%HC#;RH#F[RIg00b9RJ%6ARK#HRL/VGRMg005nRNg00boROg00d8RPP9P:P<1U78R8f;RQDRP9P:P<P8f<RRPQf:RSf9RTGAPGPTPL%3ARAg00e1RU1CLAdf8RV,2FRWE7%3D,^Tg00eMRD50NRXP9P:P<f?RYCNg00ek'[%3E'@g00fn'@/GSRE1GQSRZ%3CRC,@QP9P:P<fAR[CN'GR\PGf>R]PL%3@R^PU1CL^dPVE7%ZTR_PGf@R`PL%3BRaPU1CLad%6BRB#6#:#:#5#5,M7%6K#<#5#<#:#<#:#1#3'LE7PGP[PL%4K#3RKPU1CLKd12FYRbE7%XHRH#FRc%W7RdfDRe12F`Rfg00h0#9#9#9#9#9#9#9#9RgCD1KgY,?HRh30fERi?T`YRY%FNRjP9P>fG12F[C8%:@Rk#1#3,?N30RlP9P>fH%>[,2FC81?N`50jRmP9P>P9P:P<fJRnCSfCRo,2FC8%gNRp50jRqP9P>P9P:P<fKRrCS%>o,2FC8=0jpRs%>e90Ni#ERig00hORtP9P:P<P8fQRuP2P3fNRv,Q4RwGA1fv4RxP9P>P0fLR0,2FC8=0jpRyP9P>f6%>0,2FC8=0jpRpfORz,2F90G5#E%>z,2F90G4#EP9P>PSP3C8P9P>fWR>P3C850j[[^FGRjP9P:P<P8fVR8PVfP/@CRCfTR{f7R|M9PPdPV12FuR}PgCD1KgD,?HRH50cP9P:P;P>fU#dPSPVPDPDM9cRDP6PVPzPS%a9R>DJ1QT8'IR;=Bdv[[[[[[[[^@M]C^;I^1?P6Pn%6k#5#<,M7%1B#5#1#1#5#5#1#3'LP0P>DJ/Ir=Bdo[[[[[[[[[[[[[[[[[[[]4^AG^9N]8^7N^>N]B]?]<]:]0]2g00iFRd%;5RB%;4R7g00id%;3?0451=231=2450NRk[1=341=3550N%;2?034[R~%;1?023\kA`345P5n2001000000120000000W6W5W=P~^67^5B^=dP5PF%<@#1#:#5#<#5#1#1#3Rd,2FRBAOFdUR71_Nd1=FB1=F750NdO4b3A0GB7PGPBP9P:P<g00j?RBPQDRP9P:P<PBPRPQPSPTGAPGPTPLPAPUPWE7PGP]PLP^PUPVE7PGP`PLPaPU%1@#:#5#:#1#5#1#1#1#3,2FE7PGP[PLPKPUPbE7g00k6RbPePfPgCD=0chP9P:P<PBPuP2P3PwGAP9P:P<PBP8PVPCP{P|M9PPbPVP}PgCD=0cHABb;v\D[[\j\p\y\x[^@M^Ct^;I^1?P6PnPzP0P>DJ/Ir=Bbo[\i\s\q\m\l\Y[[[\_[\\\Z\E\X[[[^4P^AG^9N^8O^7N^>N^BN^?M^<J^:I^0?^2=XEGP4P7P5Eeb3bDo"). Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
