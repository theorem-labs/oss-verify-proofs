(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptStderr O23LeptBase O23LeptErr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.OL Require LeptCmap.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocOL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23RelocMusl O23LeptEnv O23LeptG.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptCmap () := "K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec6v_sllwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC79OSSVerify5KrLib6Common9Leptonica2OL8LeptCmap6sllw_1C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3O238O23LeptG9o23_pinsGC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica2OL8LeptCmap@pixcmapDestroy_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs4lctx00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib6Common9Leptonica2OL8LeptBase3LLGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs3Cok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs1W00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common9Leptonica8LeptDefs5c_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common9Leptonica;LeptStructs6CMAPatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica;LeptStructs5c_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4c_A0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9Leptonica8LeptDefs7cs_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs5POSTMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib6Common9Leptonica8LeptRoom6roomtrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL;o23_code_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL<o23_sites_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL8o23_leptC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib6Common9Leptonica;LeptStructs5cmapv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4LSTKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;ALLOC_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib3O23;O23LeptBase4LL16C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCmap ()) [] "h03RLTh11dp;1p;3p;2g0000j12Tg000Nj31Tg000hj10Tg001Mj23Tg001gj18Tg002Ej17Tg002hj24Tg003Nj25Tg004Ij26Tg004fg005nR0f0R1g006LR2#2R3510%02R2#2R49101%02R2#29101%02R2#29101'3'3'3%02#0#0#8R2#71423f1R3,42'51643,4231[]1P1b0o"). Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
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
  realizes SEGS (mkCfg (mkst regs (0x711dc : word) m al_rom) md) S.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCmap ()) ["Cmap"] "h01Ah12A'h21Ch31Hh41Sh52b1h62b2h72cmh82cvh91kh:1mh;2m'h<2mdh=1nh>2pph?4regsh@5regs'hA3rethB1shC3vm'hD3RLThE1bhF1qp;3p;:p;2p;1p;5p;8p;4p;9p;6g0071j3jTg007ll:iTg009>j3\Tg00:Gj3YTg00;Lj3hTg00<Uj2bTg000hj14Tg001gj1HTg002Ej1;Tg00=Vj1FTg00>8j17Tg00>]j2VTg00?Ij2UTg00@Nj5RTg00ARj8ATg0000j13Tg00BTj2CTg002hj22Tg00C7j2^Tg000Nj30Tg00CWj4NTg00D[j2[Tg00E8j2@Tg00EUj2GTg00F1j1ZTg00Fij2MTg00Gij2LTg00Hcj1XTg00ICj1WTg00JBj1:Tg00Jaj4DTg00KYj2KTg00LVj2?Tg00M8j3TTg00N@j49Tg00OCj1>Tg00PJj4STg00QMj1gTg00Qoj1ETg00RHj2QTg00SBj2fTg00THl9PTg00ULj1dTg00VCl9cTg00WHj1aTg00XEj5JTg00Y>j2ITg00Z3j3BTg00[2j2=Tg00[\j3`Tg00\@j3OTg00\cj2_Tg00]=j6eTg00]Yj2]Tf5R0f4R1f3R2f2R3f1R43O']f0R530p=8%75#4p=<%45#7p=5%75#7p=6%45#4p=1p,2fxR6g00^RR7g00_Mg00`Lg00aLR8p,2ALR9p,2CLR:p,3ASRR;p,4PINSp,3P169j9:M:iA\9:;R<9Y9:R=Ah9:<R>,b9R?g006LR@#4RA#4RB#4RC#4RD#4RE#4#HRF#;RG%HC#;RH#F[RIg00bHRJ%7ARK#HRL/VGRMg005nRNg00c>ROg00dGRPP9P:P<1U78R8f;RQDRP9P:P<P8f<RRPQf:RSf9RTGAPGPTPL%3ARAg00e@RU1CLAdf8RV,2FRWE8%3D,^Tg00e\RD50NRXP9P:P<f?RYCNg00f:'[%3E'@g00g='@/GSRE1GQSRZ%3CRC,@QP9P:P<fAR[CN'GR\PGf>R]PL%3@R^PU1CL^dPVE8%ZTR_PGf@R`PL%3BRaPU1CLad%7BRB#7#<#<#5#5,M7%7K#6#5#6#<#6#<#1#3'LE8PGP[PL%4K#3RKPU1CLKd12FYRbE8%XHRH#FRc%W7RdfDRe12F`Rfg00h?#:#:#:#:#:#:#:#:RgCD1KgY,?HRh30fERi?T`YRY%FNRjP9P>fG12F[C9%<@Rk#1#3,?N30RlP9P>fH%>[,2FC91?N`50jRmP9P>P9P:P<fJRnCSfCRo,2FC9%gNRp50jRqP9P>P9P:P<fKRrCS%>o,2FC9=0jpRs%>e90Ni#ERig00h^RtP9P:P<P8fQRuP2P3fNRv,Q4RwGA1fv4RxP9P>P0fLR0,2FC9=0jpRyP9P>f6%>0,2FC9=0jpRpfORz,2F90G5#E%>z,2F90G4#EP9P>PSP3C9P9P>fWR>P3C950j[[^FGRjP9P:P<P8fVR8PVfP/@CRCfTR{f7R|M9PPdPV12FuR}PgCD1KgD,?HRH50cP9P:P;P>fU#dPSPVPDPDM9cRDP6PVPzPS%a9R>DJ1QT8'IR;=Bdv[[[[[[[[^@M]C^;I^1?P6Pn%7k#5#6,M7%1B#5#1#1#5#5#1#3'LP0P>DJ/Ir=Bdo[[[[[[[[[[[[[[[[[[[]4^AG^9N]8^7N^>N]B]?]<]:]0]2g00iURd%;5RB%;4R7g00j3%;3?0451=231=2450NRk[1=341=3550N%;2?034[R~%;1?023\kA`345P5n2001000000120000000W6W5W=P~^67^5B^=dP5PF%6@#1#5#1#5#6#5#6#1#3Rd,2FRBAOFdUR71_Nd1=FB1=F750NdO4b3A0GB7PGPBP9P:P<g00jNRBPQDRP9P:P<PBPRPQPSPTGAPGPTPLPAPUPWE8PGP]PLP^PUPVE8PGP`PLPaPU%1@#<#1#6#6#5#1#<#1#1#3,2FE8PGP[PLPKPUPbE8g00kGRbPePfPgCD=0chP9P:P<PBPuP2P3PwGAP9P:P<PBP8PVPCP{P|M9PPbPVP}PgCD=0cHABb;v\D[[\j\p\y\x[^@M^Ct^;I^1?P6PnPzP0P>DJ/Ir=Bbo[\i\s\q\m\l\Y[[[\_[\\\Z\E\X[[[^4P^AG^9N^8O^7N^>N^BN^?M^<J^:I^0?^2=XEGP4P7P5Eeb3bDo"). Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
