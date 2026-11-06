(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Eb0DefsK Eb0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eb0ArtCellsK () := "C46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5SINV0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5argH0C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK2knC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ArtCellsK8chk_lit1C13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6ArtMem4cellC13~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK7chk_subC13~~~C47Corelib4Init9Datatypes3orbK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr01C13~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02C56Stdlib5Arith8PeanoNat3Nat3lebC46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK6hc_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK6hc_imgC13~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat6leb_leC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib7u64_litC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6edenotC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2uEC13~~~K46Stdlib9micromega6VarMap1t03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK<hc_zero_cellC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK5cs_ok00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK7chk_imgC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK8chk_zeroC13~~~C47Corelib4Init9Datatypes4andbC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK6ASEGS0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK5ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5LIMITC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K3env00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3acs00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK4APH0C13~~~K47Corelib4Init9Datatypes3nat01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_in_hullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_hull_okC13~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ArtCellsK<art_lits_chkC13~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ArtCellsK8art_lit1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ArtCellsK8ART_LITWC13~~~C47Corelib4Init3Nat3addC47Corelib5Lists7ListDef6repeatK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffCellsK9wleb_zeroC13~~~C47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:repeat_appC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec7rdn_appC13~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula08C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib7Numbers7BinNums1N00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (1321624 + 40, 4%nat, 0xffffffff); (1321624 + 56, 1%nat, 0); (0x10430, 8%nat, 0xafffff00000fffff); (0x13d8a8, 8%nat, 0x1d5ba0); (0x1d5ba0, 8%nat, 4096);
    (0x1d7c28 + 260, 1%nat, 0); (0x1d7c28 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0x13d8c8, 8%nat, 0x1460f8); (0x1460f8, 8%nat, 0x7fff8000); (0x13d8d0, 8%nat, 0x146de8); (0x146de8, 8%nat, 0); (0x13d8d8, 8%nat, 0x146df0); (0x146df0, 8%nat, 0);
    (0x13d8e0, 8%nat, 0x146de0); (0x146de0, 8%nat, 2 ^ 47 - 1); (0x13d8c0, 8%nat, 0x1438f8); (0x1438f8 + 78, 1%nat, 1); (0x13d8e8, 8%nat, 0x13f8d8); (0x13f8d8, 8%nat, 0x130034);
    (0x13d8b8, 8%nat, 0x1d7c28); (0x1d7c28 + 120, 8%nat, 18446744073709551615); (0x14595c, 1%nat, 1);
    (* [comment removed for export] *)
    (0x145960, 1%nat, 1); (0x145964, 4%nat, 0); (0x67a180 - 88, 8%nat, 0x69b638);
    (* [comment removed for export] *)
    (0x10450, 8%nat, 0x218a392cd3d5dbf); (0x104cc, 1%nat, 3); (0x10378, 8%nat, 0xcc6e96b9cc6e96b9); (0x105d0, 1%nat, 4); (0x105f9, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x10428, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0x146dd8, 1%nat, 1); (0x1c8362, 1%nat, 0); (1321624 + 3616, 8%nat, 2 ^ 40); (1321624 + 3624, 2%nat, 16); (1321624 + 3626, 2%nat, 2048);
    (0x1d7bc0, 8%nat, 0); (0x1d7bc8, 8%nat, 0); (0x1438f8 + 44, 4%nat, 4096); (0x1438f8 + 48, 4%nat, 0); (0x1438f8 + 52, 4%nat, 190); (0x1438f8 + 85, 1%nat, 1);
    (0x13e528, 8%nat, 0x10); (0x146dfc, 4%nat, 30); (0x1d7c28 + 34, 1%nat, 1); (0x142d70 + 80, 8%nat, 2 ^ 20); (0x142d70 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0x13f880, 8%nat, 0x130754); (0x13f710, 8%nat, 0x12fb34);
    (* [comment removed for export] *)
    (0x13f760, 8%nat, 0x12d748); (0x13f718, 8%nat, 0x122794);
    (* [comment removed for export] *)
    (0x67a180 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (1321624 + 64, 8%nat, 4096); (1321624 + 64 + 56, 8%nat, 0); (1321624 + 64 + 48, 8%nat, 0); (1321624 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0x142d70 + 160, 8%nat, 0); (0x142d70 + 168, 8%nat, 0); (0x142d70 + 176, 8%nat, 0); (0x142d70 + 184, 8%nat, 0); (0x142d70 + 152, 1%nat, 0); (0x142d70 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x1d5b88, 1%nat, 0); (0x1d5b89, 1%nat, 0);
    (* [comment removed for export] *)
    (0x627fd8, 4%nat, 1);
    (* [comment removed for export] *)
    (1321624 + 64 + 617, 3%nat, 0); (0x142d70 + 154, 2%nat, 0); (0x1d5b88, 4%nat, 0);
    (0x13d8b0, 8%nat, 0x13f910); (0x13f910, 8%nat, 0x1a76e); (0x146dd9, 1%nat, 1); (0x1d7d23, 1%nat, 1); (0x1d7cb1, 1%nat, 1); (0x1d7c28 + 84, 1%nat, 1);
    (0x1d5b98, 4%nat, 0); (0x146100, 4%nat, 1); (0x13f8d0, 8%nat, 0x12fc30);
    (* [comment removed for export] *)
    (0x142d70 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0x13d908, 8%nat, 1);
    (0x13f868, 8%nat, 0x116acc); (0x13e430, 8%nat, 0x146dd9); (0x13f7c8, 8%nat, 0x130c14); (0x13d918, 8%nat, 0x1d5b98); (0x13e6d0, 8%nat, 8);
    (0x1d7c7c, 1%nat, 1); (0x13f720, 8%nat, 0x136634); (0x13f728, 8%nat, 0x127030); (0x13f750, 8%nat, 0x12d72c); (0x13f758, 8%nat, 0x127448);
    (0x13f6d8, 8%nat, 0x13f6d8); (0x142a40, 8%nat, 1); (0x142a90, 1%nat, 0); (0x143910, 4%nat, 1); (0x1439b0, 8%nat, 0); (0x1d7fa0, 1%nat, 0);
    (0x67a178, 8%nat, 0x67a1a0); (0x67a1a8, 8%nat, 0x67a980);
    (* [comment removed for export] *)
    (0x13f6e0, 8%nat, 0x130518); (0x13f7a8, 8%nat, 0x11e7dc); (0x13f7b0, 8%nat, 0x130480);
    (* [comment removed for export] *)
    (0x104d0, 1%nat, 4);
    (* [comment removed for export] *)
    (0x143914, 1%nat, 0);
    (* [comment removed for export] *)
    (0x13f878, 8%nat, 0x11e9c4);
    (* [comment removed for export] *)
    (0x143958, 1%nat, 1);
    (* [comment removed for export] *)
    (0x13f700, 8%nat, 0x12fc00); (0x1d7d26, 1%nat, 1); (0x1d7d27, 1%nat, 1);
    (* [comment removed for export] *)
    (0x10398, 8%nat, 0xf5f5f5f5f5f5f5f5) ].

Definition chk_lit1 (k : list kentry) (c : Z * nat * Z) : bool :=
  let '(a, w, v) := c in
  (chk_sub k a w v || chk_img ASEGS0 ASAN0 k a w v || (chk_zero k (ELit 0) a (Z.of_nat w) && Z.eqb v 0 && Nat.leb w 8 && Z.leb 0 a))%bool.
Definition art_lits_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) ART_LITW.

Section Lits.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Lemma art_lit1 : forall E cs R FULL model c, CSOK E cs R FULL model -> chk_lit1 (kn cs) c = true ->
    cell ASEGS0 FULL (fst (fst c)) (snd (fst c)) (snd c).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0ArtCellsK ()) ["Lits"] "p'0h01Hh11mh21ni001nh32Hah44__x1h52H0h63Hw0h77__arithh84__ffh98__varmaph:5__with;4cstrh<1zi011zh=2Hvh>2Hwh?4__x2h@1vhA1EhB4FULLhC2HChD1RhE6__sat1hF6__sat2hG1ahH1chI2cshJ5modelhK1pi021phL1wp&0p;1p;2p;8p;7p;3p;5p;4p;Cp;Bp;Ep;;p;6p;<p10000p4p710g000RR0p4p710p8g0010j1<Tg001Uk10;Tg002:j1PTg002Xj1ZTg003;k20:Tg003gj1fTg004IR1j2dTg004ij8tTg0063j7nTg007=j12Tg008Hj2LTg009Xj3JTg00:5j3FTg00:Rj5HTg00;Xj4?Tg00<8j4=Tg00=Hj2QTg00=ej1sTg00?7R2j17Tg00?Wj19Tg00@6j24Tg00@Vj3]Tg00A2R3j2\Tg00ALj1[Tg00Alj25Tg00BRj4BTg00CYj2ETg00Daj2DTg00ECj38Tg00E]lChTg00FllBgTg00H;j3YTg00H^R4j2ITg00I9j2WTg00IVk209Tg00J6R5j2CTg00JPk208Tg00K3j2MTg00KPR6j21Tg00Klk205Tg00LLj26Tg00Lij1UTg00MGj2STg00Mak403Tg00NHk102Tg00Nmk101Tg00OMj2eTg00Okj1|Tg00PIj1{Tg00Q4j2cTg00QWj2bTg00R:j3NTg00R]j2yTg00S?j2xTg00Skj3rTg00TJj4qTg00U<j2`Tg00Ufj2pTg00VNj2^Tg00Vjj2uTg00WGj3oTg00Wkj1vTg00XIj3wTg00Xlj4aTg00YWj7mTg00Z;j2zTg00[Fj2lTg00\Xj2}Tg00]ij4kTg00^GlE~Tg00_\m;00Tg00a2j6jTg00bBj4_Tg00cSj2XTg00d1l<iTg00dVk706TP0k607Tg00e:R0g00fDR7g00gMR8f7R9f6R:f5R;f4R<f3R=f2R>f1R?f0R@N;00p=Rg00hWRAg00i7RB78@p=0g00iWRCg00j5RD;J@p=KAFCD@p=VP0P7P=P>P?P@Ejp=;g00jTRE,W@p=3P<P=P>P?C_/X@p=:1ME@p=>1X>?/X@p=@P=P>P?%7@C_p=APDPCP5P2P6g00k2P;P<P=P>P?P@M<ip>04PCP?g00kTP@Cap=OP?g00l;R6g00lZR2P2g00m:R5P@g00mZK06p=GPCPEP=P>P?P@J07p=Tg00n:g00oKg010YRF#<RG$0;#P%<G#<RH#<#<#<RI#PRJ#ZRK+0:%PH#ZRL#f\Kg011>1dCDRK/dCP1PKPCg0124RMp,2spRNp,5rdrawROp,4brk0p,4argvRPp,4envpRQp,3uidRRp,2hwRSGtRTPMPNPOPPPQPRPSFnRSp,2fsRRP:P;P<P=P>GR%2:/L?#0P0P;AJKC>RQ#K%VQAFKC>DH[[P@P1PCPDPTPSPRf:R1f9RQf8RPP9P:GR%21PKPCP>P?C?'L#0P0PQPKPCP=P>C?RO9JKCRN#K%VNAFKCODH[[^<CP@PTPSPRf=ROf<RNf;RMP1PQGR%2OPKPCPCPDP=P>C?P?C?'L#0f>RU#2RVP<P=P>C=PVP<P=P>C;'QRWPV%sERVP<%7=%3>D:g013<#9#9#9#9#9#9#9#9RX,4=%><3@RY;]@%0W%0Y'\P3f?RY#2RWP;P<P=C=PWP;P<P=C;'Q#0PWPVP;%7<%3=D:14<X%>;3@#0%[LRL#fRWP0PU15J:P;CB15J<,E;,DL38P@f@RZ#2R[P:P;P<C=P[P:P;P<C;'Q#0fAR\#2R]P9P:P;C=R^P]P9P:P;C;R_;]@%0^%0_'\P3fBR3#2R_PPP9P:C=#0P_PPP9P:C;#0P0P\15JQPPCB15J9,EP,DL58WR^P@fCR`#2RaPQPPP9C=#0P0P7P8PTPSPRg013[g0152Rbp,2AHRcfERdfDReP`P3P\P1PQPPP9P@MChW0P@O1PaPQPPP9C;#0P0P7P8PTPSPRPbPcPdPeP`P3P\P1PQPPP9P@MBgW0P@O1n200100000021000010000b0W0P@O1P[PVP:%7;%3<D:14;X%>:3@#0P]PVP9P:CA%3;14:X3@R;%>9R];Y@%0;%0]'IP4P_PVPPP9CA%3:149X3@#0%>P#0P^P@%2ePVP1PQCA%3P14QX3@#0%>M#0fFRQ#2PVPN%7M%31D:R114MXR^;Y?%01%0^'IP4fG#2PVPO%7N%3MD:#014NX#0P0PQ15JUPOCB15JN,EO,DL58WP@fIRM#2PVPY%7U%3OD:#014YX#0fKRO#2PVP\PZCARU%3YR^;Y?%0U%0^'IP4fLR^#2PVP3P\CA#0%3Z#0P0PO15J`P3CB15J\,E3,DL58WP@fNR3#2PVPeP`CA#0%3`#0P41W?@#0A8C>?[R`A8C?@1W>?#0Re[A8C=>\e209?@P?n2001000000120000000X1CX2CP`^1C^2CP@PdPEP?O3A8CdEP0fQ15JMfHRdCB15J@,Ed,DL58WX@CP414?@#01C>?[RW1C?@14>?#0RL[1C=>\L208?@P?n2001000000120000000X1DX2DPW^1D^2DP@PdPXPPO31CdXP41M?@#011>?[R411?@1M>?#0Rd[11=>\d205?@P?n2001000000120000000X1CX2CP4^1C^2CP@PEPOPYO311EOP0P7P8PTPSPRfWRRfVfUfTfSPVP^%7ORSPMP9P^POP>fMR9,6@RM/19X<C1COX%UHRH,1SRTPOPS1SCSPXPH1SCHJ04P>H03RHPT&02^RX%7^RO,1ER8g016IR7$01RY%[7R71eC?%|CR4%{CRd1cCERP1bCFRF5NCRW/OF'G1yd5RLP@P>1SAB1x@>#0dArCE?CqRBb8b9b:X4C16E@RA/1@^4CP@fOR`O1b7b;b615JE,`JRePHPTPXP8%UGR\%UIRI'p1^E\11EI1u\IRZ,^ERU[[11E\R1g0175R:Ao\I?UW311EZ\:^31PYP7%vCR1P4PdP6P2P2P51OPP,GdPCPPg017Q1cC\=wCJCa,GdFmPLPBb8b9b:11EE/IUP@b7bEbFb;b6,zERECT1lRV,`J/6^RJ/1^e1}RV/6^RR/1^e169O16MO'1X<CPHPTPXP8PYP7PC1eC>P?P1CkP41bCGRG9NCFANCWG'O,GdPLPBb8b9b:X4CX?C16@?16A?'1^4C^?CP@%73P`O2b7b;b6PePECT16^SR^16JS'1e16RS,1^eME~b3b5b>b5PQP@CTb=b5W=W0P?P@O2n2001000000121000000b0W>W0P?P@O2n2001000000121000000b0W3W0P?P@O2n2001000000121000000b0W0P@O1n200100000021000011000b0P0PNP<P=P>DHeP0PNPKPCPCPDP<P=C?P>C?R>9JKCR=#K%V=AFKC>DHeW0WCX@CXLDXGCP?P@O2n2001102000121101100XKKP?P@O2n2001102000121102101WHWJWBWDWIWAo"). Qed.

  Lemma art_lit : forall E cs R FULL model, CSOK E cs R FULL model -> art_lits_chk cs = true ->
    forall a w v, In (a, w, v) ART_LITW -> cell ASEGS0 FULL a w v.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0ArtCellsK ()) ["Lits"] "h01xh11Eh24FULLh31Hh42HCh53Hinh61Rh71ah82csh95modelh:1vh;1wp;1p;2p;8p;7p;;p;4p;3p;6g0010j10Tg001Uj1ETg002:j14Tg002Xj15Tg003;j2DTg003gj1CTg004ij8>Tg0063j7=Tg00_\l;<Tg0188j1;Tg004Ij28Tg00;Xj42Tg019Lj3:Tg007=j13Tg008Hj19j26Tg019cj37Tg01:?j3BTg01:bj6?Tg01;=j8@Tg00ECj3ATg00hWf0R0g00i73Ap=1g00n:g00oKg010Y#0R1#E#4%01#0R1#0#0#0#4#5R2'D%41#5#C\2g011>g00e:g00fDg00gMg0124R2p,2spR1p,5rdrawR3p,4brk0p,4argvR4p,4envpR5p,3uidR6p,2hwR7G>P2P1P3P4P5P6P7F=p,2fsf4R7f3R6f2R5f1R4P0M;<%;7#1g00iWR3g00j5R11831R2/83R8P2P3P3P1P5P4C2P0C2g01<MR93:f:R:f9R;f8f7f6P2P3P3P1P6P5C2P4C2R5f5%3;#9R;=789#1A:809R6f<#3/64#1[^08[f;#3/64#1\6^08%3:#9=789#1[AB8;9P7P5P0E?G@W5X:3W;W7W3W4W9W2W6W8W1o"). Qed.
End Lits.

(* [comment removed for export] *)
Lemma cell0_cat : forall (M : word -> option byte) a (w1 w2 : nat), 0 <= a -> a + Z.of_nat w1 < 2 ^ 64 -> (w1 + w2 <= 8)%nat ->
  cell ASEGS0 M a w1 0 -> cell ASEGS0 M (a + Z.of_nat w1) w2 0 -> cell ASEGS0 M a (w1 + w2) 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0ArtCellsK ()) [] "h04__x1h14__x2h21zh33Hw0h47__arithh54__ffh66__sat3h76__sat4h88__varmaph95__with:4cstrh;5cstr0h<1lh=2Hah>1Hh?2H1h@2H2hA2b1hB2b2hC1nhD3H2'hE2HnhF2HwhG1MhH1ahI1bhJ1ohK2w1hL2w2p%0p&0p;1p;2p;3p;4p;6p;7p;9p;5p;<p;Bp;8g0010j1CTg002:j1dTg002Xj1@Tg003gj1_Tg00?7R0j13Tg00LLR1j20Tg00Lij1RTg00Vjj2nTg00VNj2GTg01=]j2HTg00?Wj1;Tg00J6R2j2DTg00ALj1cTg00Alj22Tg01>4j3<Tg00Daj2ATg00ECj31Tg00CYj2STg00KPR3j25Tg00Maj4WTg00NHj1ZTg00Ufj2kTg00WGj3jTg01>Sj2JTg01?<j3FTg01?ej2NTg00Nmj1iTg01@Qj3OTg00Wkj1hTg00OMj2gTg00]ij4^Tg00Okj1fTg00PIj1eTg00Q4j2LTg001Uk100Tg00QWj2\Tg01A1j1~Tg00R:j3YTg00R]j2}Tg00MGj2XTg00S?j2|Tg00Skj3{Tg00TJj4zTg01ASj4UTg01B>j2[Tg01CPj6MTg00U<j24Tg01Clj3uTg01DPj1bTg01EKj3TTg01F0j27Tg01FVj2>Tg00XIj3tTg00Xlj4PTg00YWj7sTg00H^R4j2rTg01G6j3aTg01GYj2QTg01HHj3qTg01I6j3`Tg01ISj4pTg000Rj6KTg01J2l9oTg00:Rj5vTg00BRj4wTg00d1l<mTg01K<lBxTg00dVj7yTg01Kbj8lTg00jTR5f0R6'5p=9g00e:R7f2R8f1R9P6P5Dvp=]P7P8P9P6Cwp==g00iWR:/X6p=?g00j5R;P:P2P0P3g00k2f5R3f4R2f3R<P8P9P6M<mp=IP;P;P;P:P:P:g01LFP0P0P0P1g01LfP3P2P<P8P9P6MBxp=VP:P9g00kTP6CPp=BP9g00l;R1g00lZR0P0g00m:R=P6g00mZFyp=:P<P1P0P0P=P8P9P6Glp=6A1:96p=8P:P2P<P8P9P6EKp=Eg010YR>#CR?#C#CR@#C#C#CRA#dRB#@RC%d@RD#@RE#_[%98RF%38,0<%R?RG%RARA'nRH'G1H<8g013<RI#;RJ#;RK#;RL#;#;#;#;#;RM'Df6RN?]32f7RO%33RP,0N;]2%cERQ12D5RD1HN3RR5<E%_QRSf9RTf8RU,2BRV1HONRW3=1AQ6RX31X<QPQ12B5RY,S3%3ORZ,0U,2B==TN=1SXX<QP6A<ED3R[1D3M%R@R@,5PP3PP%?PR\PMP@%?@R]EI1DRMS00%3NR^/0PR_/5@R`PRP_PNP^%?^R_P3PPP\EVPMP@P]EIS01P8CWS02P`%ZOR\%9ZRPP\PP1kGARa1G5G%9A1G5H[[Rb%9GRcg0175RdAjGA9UW=RA%9H\d^=cRcg016IRd1J:KRK1J:J1J:IRI5F:RJ5F:g01MIRe'N%idRf3ORg%cdRhP:%h:S03P91g:8S04C^Ri%f:Rj%e:Rk1L:5Rl&00>,\:Rm'B,:kRn%~0RoPk1\:>R>9Y:m1L:@Rp'B,:kPo1B>p,:kRqC6C61}k=RrP6P8g00hWRsg00i7Rt'X1|68=1stdA{:59CzR5b5b8b9X0:X1:%99Rt1089/5@158@Rs[[^0:^1:P6f<Ru#3Rvf;Rw#3S05P2P3O4b4b6b7b;b:b3CU,[3EM10O^,2B==U31AQ[51SPQ1SOYf:R[12BTRx;=U=1SXX<QP8A<EDORy1DOM15Z@POPZ%?ZRzPMP@P]EI1DWM10Z^R{/5@R|PWP{POPZPzPNP^P_EVPMP@P]EIP<CWP|%ZUR|%3UR_#9R^P|P^PaPbPAPcPgPhPiPjPkPnPoPkAY:>m/Bp,:kRmPoPqC6C6PrP5b5b8b9X0:X1:1098Rq/5@S06Ps[\t^0:^1:P6Pvf=S07#3P<P3O4b4b6b7b;b:b3CU,[OEMA=TVO1AQyRy51Sg01N5RV%@6Rs%@9RgP4%@8?19614<814<9'8R4[14891486'8%@<?189[R^%@2?1<8\4Au896P6n2001000000120000000WBWAWCP^^Bg^As^CVP6PB%3TRV,0[Rs,2BRg12B[R^%bT5TBR414B^S0812BVR|,4BS09'0,7B%3[RN,0wRz,2B,4B/86X2:17BsRZ12Bw,4B12BN,4BR{'0,7B,86X2:17B[RW17BzR}106{,7B'8X2:17BVR{17Bw/06,7B,8}X2:P[1>zHRz1>NH,06/>H'8X2:PV10w6/>H,8zX2:1>sH#?1>VH1HTURz/DM10V_R}/5@R~PzP}PTPV%?VPUP_%?_EVPMP@P]EIP3CWR]P~%Z[RM%9NRNPMPNPaPbPAPc1J:LRL=F:J/Ne=OdfPhPiPjPkPnPoPk1Bl>,:kRnPoPkPmPoPkP1P0P0P=PnP:P>g017QR=1L:G=t:BRGCP,:kFsR0C6C6C6PrP5b5b8b9X0:X1:108</5@%9<1G<H'rR1[\t\t^0:^1:P6f>#3f?#3RmP<P2P3O5b4b6b7b;b:b39aVHDE1>[HP]P~PMPNPMPNPaPbPAPcAF:KI9F:L/Ne=OdfPhP:Q04P9Q03C^RdPjPk1\:?R?,Bl,:kPoPkP:AY:>?R?P=PGCP,:kPoPkPnPoP0C6C6C6PrP5b5b8b9X0:X1:1GqHP1\F[\t^0:^1:P6Pmf@P2PuQ07O5b4b6b7b;b:b39a[HDE10W{,7B,8ZeQ091QBVDEQ081QB[DE14BgRV1QBsDEATB^|,4BAqB^|DE14B4,8VeO4b>10T_,2B%bU9TBxRx51CPCPgA=u6TA<EDTRu,AQ51SXICP8P4P6EMb>A=[xO=1SyPSA<EDURy9`EuRx,AQR41H[T9<ED,AQ91S6XJSPQPxA<ED[=`Eu,AQ=1SXX<Q1XS4A<EDzPEPDPTPUCpEKA=w^zP7PwPTPUP^PuPyP9P6M9oEKbDb?b@1SRYQ00P`Q01Q02P`P\PPP\PPPaPbPAPcPfPhPdPjPk1B?p,:kRkPoPkC6PrP5b5b8b9X0:X1:1069/5@Q06[^0:^1:P6Q05PvP3O3b4b6b7b;b:b3CU,[REKA]UOReW@W?WFWEW=XL;XK;XH:WGo"). Qed.
