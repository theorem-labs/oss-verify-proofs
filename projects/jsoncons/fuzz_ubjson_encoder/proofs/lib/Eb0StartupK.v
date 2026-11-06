(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
  AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK Eb0PlanImagesK AsanInitK
  AsanNodesIfaceK AsanNodesMmLibK AsanNodesMmAK AsanNodesMmBK AsanNodesExtraDefsK AsanNodesExtraK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eb0StartupK () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK5cs_ok00C13~~~I47Corelib4Init9Datatypes4prod00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK3XE0C13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymRun3K9env_agreeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3nxtC13~~~I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK2pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK6cfg_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2WpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~C47Corelib4Init5Logic9False_indC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK9emit_stmtC13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K3env00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes3nat00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3acs00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6spiece00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK6ASEGS0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK5ASAN0C13~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3NX0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK3XB0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_alt2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK9ext2_stmtC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK6alwaysC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK3XN0C13~~~K47Corelib4Init9Datatypes3nat02C56Stdlib5Arith8PeanoNat3Nat3eqbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libCAsanNodesExtraDefsK:xn_smearvaC13~~~K47Corelib4Init9Datatypes6option02C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?AsanNodesExtraKAxn_absbytes_soundC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK:node1_stmtC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK8ext_stmtC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libCAsanNodesExtraDefsK>xn_addrisinmemC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libCAsanNodesExtraDefsK;xn_absbytesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?AsanNodesExtraKDxn_addrisinmem_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?AsanNodesExtraK@xn_smearva_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK9AIM_ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK?Asan0_wx_nowrapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_in_hullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_hull_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK:e_sp0_initC13~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK=X_MAXVA_ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_segs_wrC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK5HOLESC13~~~K47Corelib4Init5Logic2eq01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4cres01C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5SINV0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5argH0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanNodesMmBK?node_exit_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?AsanPlanSound2K?node_join_soundC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK9XN0_soundC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK9XE0_soundC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK9XB0_soundC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5checkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanNodesMmBK>node_sys_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanNodesMmBK?node_brk2_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanNodesMmAKDnode_mmap2_sound_OBLC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanNodesMmAKEnode_mmapin_sound_OBLC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanNodesMmAKHnode_mprotect2_sound_OBLC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK;check_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5LIMITC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_res_lenC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK>asan0_res_hullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK?asan0_shadow_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK@asan0_hull_tiledC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK=asan0_hull_ltC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK;HOLES_agreeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK9HOLES_nilC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK:HOLES_flatC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_nilC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4plan00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5shape00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4cres00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7loopctx00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK4APH0C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK9hole_onlyC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2sdC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK;stage_soundC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srz_conseqC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK=hole_only_denC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6hs_extC13~~~C47Corelib4Init5Logic7f_equalC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK:holes_stmtC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK9img_facts00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK2R0C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7a_entryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5FULL0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK6model0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK2E0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK:init_cs_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK;init_acs_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK3inpC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC56Stdlib6ZArith6BinInt1Z4of_NC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK;init_cfg_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK?asan0_img_factsC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK:asan0_initC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M7init_pcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK:stage_holeC13~~~".
Import ListNotations.
Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section As0.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

(* [comment removed for export] *)
Hypothesis AIMW0 : aim_spec ASEGS0 AIM_ASAN0.
(* [comment removed for export] *)
Hypothesis SMEARW0 : forall (mem rom : word -> option byte) regs (x : word),
    getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
    exists regs',
      msteps ASEGS0 (mkst regs (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 0) mem rom) (mkst regs' (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 180) mem rom)
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
      /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
      /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
      /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
      /\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma XE0_sound : forall LIMIT SINV argH FS0, emit_stmt ASEGS0 scfg ASAN0 NX0 LIMIT XE0 SINV argH FS0.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"] "p'0h01Eh12E'h23FS0h34FULLh45FULL'h51Hh62H0h75LIMITh81Rh92R'h:4SINVh;1Th<2_Hh=3_H0h>4argHh?4argsh@2cshA3cs'hB1ehC2fdhD2idhE5modelhF6model'hG2pshH1xi001op;1p;2p;;p;3p;4p;6p;5p;9p10000p4p70p1000`p4p710R0p8g001>R1p4p70P0p8g001lR2p4p7210P0p8p1002Xp4p70P0p8g003Nj10Tg0043j12Tg004Qj17Tg0054R0j14Tg005Vj13Tg0066j1GTP2j2CTg006[l;=Tg0081j2<Tg008QR2j36Tg009Xj41Tg00:8j29Tg00:Zj3:Tg00;4j1ITg00;Tj6HTg00<0j3?Tg00=?j1FTg00>Kj2ETg00>fj15Tg00?Yj1;Tg00@dj5>Tg00B9j58Tg00CEj3BTg00DVj2ATg00E`j2DTg00F?l9@Tg00GWR3g00H5R4g00IF#0R5#0#0R6#0#0#0#2#7R7%26#7#4[R6p-0R8[[g00Ik\7\4g00JKg00Jj#3g00L<R9g00MJ#3R:%G5#2/C7R7g00N[R5g00OQR;#3P8]Hg00PGR<g00QQR=f>R>f=R?f<R@f;RAf4RBf8RCf3RDf2REf1RFM;=1<3:RG/<9RH#4RIf:RJf9RK56APGP9P3P:PCf7RLC1f6RMC1,9H3:PE%I;O1PIA6?@AP0PHP8f0R8g00RZR0g00S7n10110000021000000XBIg00SSPGP9P3P:PJPKC1PCC1,9HPFEHP0g00SoR0??@Df@RH#F??@D'EP<P=fGfFfEfDPBP>PDPEPFM;=%5E%5A5:1g00U;R>P<p,4scfgRJP<f5R:%;HPBPDD>PAD8[[[^F5^46^97^14P>P<PJP<PC%;?PLPMD>ABK@A/A:D8[/D8b6W=W5W<W;WEX36W8X04XA9WGXC3W@W?WDP<PJP=P0PDP2PEPFP8M9@eX21W>W:W7o"). Qed.
Lemma XB0_sound : forall LIMIT SINV argH FS0, ext2_stmt ASEGS0 scfg ASAN0 NX0 LIMIT XB0 SINV argH FS0.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"] "p'0h02E'h15FULL'h22R'h36model'h41Eh53FS0h64FULLh71Hh82H0h95LIMITh:1Rh;4SINVh<2TAh=2TBh>2_Hh?4argHh@4argshA2cshB3csahC3csbhD1ehE2idhF5modeli001op;1p;2p;3p;4p;6p;5p;9p;;g003Nj10Tg0043j15Tg004Qj1=Tg0054R0j16Tg005Vj1HTg0066j1FTg001lj2DTg0081j2@Tg00VGR1j39Tg009Xj47Tg00:8j28Tg00:Zj34Tg00;Tj6GTg00<0j31Tg00=?j1?Tg00>Kj2<Tg00>fj12Tg00?Yj1:Tg00@dj5;Tg00B9j5>Tg00WNj2CTg00E`j2BTg00XXl9ATg006[l;ETg00PGR2g00QQR3f0R4f1R5f2R6f3R7f4R8f5R9f6R:f7R;f8R<M;Ep=3g00GWg00H5R=g00IF#0R>#0#0R?#0#0#0#5#=R@%5?#=#6[R?p-0RA[[g00Ik\@\=g001>RBg00JKg00Jj#Hg00L<RC%F>#5/D@R@g00N[R>g00Z0RDf>f=REf<RFf;RGP9P<P8P7P6M931@CCRH#6RIf:RJf9RK59GPCPCP<P;C7,8H34PIA9FGJP0PHPAP4g00RZRAg00S7n10110000021000000XDIg00SSPCPCPKP<C7,8HP4EGPAg00SoRA?1F7f?RH#??1F7'<fFRIfER0fDRJfCP8PHP7P6P5M93%26RL%2G54Bg00U;RMP2p,4scfgRNP2P9fA#:P8P7D;PGD>RG[[[^3>^1?^2@^0=A1AE7f@#??1E7'<fGPIP0PJP8PHP7P6P5M93%2F94BLPG[[[^3>^1?^2@^0=PMP2PNP2PK%:EP<P;D;1C:9D>[[/B4b8W7W>X=DW<WFX6?W:X4=XCCXBCWAW@WEP2PNP3PAP7P1P6P5P4M9AeW5W?W;W9o"). Qed.

Section Hooks.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Theorem XN0_sound : ext_stmt ASEGS0 scfg ASAN0 NX0 LIMIT XN0 SINV argH FS0.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Hooks"] "p'0h02Hnh11bi001bh21Eh32E'h44FULLh55FULL'h61Hh72HCh82Hkh94Hpreh:1Rh;2R'h<1Th=4argsh>2csh?3cs'h@1ehA2idhB5modelhC6model'i011op;1p;2p;;p;3p;5p;Hp;6p;:p;9p;4p;Np;Jg005Vj1[Tg003Nj15Tg0066j1JTg0043j1:Tg004Qj1BTg001lj2RTg0054R0j1<Tg006[l;>Tg00[8R1j1HTg00:Zj31Tg00\MR2j3Fj2PTg00<0j3ATg00=?j1ZTg00>Kj2UTg00>fj1@Tg00?Yj1;Tg00@dj58Tg00]Tj10Tg00^3j22Tg00^Sj37Tg00_lj1GTg00`Nj2LTg00a4lHMTg00;Tj6NTg00E`j2DTg00bPl:QTg00cil9CTg00:8j2STg00B9j5TTg00e@j5YTg00f]j4XTg00h7lNWTg00iVlJVTg00L<R3f0R4'Sp=3g00U;g00PGR5f2R6f1R7P4DTp=9%04#0p=?%04#0#0#0p=O%04#0#0#0#0#0#0#0p=I%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=6P5g00SoR8g00k1R9P7P4DYp==P5P8P7P4CXp=4P5P4g00QQR:P8P7P6f3R;f4R<g00l>R=g00mWR>g00nnR?f5R@g010ERAf6RBf7RCf8RDP9f9R9f:REf;RFf<RGf=RHf>RIf?RJf@RKfARLfBRMfCRNfDfEMNWp=KP5P4P:P8P7P6P;P<P=P>P?P@PBPCPDP9PEPFPGPHPIPJPKPLPMPNMJVp=Eg00JKg00Jj#[g00H5RNg00IF#5RM#J#:%5M#5RM#5#5#5#:R?#BR>'RR=%:M#B#<\>R>g00N[RMg00Z0P5P:p,5LIMITROp,4SINVRPp,4argHRQp,3FS0RRP<PBP;P6P7M;>g00IkRS%HCg011T31%<3RTAFE9D%3C31AA8F;%ZH?AF;'UP5P:POPPPQPRP<PHP;P6P7M;>g001>%@6%@E31p,4scfgRUP5P@%;JRVP<P;D8;9E[[[^CM^5>^;=^3Ng0124#0#?#O#I#6#6#6#6#6RN,2GPSPSPSPTP41=HGPSPT%?NRN,2IR=g012SR>?7HGPSPT%0NRM,2I14HG%G3R;n0100000020000n0100000020000n0100000020001%3F51TP5PE%;HP9PDD8=9UC]0P41=GF%3ERW51TPUPOPPPQPRp,9argH_highp,:argH_agreeRXp,:SINV_frameRYp,:SINV_agreeRZp,5AIMW0PHPGPFPEP9PDPCPBP@P<P4P6MFKW0PSPT12HNA7>GFPSPT12HM14GFP;n0100000020000n0100000020000=1TWP=PSPSPSPTP4A7>JIPSPT12KMR=14JIP;n0100000020000n0100000020000%3H51TP5PGPVPFPED8=9U9]0P4A7>IH%3GRV51TPUPOPPPQPRPY1L?>p,7SMEARW0PJPIPHPGPFPEP9PDPCPBP4P<MDEW0PSPT12JM14IHP;n0100000020000=1TVP=PSPSPSPTP414LKP;n0100000020000%3JRS51TP5PI%;LPHPGD8=9UFR=]0P414KJ%3IRV51TP5PUP:P8POPPPQPRPAPXPZg013dPLPKPJPIPHPGPFPEP9PDP4PBMHMW0A1T;VPTP;P0P3p-0P4g00RZR0g00S7n10110100021000000X@Tg00SSPSP4ENP01D=4b6W0n0110000020000P7O1b1W0n0110000020001P7O1b1W0n0110001020001P6O1b1W8W0W9W7W<WBW4W:W2X?3X>3P5PUP:P8POPPPQPRP11P74M:QeW=WAP5PUP:P8POP2PPPQPRM9Ceo"). Qed.
End Hooks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stage.
  (* [comment removed for export] *)
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInitK.LIMIT.
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree APH0 sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH0 sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH0 sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  (* [comment removed for export] *)
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T fs'.
  Lemma HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Stage"] "h01Eh12E'h23fs'h31hp;3p;2g00<0j32Tg015;j31Tg016Gj20Tg00JKg00H5R0g001>g00Sof2R1f1R232g00Z0f4?112'0UW2X10W0W3o"). Qed.
  Lemma HOLES_nil : forall h E fs', HOLES h E fs' [].
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Stage"] "h01Eh13fs'h21hg00JKg00H5g001>p,5T_nilf0O1W1W0W2o"). Qed.
  Lemma HOLES_flat : forall h h' E E' fs', HOLES h E fs' = HOLES h' E' fs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Stage"] "h01Eh12E'h23fs'h31hh42h'p;3p;2g015;j31Tg016Gj20Tg00JKR0g00H5R1g001>g00Z0f3f1f031'0W2X11W0X40W3o"). Qed.
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH HOLES fs.
  (* [comment removed for export] *)
  Hypothesis X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs x.
  (* [comment removed for export] *)
  Variables KC0 BFUEL FUEL : nat.

  Theorem stage_sound : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (sd HOLES t_nil E (m_fs model) s).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Stage"] "h01Eh14FULLh22HCh35Hcerth41Rh53cs0h65modelh71ph81sp;1p;3p;2p;8p;7p;;p;4p;?p;Bp;@p;Fp;gg00_lj1QTg016aj14Tg00:Zj33Tg003Nj10Tg0066j1<Tg0043j11Tg004Qj12Tg001lj26Tg0054j17Tg0180j88Tg019:j79Tg006[l;:Tg01:Dj7?Tg01;\j8;Tg01=6j8@Tg01>Fj4ATg01?Vj45Tg005Vj1CTg00;4j1DTg016Gj2ETg01@fl?GTg01B4lBHTg01CKl@ITg01DclFJTg01F@lFKTg01G^lFLTg01I?lgMTg00PGR0f7R1g00QQR2g00SoR3g01JYR4g00\MR5g008QR6g00VGR7f6R8f5R9f4R:f3R;f2R<f1R=f0R>M?Gp=PP0P>P=P2P3P4P<P;P:g01KcR?g01M:R@g00nnRAg01NRRBP9g010ERCP8P1f8RDMBHp=OP0P8P9P2P3P4P:P;P<g00mWREP?P@PAPBP=P>M@Ip=NP0P>P2P3P4P=P<P;P:g00l>RFPEP?P@PAPBP9PCP8P1PDg01OkRGg01QERHMFJp=BP0P>P2P3P4P=P<P;P:PFPEP?P@PAPBP9PCP8P1PDPGPHMFKp==P0P>P2P3P4P=P<P;P:PFPEP?P@PAPBP9PCP8P1PDPGPHMFLp=>P0P>P=P<P2P3P4P;P5P6P7PFPEPAPBP:P9P8PCP1PDf9g015;g01R\g01Sng01U>f:f;f<f=f>f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRg01VOfSg00SSfTMgMp=Fg01WXg00L<g01Xgg01Z7p,3IT0RCp,2HSRBp,3KC0RAp,5BFUELREp,4FUELRFg01[F#QR7P=P<GP%4>33g00H5g00IF#0R6#<#1%06#0R6#0#0#0#1#2R5'6%16#2#7\5g00N[P0P2P4g01\XR5p,2spR6p,5rdrawRHp,4brk0p,4argvRGp,4envpR@p,3uidR?p,2hwRIG8RJP5P6PHPGP@P?PIF9RIp,2fsR?P;P8P<P=P>M;:p,4scfgR@PCp,6IT0_okPBPJPIp,2AHRBp,2AARCp,2SFRGp,2SARHP?PAP@p,6HallocRAPJPIP?PBPCPGPHM9OP@PAPJPIP?PBPGFNP@PJPIP?PAPBPCPGPHM9BP@PJPIP?PAPBPCPGPHM9=P@PJPIP?PAPBPCPGPHM9>P0P@P2P4PJPIP?F?p,5X_ALLP0P@P2P3P4PJPIP?G;P4PJPIP?PBPCPGPHG@P4PJPIP?CAP4PJPIP?C5p,8HS_soundPFPEP7PDP1P8P9P:P;P<P=P>g00OQR>#C%D>'EMUFW2W6W1W4W0W3W8W5W7o"). Qed.

  (* [comment removed for export] *)
  Corollary stage_hole : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s -> hole_only s = true ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (T (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Stage"] "h01Eh14FULLh22HCh35Hcerth43Hhoh51Rh63cs0h75modelh81ph91sp;1p;3p;2p;8p;7p;;p;5p;9p;?p;<g00_lj1FTg016aj16Tg00:Zj33Tg01]`j1DTg003Nj10Tg0066j1:Tg0043j11Tg004Qj12Tg001lj27Tg0054j14Tg0180j88Tg019:j79Tg006[l;CTg00?Yj1BTg00@dj5<Tg00>fj1;Tg01_2j5=Tg01`Cl9>Tg01aUj8@Tg01@fl?ATg01bbl<5Tg00PGR0f7R1g00QQR2g00SoR3g01JYR4g00\MR5g008QR6g00VGR7f6R8f5R9f4R:f3R;f2R<f1R=f0R>M?Ap=EP3P:P5P6P7g015;R7g01U>g01VOR6P;P<P=P>M<5p=?g01WXg00L<g01Xgg01Z7p,3IT0p,2HSR5p,3KC0p,5BFUELp,4FUELg01[F#FP=P<GE%6>33g00Ik%D=g011T33g00H5g00IF#0R3#:#1%03#0R3#0#0#0#1#2R?'7%13#2#4\?g00N[P0P2P4g01\XR4p,2spR2p,5rdrawR?p,4brk0p,4argvR3p,4envpR@p,3uidRAp,2hwRBG8P4P2P?P3P@PAPBF9p,2fsP;P1P<P=P>M;Cg00U;P0p,4scfgP0P;f8R0#BP<P=D<P7P6P:%;=R6P1D=p,1TP6O1f9P0P1P8P:P;P<P=P>M9>P5P:P6P1P9D?G@W2W7W1W5W0W4W3W9W6W8o"). Qed.

  (* [comment removed for export] *)
  Lemma holes_stmt_ext : forall JS : nat -> option acs,
    (forall h c, JS h = Some c ->
       forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E c R FULL model ->
         srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc c) FULL model) (T (m_fs model))) ->
    holes_stmt ASEGS0 scfg ASAN0 LIM (hs_ext HS JS) SINV argH HOLES fs.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Stage"] "p'0h02Ejh12Hhh22HCh31Eh44FULLh51Hh61Rh71ci001ch82chh91hh:5modelh;2HJh<2JSh=1eh>1oi011oi021ai031xp;1p;3p;2p;8p;7p;5p;6p;9p;;g0054R0j1:Tg00:Zj30Tg003Nj12Tg0066j1ITg0043j15Tg004Qj19Tg001lj2>Tg0180j8<Tg019:j7;Tg00?Yj17Tg00@dj56Tg00>fj18Tg01d>j3Hj2ATg016Gj2GTg01eMj6FTg00;Tj7BTg00_lj1?Tg015;R1j3@Tg01ejl9=Tg00:8j2CTg006[l;DTg00B9j5ETg00L<R2f0R3'Cp=1g00PGR4g00QQR5g01JYR6f7R7f6R8f5R9f4R:f3R;f2R<f1R=P3M;Dp=4g00U;P4P<P=P3DEp=3g00JKR>%:2R?[P<P=O1%13R@50?g00H5RAg00IF#2RB#I#5%2B#2RB#2#2#2#5#9RC'>RD%5B#9#:\CRCg00N[RBg01\XREp,2spRFp,5rdrawRGp,4brk0p,4argvRHp,4envpRIp,3uidRJp,2hwRKG<RLPEPFPGPHPIPJPKF;RKp,2fsRJP;P9P<P=P3G4RIp,4scfgRHP4P;%78P<P=D6RGp,1TRF%8=REO133[]:]4]6]3[^72^9>p,2HSRM?H;==0?@f9RNP7O1P?1G?3f:ROf8RPO1=0?3P0P2f<RQPOO1=0?3P0P2P?P=P@PMf;RRO1n10110300021010000%1O50?P4PP%7RP7P8D6PF%88O153H]1]0P=f=RSPRO1=0?@%1=%1R50?P?P2P0P2P2P3P3P;n10110100021010200X=?%1<%1QP3EFA02<QA02;SP2P:PLPKPJPSP3PQPRPOG4P4PS%7=PQPRD6PF%8RO153H]2X82PLPKPJPQP:PRPOPNG4fAf@P9P:PSPQPRPOP3O8W2f>P3PPFBW5P3O1b5W1W0X72P3O1PRPNO1%?250?PMPOO1%1N50?p,8HS_soundPRPOP3PPP7P8P9P:O8W1W0n10110100021010200P3P7O2b0b>A@7:E93HGeX2IX:BX4CX6DX3AW1X82X9>P4PHP5P61AM=PLPKP1PJM9=eW;W<o"). Qed.
End Stage.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Startup.
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.   (* [comment removed for export] *)
  Variable abrt : bool. Variable ur : InputStream.  (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Hypothesis X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs x.
  Variables KC0 BFUEL FUEL : nat.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert :
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None asan0_init startup_plan = COk startup_shape.

  Theorem as0_startup :
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (sd (HOLES T) t_nil E0a fs startup_shape).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Startup"] "h02HCh13IMGh21cp;3p;1p;7p;Ap;5p;8p;Lp;;p;Mp;=p;9p;2p;Fp;6g01gCj3ETg01hSj1DTg01iZj10Tg01jjj71Tg01l4lACTg00@dj52Tg015;j13Tg01m?j84Tg01_2j55Tg00B9j56Tg01nFlL7Tg0180j88Tg019:j79Tg01oUj1BTg006[l;:Tg01`ClM;Tg020il=<Tg0221l9=Tg022ij1>Tg016Gj2?Tg023GlF@Tg000`j6ATg024Wg00PGR0g00QQR1g01\XR23Eg0260R3P0p,2spR4#DR5%01P2P4p,5rdrawR6p,4argvR7p,4envpR8p,3uidR9p,2hwR:F1R;P0P4p,4brk0R<p,5mbaseR=P7P8p,2fsR>p,5stdinR?P9p,3gidR@P:p,6groupsRAp,3netRBp,6nofileRCp,7sigmaskRDp,4abrtREp,2urRFMACRGD2g00U;P0p,4scfgf0RHp,1TRI#3g01VOP2P4P6P<P7P8P9P:G4RJP>p,=startup_shapeRKD5D6X23P0P1P2P4P6P<P=P7P8P>P?P9P@P:PAPBPCPDPEPFPHp,3HspR3p,4Hbrkp,3HvaRLp,3Hvep,4Hfitp,4Huidp,3HhwML7P0P1g01JYRMP2P4P6P<P7P8P9P:G8P2P4P6P7P8P9P:F9P>PJ%B1P5P;PGM;:P4P<P6P7P8P9P:P>P3PLp,3IT0p,6IT0_okp,2HSPIp,5T_nilp,8HS_soundp,5X_ALLp,3KC0p,5BFUELp,4FUELp,<startup_plang026ePKp,<startup_certPJP5P;PGPHMM;b0P0g0283RHP2P4P<P=P6PMP7P8P>P?P9P@P:PAPBPCPDPEPFM=<M9=P0P1P2P4P6P<P=P7P8P>P?P9P@P:PAPBPCPDPEPFPHg00GW%>H'?MF@EAb1o"). Qed.

  (* [comment removed for export] *)
  Corollary as0_startup_hole : hole_only startup_shape = true ->
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (T fs).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupK ()) ["As0"; "Startup"] "h02HCh13Hhoh23IMGh31cp;1p;3p;7p;Ap;5p;Lp;8p;;p;Np;=p;9p;2p;Fp;6g01]`j1ETg00:Zj3DTg01gCj30Tg01hSj11Tg01iZj1CTg01jjj72Tg01l4lA3Tg00@dj54Tg00B9j55Tg01nFlL6Tg0180j87Tg019:j78Tg01m?j89Tg01oUj1BTg006[l;:Tg029=lN;Tg020il=<Tg0221l9=Tg022ij1>Tg016Gj2?Tg023GlF@Tg000`j6ATg00Ikp,=startup_shapeR0#Eg011T3Dg024Wg00PGR1g00QQR2g01\XR330g0260R4P1p,2spR5#1R6%C2P3P5p,5rdrawR7p,4argvR8p,4envpR9p,3uidR:p,2hwR;F2R<P1P5p,4brk0R=p,5mbaseR>P8P9p,2fsR?p,5stdinR@P:p,3gidRAP;p,6groupsRBp,3netRCp,6nofileRDp,7sigmaskREp,4abrtRFp,2urRGMA3RHD4g00U;P1p,4scfgf0RIp,1TRJP?O1D5X34P1P2P3P5P7P=P>P8P9P?P@P:PAP;PBPCPDPEPFPGPIp,3HspR4p,4Hbrkp,3HvaRKp,3Hvep,4Hfitp,4Huidp,3HhwML6P1P2g01JYRLP3P5P7P=P8P9P:P;G7P3P5P7P8P9P:P;F8P?P3P5P7P=P8P9P:P;G9RM%B2P6P<PHM;:P5P=P7P8P9P:P;P?P4PKp,3IT0p,6IT0_okp,2HSPJp,5T_nilp,8HS_soundp,5X_ALLp,3KC0p,5BFUELp,4FUELp,<startup_plang026eP0p,<startup_certf2PMP6P<PHPIMN;b0P1g0283RIP3P5P=P>P7PLP8P9P?P@P:PAP;PBPCPDPEPFPGM=<M9=P1P2P3P5P7P=P>P8P9P?P@P:PAP;PBPCPDPEPFPGPIg00GW%>I'?MF@EAb2W1o"). Qed.
End Startup.
End As0.
