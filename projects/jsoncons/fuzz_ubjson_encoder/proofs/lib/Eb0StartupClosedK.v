(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
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
  AsanNodesExtraDefsK AsanNodesExtraK Eb0StartupK AsanXAllKB0 AsanAddrIsInMemWalkKB0 AsanMaxVAWalkKB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eb0StartupClosedK () := "C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libFAsanAddrIsInMemWalkKB0@asan_addrisinmemC13~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK=X_MAXVA_ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanMaxVAWalkKB0@asan_maxva_entryC13~~~I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1Z02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare3at_C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare:regs_agreeC13~~~I47Corelib4Init5Logic2ex00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanMaxVAWalkKB0<asan_smearvaC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare4at_0C13~~~C47Corelib4Init5Logic8eq_ind_rK45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK6ASEGS0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEb0StartupClosedK>asanreflect_fxC13~~~K47Corelib7Numbers7BinNums1Z01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEb0StartupClosedKBas0_maxva_entry_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanXAllKB0:asan_X_ALLC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK:stage_holeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEb0StartupClosedK8as0_AIMWC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEb0StartupClosedK:as0_SMEARWC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEb0StartupClosedK9as0_X_ALLC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0StartupK@as0_startup_holeC13~~~".
Import ListNotations.
Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

Lemma as0_AIMW : aim_spec ASEGS0 AIM_ASAN0.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupClosedK ()) [] "g0000o"). Qed.

Lemma as0_maxva_entry_eq : Z_to_bv 64 X_MAXVA_ASAN0 = asan_maxva_entry.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupClosedK ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g001Rj12Tg0025j33Tg002Oj21Tg0039j34Tg003]j10Tg004Bj17Tg004`j26Tg005Fj25Tg005`R0f0R1#2R2f1R3#2R4g006>f2R5#2?331g006YR6f3R7/15117333R8[11531151536%27?353[R9f4#2?375\8A4531P1n2001000000120000000W1W0W2P9^14^02^20P1g0077#0#0#0#0#0#0#7R1g007\,61g008mR01110,56O4b3o"). Qed.

Lemma as0_SMEARW : forall (mem rom : word -> option byte) regs (x : word),
    getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
    exists regs',
      msteps ASEGS0 (mkst regs (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 0) mem rom) (mkst regs' (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 180) mem rom)
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
      /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
      /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
      /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
      /\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupClosedK ()) [] "h01bh15regs'h22Hrh32Hxh43memh51rh64regsh73romh81xp;1p;2p;3p;5p;6g003]j11Tg004Bj1BTg001Rj1CTg00:Ij1TTg00:kj10Tg00;Pj2PTg00<<j12Tg00<Zj28Tg0025j3:Tg00=bj2ETg002Oj2ITg00>?j2STg00>[j2RTg006>j26Tg00?7j2ATg00@;j5@Tg00ACj3FTg00BMj2OTg004`j29Tg00Bjj1NTg00CJj3=Tg00Cjj3MTg00DAj3LTg00ELj2GTg00Efj6KTg00G>j1JTg00HCj6HTg00Haj3QTf0R0#1#1p=4f1R1g00ID7Q0p=<%10#0p=7%00#0#0#0p=5%00#0#0#0#0#0#0#0p=>%00#0p=D%10#1#0#0#1#1#0#0p=;%10#1#1#1p=3%10#1#1#1#1#1#1#1p=?g0077R2#1R3#4R4#1#4R5#BR6#CR7%B4#C#T[R4%03R8#BR9/P7R:%18#2,<9R;,81=:70%23R3%08R8#0R<#1#2'E1I61R='S%0<#2,E3R3,R='6P7g008mR=g00I`R<g00JjR>f5R?g00LER@,A1f7RAf6RBD@P>P0%78#4#2RC,A1PAPBD@3F180;%22,O3,965:7%28,<9R8,80%02R2#0R3#0RD#0#5#>RE#0#D#5#>#>#>#>#>#2,965:7%12R2#1RF#2,<9RG,80%DF#;#;#;#;#;#;#;#2,965:7%02#2,<9R2,80%3D#5#3#5#3#5#3#5#3#5#3#5#3#5#2,965:7%13#2,<9R3,80%75#4#3#7#4#3#7#4#3#7#4#3#7#4#3#7#4#3#7#2,965:7%2D,<9RD,80%4E#3#?#?#?#?#?#2,965:7%C9R9%N99=9D9=939=929=9G9=989=9;9M90W5?L?0'6'6'6'6'6'6R9'6X1:,G:X07P7P=P>P?P1PAPBD@P>P01A=CPAPBD@5F</69X1:,G:X07P?f4f3f2P1P0EK1A=@%J=EHg007\,96g00LcEHW2W3X87W6X74W4o"). Qed.

Section Closed.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Lemma as0_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs x.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupClosedK ()) ["Closed"] "p;=g00NBl=0Tp,4scfgp,2spp,4brk0p,5rdrawp,4argvp,4envpp,3uidp,2hwp,2fsp,3Hspp,3Hvap,3Hvep,4HfitM=0o"). Qed.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Variables KC0 BFUEL FUEL : nat.

  (* [comment removed for export] *)
  Theorem as0_stage_hole : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s -> hole_only s = true ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (T (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupClosedK ()) ["Closed"] "p;Hg00OSlH0Tp,4scfgp,6Hallocg00Pdg00R9p,2spp,4brk0p,5rdrawp,4argvp,4envpp,3uidp,2hwp,2fsp,3Hspp,3Hvap,3IT0p,6IT0_okp,2HSp,1Tp,5T_nilp,8HS_soundg00SPp,3KC0p,5BFUELp,4FUELMH0o"). Qed.
End Closed.

(* [comment removed for export] *)
Section ClosedStartup.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
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
  #[local] Notation LIM := AsanInitK.LIMIT.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Variables KC0 BFUEL FUEL : nat.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert :
    check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None asan0_init startup_plan = COk startup_shape.
  Hypothesis startup_ho : hole_only startup_shape = true.

  Theorem as0_startup_hole_c :
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (T fs).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0StartupClosedK ()) ["ClosedStartup"] "p;=p;Zg00SPl=1Tg00TflZ0Tp,4scfgR0p,6Hallocg00Pdg00R9p,2spR1p,4brk0R2p,5mbasep,5rdrawR3p,4argvR4p,4envpR5p,2fsR6p,5stdinp,3uidR7p,3gidp,2hwR8p,6groupsp,3netp,6nofilep,7sigmaskp,4abrtp,2urp,3HspR9p,4Hbrkp,3HvaR:p,3HveR;p,4HfitR<p,4Huidp,3Hhwp,3IT0p,6IT0_okp,2HSp,1Tp,5T_nilp,8HS_soundP0P1P2P3P4P5P7P8P6P9P:P;P<M=1p,3KC0p,5BFUELp,4FUELp,<startup_planp,=startup_shapep,<startup_certp,:startup_hoMZ0o"). Qed.
End ClosedStartup.
