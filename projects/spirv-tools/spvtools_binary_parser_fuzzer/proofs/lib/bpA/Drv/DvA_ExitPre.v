(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HCatSim HShapeAlg HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX HSymAux.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LazyRestrict LazySR LazyFdNodes AsLazyRun.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsPrintfFirst AsExitDefs DvA_ExitKit DvA_ExitTmpl DvA_ExitLoop.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_DvA_ExitPre () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre4XENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF>HSymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre4kn_XC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF>HSymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I69OSSVerify5KrLib3bpA2HF6LazySR4lzok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF<LazyRestrict8restrictC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib3bpA2HF9HPropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HPropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv;DvA_ExitKit9rflat_chkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre3xs0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpA2HF7HSymRun7vals_evC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib3bpA3Drv;DvA_ExitKit?rflat_chk_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF7HSymAux<regions_flatC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib3bpA2HF9HSymDrive8blobs_evC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC69OSSVerify5KrLib3bpA3Drv;DvA_ExitKit5xs_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HSymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltI47Corelib4Init5Logic2ex00C69OSSVerify5KrLib3bpA2HF<LazyRestrictEsame_but_materializedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF6LazySR8hid_sameC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC79OSSVerify5KrLib3bpA2HF9HSymExec23SX22evC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib3bpA3Drv<DvA_ExitLoop7ax_loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF<LazyRestrictHsame_but_materialized_fsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv9AsLazyRunCrz_msteps_lazy_mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv;DvA_ExitKit=xchain_rebaseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2HF9HShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC69OSSVerify5KrLib3bpA3Drv;DvA_ExitKitCxchain_rebase_soundC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2HF7HCatSim6msteps00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK79OSSVerify5KrLib3bpA2HF9HSymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF7HSymAux6rdenotC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib3bpA2HF6HFrame9frame_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre9x_regionsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre3XNVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv<DvA_ExitTmpl4XNVTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre9PRE_CLEANC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv<DvA_ExitTmpl4ACUTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv<DvA_ExitTmpl5XKEPTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv<DvA_ExitTmpl4sr_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv<DvA_ExitTmpl4kn_TC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3bpA2HF4Scfg=hunspell_scfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF7HSymAux7sregionC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib3bpA3Drv:AsExitDefs4x_srC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv:AsExitDefs5AEXITC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre=pre_clean_chkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre4xk_UC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre5xk_T0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv;DvA_ExitPre5xk_U2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Asan.M.loaded_segments.

Definition XNV : nat := 41.
Definition XENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

Definition ATB_LO : Z := 4096.
Definition ATB_HI : Z := 0x7fffff472000.
Definition AIMGR_LO : Z := 0x10000.
Definition AIMGR_N : Z := 0x6d6000.
Definition ASHR_LO : Z := 0x7fff7000.
Definition ASHR_N : Z := 0x10007fff8000 - 0x7fff7000.

Definition shx : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-260))) (ELit 3)) (ELit 0x7fff8000)) (ELit (-8)).
Definition SHX_LO : Z := 0x10006fdf7fd8.
Definition SHX_HI : Z := 0x10007fff8000.

Definition x_regions : list sregion :=
  [(SA (EVar 0) (-2560), 2560); (SA (ELit 0) 0x6e3f68, 32); (SA (ELit 0) 0x6e4188, 4); (SA (ELit 0) 0x18c090, 1);
   (SA (ELit 0) 0x18c040, 8); (SA (ELit 0) 0x18cfb0, 8); (SA (ELit 0) 0x6c3ee8, 8); (SA (ELit 0) 0x7fffa000, 0xdac00);
   (SA (ELit 0) 0x187f60, 232); (SA (ELit 0) 0x188140, 232); (SA (EVar 40) 0x14dc00, 8); (SA (EVar 40) 0x224ac0, 8)].

Definition kn_base : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (-2560)) 2560; KRange (EVar 1) 1 2147483647;
   KImg 0x10000 0x91000; KImg 0x17c000 0x185000; KImg 0x188048 0x188140; KImg 0x188228 0x18c040;
   KWord (SA (ELit 0) 0x6c3e70) 4 (EVar 1); KWord (SA (ELit 0) 0x6e3f58) 8 (EVar 3);
   KWord (SA (ELit 0) 0x18ef48) 8 (EVar 40); KAlign (EVar 40) 4096; KRange (EVar 40) ATB_LO ATB_HI;
   KDisj (SA (EVar 40) 0x14dc00) 96 (SA (ELit 0) AIMGR_LO) AIMGR_N; KDisj (SA (EVar 40) 0x224ac0) 96 (SA (ELit 0) AIMGR_LO) AIMGR_N;
   KDisj (SA (EVar 40) 0x14dc00) 96 (SA (ELit 0) ASHR_LO) ASHR_N; KDisj (SA (EVar 40) 0x224ac0) 96 (SA (ELit 0) ASHR_LO) ASHR_N;
   KDisj (SA (EVar 40) 0x14dc00) 96 (SA shx 0) 8; KDisj (SA (EVar 40) 0x224ac0) 96 (SA shx 0) 8;
   KDisj (SA (EVar 40) 0x14dc00) 96 (SA (EVar 0) (-2560)) 2560; KDisj (SA (EVar 40) 0x224ac0) 96 (SA (EVar 0) (-2560)) 2560;
   KZero (SA (EVar 40) 0x14dc00) (ELit 96); KZero (SA (EVar 40) 0x224ac0) (ELit 96);
   KWr (SA (EVar 40) 0x14dc00) 8; KWr (SA (EVar 40) 0x224ac0) 8;
   KWord (SA (ELit 0) 0x800d03f8) 8 (ELit 0);
   KZero (SA shx 0) (ELit 8); KRange shx SHX_LO SHX_HI;
   KWr (SA (ELit 0) 0x187f60) 232; KWr (SA (ELit 0) 0x188140) 232; KWr (SA (ELit 0) 0x18c040) 8; KWr (SA (ELit 0) 0x18c090) 1;
   KWr (SA (ELit 0) 0x18cfb0) 8; KWr (SA (ELit 0) 0x6c3ee8) 8; KWr (SA (ELit 0) 0x6e3f68) 32; KWr (SA (ELit 0) 0x6e4188) 4;
   KWr (SA (ELit 0) 0x7fffa000) 0xdac00].

Definition kn_c (cs : list (Z * nat * Z)) : list kentry :=
  map (fun c => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cs.

Definition xk_common : list (Z * nat * Z) := [(0x185580, 8%nat, 0x185580); (0x1855d8, 8%nat, 0x16c1ec); (0x185648, 8%nat, 0x16a760); (0x185680, 8%nat, 0x16b77c); (0x185780, 8%nat, 0x1750fc); (0x185788, 8%nat, 0x175500); (0x1877fc, 4%nat, 0x8); (0x187f60, 4%nat, 0x5); (0x187fb8, 8%nat, 0x6e4730); (0x187fc0, 8%nat, 0x0); (0x187fec, 4%nat, 0xffffffff); (0x187ff0, 4%nat, 0xffffffff); (0x188048, 8%nat, 0x187f60); (0x188058, 8%nat, 0x0); (0x188060, 8%nat, 0x0); (0x188078, 8%nat, 0x0); (0x188088, 8%nat, 0x0); (0x1880dc, 4%nat, 0xffffffff); (0x188138, 8%nat, 0x188050); (0x188140, 4%nat, 0x5); (0x188198, 8%nat, 0x6e4b40); (0x1881a0, 8%nat, 0x400); (0x1881cc, 4%nat, 0xffffffff); (0x188228, 8%nat, 0x188140); (0x18c040, 8%nat, 0x1); (0x18c090, 1%nat, 0x0); (0x18cf10, 4%nat, 0x1); (0x18cf14, 1%nat, 0x0); (0x18cfb0, 8%nat, 0x0); (0x18ef40, 8%nat, 0x18ef48); (0x18ef5c, 1%nat, 0x1); (0x18f6f8, 8%nat, 0x7fff8000); (0x1903d8, 1%nat, 0x1); (0x1903d9, 1%nat, 0x1); (0x2212a0, 8%nat, 0xffffffffffffffff); (0x2215a0, 1%nat, 0x0); (0x6c1ff8, 8%nat, 0x181250); (0x6c2038, 8%nat, 0x188140); (0x6c2040, 8%nat, 0x6c2a70); (0x6c2048, 8%nat, 0x6c1fc4); (0x6c2058, 8%nat, 0x181250); (0x6c2098, 8%nat, 0x187f60); (0x6c20a0, 8%nat, 0x6c2a70); (0x6c20a8, 8%nat, 0x6c1fcc); (0x6c20b8, 8%nat, 0x181380); (0x6c20f8, 8%nat, 0x188140); (0x6c2100, 8%nat, 0x6c2c00); (0x6c2108, 8%nat, 0x6c1fdc); (0x6c2118, 8%nat, 0x181380); (0x6c2158, 8%nat, 0x187f60); (0x6c2160, 8%nat, 0x6c2c00); (0x6c2168, 8%nat, 0x6c1fe4); (0x6c2248, 8%nat, 0x180df0); (0x6c2259, 1%nat, 0x10); (0x6c2270, 4%nat, 0x0); (0x6c2278, 8%nat, 0x6c1ff8); (0x6c22d8, 8%nat, 0x0); (0x6c22e8, 8%nat, 0x180f10); (0x6c22f9, 1%nat, 0x10); (0x6c2310, 4%nat, 0x0); (0x6c2318, 8%nat, 0x6c20b8); (0x6c2378, 8%nat, 0x0); (0x6c24c8, 8%nat, 0x180df0); (0x6c24d9, 1%nat, 0x10); (0x6c24f0, 4%nat, 0x0); (0x6c24f8, 8%nat, 0x6c2058); (0x6c2558, 8%nat, 0x0); (0x6c2568, 8%nat, 0x180f10); (0x6c2579, 1%nat, 0x10); (0x6c2590, 4%nat, 0x0); (0x6c2598, 8%nat, 0x6c2118); (0x6c25f8, 8%nat, 0x0); (0x6c2a70, 8%nat, 0x1818c8); (0x6c2c00, 8%nat, 0x181618); (0x6c2c10, 8%nat, 0x6acc0); (0x6c3ee8, 8%nat, 0x6e41e0); (0x6e3f6c, 4%nat, 0x0); (0x6e3f78, 8%nat, 0x6e3f80); (0x6e3f80, 8%nat, 0x0); (0x6e3f88, 8%nat, 0x163a80); (0x6e3f90, 8%nat, 0x1252fc); (0x6e3f98, 8%nat, 0xae744); (0x6e4088, 8%nat, 0xd820c); (0x6e4090, 8%nat, 0x6c1fb8); (0x6e4098, 8%nat, 0x0); (0x6e4188, 4%nat, 0x0); (0x6e41ab, 1%nat, 0x0); (0x6e4720, 8%nat, 0x0)]%Z.
Definition xk_U : list (Z * nat * Z) := [(0x6e3f70, 4%nat, 0x3); (0x187f80, 8%nat, 0x0); (0x187fe8, 4%nat, 0xffffffff); (0x188160, 8%nat, 0x0); (0x1881c8, 4%nat, 0x0); (0x1881d0, 4%nat, 0xa)]%Z.
Definition xk_U2 : list (Z * nat * Z) := [(0x6e3f70, 4%nat, 0x3); (0x187f68, 8%nat, 0x0); (0x187f70, 8%nat, 0x0); (0x187f80, 8%nat, 0x6e4730); (0x187f88, 8%nat, 0x6e4730); (0x187f98, 8%nat, 0x6e4730); (0x187fe8, 4%nat, 0xffffffff); (0x188160, 8%nat, 0x0); (0x1881c8, 4%nat, 0x0); (0x1881d0, 4%nat, 0xa)]%Z.
Definition xk_T0 : list (Z * nat * Z) := [(0x6c1d54, 1%nat, 0x0); (0x6e3f70, 4%nat, 0x4); (0x6e3fa0, 8%nat, 0x163a80); (0x6e40a0, 8%nat, 0xe8bd4); (0x187f80, 8%nat, 0x0); (0x187fe8, 4%nat, 0x0); (0x188148, 8%nat, 0x0); (0x188150, 8%nat, 0x0); (0x188160, 8%nat, 0x6e4f40); (0x188168, 8%nat, 0x6e4b40); (0x188178, 8%nat, 0x6e4b40); (0x1881c8, 4%nat, 0xffffffff); (0x1881d0, 4%nat, 0xffffffff)]%Z.
Definition xk_T (j : Z) : list (Z * nat * Z) := [(0x6c1d54, 1%nat, 0x0); (0x6e3f70, 4%nat, 0x4); (0x6e3fa0, 8%nat, 0x163a80); (0x6e40a0, 8%nat, 0xe8bd4); (0x187f80, 8%nat, 0x0); (0x187fe8, 4%nat, 0x0); (0x188148, 8%nat, 0x0); (0x188150, 8%nat, 0x0); (0x188160, 8%nat, 0x6e4f40); (0x188168, 8%nat, (0x6e4b40 + 2 * j)); (0x188178, 8%nat, 0x6e4b40); (0x188188, 8%nat, 0x16b42c); (0x1881b8, 4%nat, 0x1); (0x1881c8, 4%nat, 0xffffffff); (0x1881d0, 4%nat, 0xffffffff)]%Z.

Definition kn_X (xk : list (Z * nat * Z)) : list kentry := kn_base ++ kn_c xk_common ++ kn_c xk.

Definition xs0 (xk : list (Z * nat * Z)) : xst := XS AEXIT x_sr (kn_X xk).

Definition XR (dirs : list bool) : xseg := XRun 40000%N [0x16b42c] dirs (fun _ => true).
Definition PRE_AHM : list xseg :=
  [XR []; XCas 8; XR []; XCas 8; XR []; XCas 8; XR []; XCas 8; XR [false]; XCas 8; XR []; XCas 8; XR [false]; XCas 8;
   XR []; XCas 8; XR []].
Definition PRE_CLEAN : list xseg := [XR []; XCas 4] ++ PRE_AHM.
Definition PRE_F1 : list xseg := [XR []; XCas 4; XR []].
Definition PRE_F2 : list xseg := PRE_AHM.

Definition pre_clean_chk (xk : list (Z * nat * Z)) : bool :=
  (rflat_chk (kn_X xk) x_regions
   && xchain_rebase RSEGS x_regions XNV XNVT PRE_CLEAN (xs0 xk) ACUT XKEPT sr_T kn_T)%bool.

Section Clean.
  Context {fx : DFP}.
  Variable xk : list (Z * nat * Z).
  Hypothesis CHK : pre_clean_chk xk = true.

  Theorem ax_clean : forall vals R M msF mo L S Zr,
    length vals = XNV ->
    regs_ok (XENV vals) x_sr R -> know_ok RSEGS (XENV vals) M (kn_X xk) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 AEXIT) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (bv_and (vals_ev vals 2) (Z_to_bv 64 255)) (m_fs mo)).
Proof.
ltac2:(KReplay.run1 (kr_t_DvA_ExitPre ()) ["Clean"] "p'0h01nh11Hh22M'h32R'h42CXh52_Hh62AGh72CFh83CHKh92HKh:3HK'h;2HLh<3HL0h=2HRh>3HR'h?3Hmsh@1LhA1MhB2OKhC3OK'hD1RhE2RFhF2RShG3RS'hH1ShI2SBhJ2ZrhK7__arithhL4__ffhM8__varmaphN5__withO1bhP4cstrhQ5cstr0hR1ehS1fhT2mohU3mo'hV3msFhW4msF'hX4valshY1xi001xhZ1yp&0p;1p;2p;3p;4p;5p;7p;6p;<p;=p;Cp;:p;Eg0000R0p4p70g000^R1p4p710p8g001:j1?Tg001_j1\Tg002=j1iTg002`j1LTg003@j1;Tg003ek20KTg004Qk10ITg0053j2hTg005Sj21Tg0063j39j1]Tg006Mj1RTg007Jj3_Tg008Qj1vTg009Nj4[Tg00:Uj2XTg00;Jj5sTg00<Cj3rTg00=Dj2HTg00=jk10JTg00>gj54Tg00?ak20HTg00@ck10ETg00A_k30@Tg00BBR2j2GTg00B]j20j1ETg00CXj1STg00D6j17Tg00Dij7}Tg00F1j2zTg00G1j6jTg00GOj1^Tg00Goj1wTg00Hmj3NTg00ILj3tTg00Ink10LTg00Jlj16Tg00KkR3j22Tg00LCR4j2QTg00L]k20FTg00Mkk40DTg00Nfj13Tg00OER5k20ATg00Oaj2ITg00P;R6j1KTg00P[k20=Tg00Q>k30<Tg00Q[l<`Tg00R@k40:Tg00Rgj1eTg00SLj2dTg00Shk109Tg00TFk108Tg00Tdk107Tg00UOj2bTg00V2k405Tg00V]k704Tg00WAk202Tg00Wck201Tg00XOk303Tg00Xnk400Tg00Y`k406Tg00ZKj2aTg00[Gj3UTg00[ll=|TP1j6fTg00\mj3{Tg00^>mC0>Tg00_Hl:gTg00`Nj2ZTg00aJj4mTg00bJj2OTg00balEyTg00cmj3xTg00dij3>Tg00eFj2JTg00fEj1kTg00g?j4qTg00g[j3pTg00hWR1g00j5R7g00k7R8g00l3R9g00m1R:f0R;g00n3R<g00o1R=g0100R>g010nR?M:gp>0Bg011lR@g012LRA79;p=F%3;#3p=cP1g012lRBf5RCf4RD'Xf3REf2RFf1RG3U/Z;Cmp==P1P7PGP9P:P;P<P=P>P?M:gp=o11G;,O9p=uP;P1P7P9P:PGP<P=P>P?PFPEPDPCf6R=f7R:f8RHf9RIf:RJf;RKf<RLMEyp>0MAx1G;p=D11G;,O99NEFp=CA>EFG9>CD#E/J;p=YA_G>;p=<1O9;9NFGp=5A>DEF9>=C/0G=9:;p=:g013jR>PE%EF/JG#kP7Cq9pCD/G;p=8P1PFPGP?C[/G;p=B1GG;,GFp=A%6G9>EF9>CD#E/J;p=@1O9G9NEF=>D;9>=Cp=W10EF10G;59Dp=V%EG/J;p=TP1PGP;P?C[p=P1JG;#kp=nP>PGP;P7Cq9pEFp=l10EF=UDG/Z;p>0G%3;#3#3#3p>0C%3;#3#3#3#3#3#3#3p=Mg014eR>g015DR?P3P6P5g015bPCPDPEPFPGP;M<`p>0?10G;99EFp=~P1PBPF1ZG;Cmp>0;g016DRB#?R5#?#?R3#?#?#?#\R9#iRM#L%;5RN#\00KMRO%\3#iR3$0I\MRPg016iRQg0180RR1hMM#LRS11M:=9>8%RHg018f;_:P1%RIP:p,2xkRT#vRUC[P1PCPDPE1X:=RVDsAr=CHp,2fxRWPJg019b,H9RXPI&0J1RYD459Q20HU7RZ&0ETRT$0BR[p,3CHK40@%FZRZ%F[R['GP2PZP[PKPJP9f>R\g01:_#cR]'0%;B#;#;#;#;#;#;#S,H9RB%7JE=P;P1fAR^#RR_f?R`PUP7P:PGF}1z_7P>P81o;T#FX0>PGfBR_,1MR7PJEj1o7T#FPWPTfCR7%L3#^#wR3P_P^PYg01;>RU,H9Ra1uM7Rb5NMP;AtMabPGPJPIN=0MPWfDRb&0LT,H9RTP7PYD4PWPG1H9<R<P;PYD4Rc'DPMfERdPMPMPaPMPdCC%6GReP3EYRf/<GP7P;1hM?RgPdP3fFRh,1MRi,2;PMPMfGRjPM11MjRk95Ma%6ERlPG10jGG:[^0>E89Bf;3AX2P,QPX3O,QOP4POPWPdPTPbPYD4/DcPMPhPMA5MaiPeP3EYRi/<GPbP;PgPhP312;kPMPMfHRkPMPMPaPMPkCCRbPlPG10kGG:[^0>E89Bi;3AX2P,QPX3OP_P^P910d]PB%7^E=P;PWPjPTPhPYD4/DcPMPkPMPbPeP3EYRe/<GPhP;PgPkP3fIRb,1MRc,2;PMPMfJRiPM11MiRf95MaPlPG10iGG:[^0>E89Be;3AX2P,QPP4PPPWPkPTPjPYD4PWPFP<P;PYD4'DPMPbPMA5MacPFP3E@Rc/<FPjP;PgPbP312;fPMPMfKRfPMPMPa11Mf%6DFWRjPGPfPGDV[^0>E89Bc;3AX2PPhPdP910b]PB%7dE=P;PWPiPTPbPYD4PWPDP<P;PYD4'D1Tj3Rj/<DPbP;PgPfP3fLRc,1MR4,2;PMPMfMRePM11MeRl95Ma%6=PG10eGG:[^0>E89Bj;3AP2PWPfPTPiPYD4PWPCP<PGPYD4'DPMPcPMA5Ma4PCP3E@R4/<C1P4GPiPGPgPcP312;lPMPMfNRlPMPMPaPMPlCC%6:PG10lGG:[^0>E83APiPbP910e]PB%7bE=P;PWPePTPcPYD4PWP:P<PEPYD4'DPMfOR:PMPMPaPMP:CCPHP3E@RT/<H1PTDPePDPgP:P3fPR:,1MRT,2;PMPMfQRbPM11MbR495Ma%6JPG10bGG:[^0>E83AP2PMP:PMA5MaTPIP3E@RT/<IPlPCPgP:P312;4PMPMfRR4PMPMPa11M4%6KFWRJPGP4PGDV[^0>E89BTCPlPeP910b]PB%7eE=P;1TJ3/<KPMfSRJPMPMPaPMPJCCPLP3E@PbPHPgPJP3fTRJ,1MRe,2;PMPMfURlPM11MlRT95Ma%6\PG10lGG:[^0>E87BHP2PMPJPMA5Maef=ReP3E@/PIP4PIPgPJP312;TPMPMfVRTPMPMPa11MT%6`FWRJPGPTPGDV[^0>E8P4PbP910l]PB%7bE=P;1TJ3/PKPlPLPgfWRKP3fXRJ,1M,2;PMPMfYR4PM11M4RI95Ma%6_PG104GG:[^0>E8P2PTPePg%EJ/n3Cl12;IPMPMfZRIPMPMPaPMPICC%67PG10IGG:[^0>PTPlP9104]PB%7lE=P;PJP`Pg%EI/n3Clf\Rg,1M,2;PMPMf]R`PMPMPaPMP`CC%6hPG10`GG:[^0>PWP1PKPTPlP4f[RlPXPIPYPdP<P^PJP9PgP]PB%7JI0GPbP:PeP1P4PJPK1XG;Ds20FlGPlPIP`PEH0DArglDPWPiP<PhPYD459QP0%7DP=PCP9fcRY/0]RhPBP;E=XS0P=P]P>P812];X0>%3]#c$0C#M#M#M#MR0,2]%S5R5%?N#?#;#SRN+0AR<P]P51I?5P0PN1I?NJ0?fbR0,1MRi=9>8%KiRl%K8RE59?RKP>P?%]>P6%]?%KG%K;59?A9>G;20=G;40<XZ>XY>PiPl1I?lP8PE1I?EM<`PIH0:PK11MYRK#e%KK,dU%e81dUEg01;\RE#^%LE&09?&08?&07?REg01<Hg01<gRlPlg01=GRlP?1b?5g01=g1b?NH05g01>NK04202ElP;PF1I@A201;F#FdB03?UGH00bLbMbNP<P;bKbQbPb<H0612]8ePiPIEjO2PMPMP0PMA5MaiPfP3E@/a]P0P]C~R0eP0PMPMPYPMA5MaKPcP3E@R3/a]AU9;B%7=60;VXOMPWP3PcPkP=PCf^RCP`Pgf@PLPDPGM=|PhP;Efb1%7CA{CDFEfWGW5WIWCXURXWQNC0>W6W5PGP;O2n2001000000121000000W1W:PGP;O2n2001000000121000000W1W>PGP;O2n2011000000121000000W1W?PGP;O2n2011000000121000000W1X2PPGP;O2n2011000000121100000W1X3OPGP;O2n2011000000121100000bRb4bEX4[X7ZPGP;O2n2001000000121000000b8WFWBW9W=W;XJSXHSW@WTWVWAWDWXo"). Qed.
End Clean.

Lemma pre_U_ok : pre_clean_chk xk_U = true.
Proof.
ltac2:(KReplay.run1 (kr_t_DvA_ExitPre ()) [] "p;2p;1p;3g00Oaj22Tg01>nj11Tg0063j30Tg011lR0g012LR1'2g01@4#1=001do"). Qed.
Lemma pre_T0_ok : pre_clean_chk xk_T0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_DvA_ExitPre ()) [] "p;2p;1p;3g00Oaj22Tg01>nj11Tg0063j30Tg011lR0g012LR1'2g01A1#1=001do"). Qed.
Lemma pre_U2_ok : pre_clean_chk xk_U2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_DvA_ExitPre ()) [] "p;2p;1p;3g00Oaj22Tg01>nj11Tg0063j30Tg011lR0g012LR1'2g01Ao#1=001do"). Qed.
