(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatSim BShapeAlg BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymAux.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict BazySR BazyFdNodes BsLazyRun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsPrintfFirst BsExitDefs DvB_ExitKit DvB_ExitTmpl DvB_ExitLoop.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_DvB_ExitPre () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00c6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre4XENVC7ARocqVerifyHarness?AgentSubmission3bpB2HF>BSymExec2Sound4SX2S7regs_okc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre4kn_XC7ARocqVerifyHarness?AgentSubmission3bpB2HF>BSymExec2Sound4SX2S7know_okK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR4lzok00C6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict8restrictC45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec7seg_romC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec4mkstC6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitKit9rflat_chkc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre3xs0C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission3bpB2HF7BSymRun7vals_evK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitKit?rflat_chk_soundC6ARocqVerifyHarness?AgentSubmission3bpB2HF7BSymAux<regions_flatC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4list01C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymDrive8blobs_evC47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitKit5xs_pcC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymDrive9junk_valsC47Corelib4Init5Peano2ltI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrictEsame_but_materializedC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR8hid_sameK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX22evC45stdpp9bitvector;definitions6bv_andC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_ExitLoop7ax_loopC6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrictHsame_but_materialized_fsC6ARocqVerifyHarness?AgentSubmission3bpB3Drv9BsLazyRunCrz_msteps_lazy_mkstC6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitKit=xchain_rebaseC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg6t_exitI6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg8realizes00C47Corelib4Init3Nat3subC6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitKitCxchain_rebase_soundI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00C47Corelib4Init9Datatypes3appK7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX23env01C6ARocqVerifyHarness?AgentSubmission3bpB2HF7BSymAux6rdenotC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BFrame9frame_modC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre9x_regionsc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre3XNVC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_ExitTmpl4XNVTc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre9PRE_CLEANC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_ExitTmpl4ACUTC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_ExitTmpl5XKEPTC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_ExitTmpl4sr_TC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_ExitTmpl4kn_TI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C6ARocqVerifyHarness?AgentSubmission3bpB2HF4Bcfg=hunspell_scfgC6ARocqVerifyHarness?AgentSubmission3bpB2HF7BSymAux7sregionI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB3Drv:BsExitDefs4x_srC6ARocqVerifyHarness?AgentSubmission3bpB3Drv:BsExitDefs5AEXITK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01c6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre=pre_clean_chkc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre4xk_Uc6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre5xk_T0c6ARocqVerifyHarness?AgentSubmission3bpB3Drv;DvB_ExitPre5xk_U2".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition XNV : nat := 41.
Definition XENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

Definition ATB_LO : Z := 4096.
Definition ATB_HI : Z := 0x7fffff472000.
Definition AIMGR_LO : Z := 0x10000.
Definition AIMGR_N : Z := 0x6d8000.
Definition ASHR_LO : Z := 0x7fff7000.
Definition ASHR_N : Z := 0x10007fff8000 - 0x7fff7000.

Definition shx : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-260))) (ELit 3)) (ELit 0x7fff8000)) (ELit (-8)).
Definition SHX_LO : Z := 0x10006fdf7fd8.
Definition SHX_HI : Z := 0x10007fff8000.

Definition x_regions : list sregion :=
  [(SA (EVar 0) (-2560), 2560); (SA (ELit 0) 0x6e58a8, 32); (SA (ELit 0) 0x6e5ac8, 4); (SA (ELit 0) 0x18d9d0, 1);
   (SA (ELit 0) 0x18d980, 8); (SA (ELit 0) 0x18e8f0, 8); (SA (ELit 0) 0x6c5828, 8); (SA (ELit 0) 0x7fffa000, 0xdb000);
   (SA (ELit 0) 0x189920, 232); (SA (ELit 0) 0x189b00, 232); (SA (EVar 40) 0x1e34f8, 8); (SA (EVar 40) 0x2cf448, 8)].

Definition kn_base : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (-2560)) 2560; KRange (EVar 1) 1 2147483647;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000; KImg 0x189a08 0x189b00; KImg 0x189be8 0x18d980;
   KWord (SA (ELit 0) 0x6c57b0) 4 (EVar 1); KWord (SA (ELit 0) 0x6e5898) 8 (EVar 3);
   KWord (SA (ELit 0) 0x190888) 8 (EVar 40); KAlign (EVar 40) 4096; KRange (EVar 40) ATB_LO ATB_HI;
   KDisj (SA (EVar 40) 0x1e34f8) 96 (SA (ELit 0) AIMGR_LO) AIMGR_N; KDisj (SA (EVar 40) 0x2cf448) 96 (SA (ELit 0) AIMGR_LO) AIMGR_N;
   KDisj (SA (EVar 40) 0x1e34f8) 96 (SA (ELit 0) ASHR_LO) ASHR_N; KDisj (SA (EVar 40) 0x2cf448) 96 (SA (ELit 0) ASHR_LO) ASHR_N;
   KDisj (SA (EVar 40) 0x1e34f8) 96 (SA shx 0) 8; KDisj (SA (EVar 40) 0x2cf448) 96 (SA shx 0) 8;
   KDisj (SA (EVar 40) 0x1e34f8) 96 (SA (EVar 0) (-2560)) 2560; KDisj (SA (EVar 40) 0x2cf448) 96 (SA (EVar 0) (-2560)) 2560;
   KZero (SA (EVar 40) 0x1e34f8) (ELit 96); KZero (SA (EVar 40) 0x2cf448) (ELit 96);
   KWr (SA (EVar 40) 0x1e34f8) 8; KWr (SA (EVar 40) 0x2cf448) 8;
   KWord (SA (ELit 0) 0x800d0720) 8 (ELit 0);
   KZero (SA shx 0) (ELit 8); KRange shx SHX_LO SHX_HI;
   KWr (SA (ELit 0) 0x189920) 232; KWr (SA (ELit 0) 0x189b00) 232; KWr (SA (ELit 0) 0x18d980) 8; KWr (SA (ELit 0) 0x18d9d0) 1;
   KWr (SA (ELit 0) 0x18e8f0) 8; KWr (SA (ELit 0) 0x6c5828) 8; KWr (SA (ELit 0) 0x6e58a8) 32; KWr (SA (ELit 0) 0x6e5ac8) 4;
   KWr (SA (ELit 0) 0x7fffa000) 0xdb000].

Definition kn_c (cs : list (Z * nat * Z)) : list kentry :=
  map (fun c => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cs.

Definition xk_common : list (Z * nat * Z) := [(0x186f40, 8%nat, 0x186f40); (0x186f98, 8%nat, 0x16db90); (0x187008, 8%nat, 0x16c104); (0x187040, 8%nat, 0x16d120); (0x187140, 8%nat, 0x176aa0); (0x187148, 8%nat, 0x176ea4); (0x1891bc, 4%nat, 0x8); (0x189920, 4%nat, 0x5); (0x189978, 8%nat, 0x6e6070); (0x189980, 8%nat, 0x0); (0x1899ac, 4%nat, 0xffffffff); (0x1899b0, 4%nat, 0xffffffff); (0x189a08, 8%nat, 0x189920); (0x189a18, 8%nat, 0x0); (0x189a20, 8%nat, 0x0); (0x189a38, 8%nat, 0x0); (0x189a48, 8%nat, 0x0); (0x189a9c, 4%nat, 0xffffffff); (0x189af8, 8%nat, 0x189a10); (0x189b00, 4%nat, 0x5); (0x189b58, 8%nat, 0x6e6480); (0x189b60, 8%nat, 0x400); (0x189b8c, 4%nat, 0xffffffff); (0x189be8, 8%nat, 0x189b00); (0x18d980, 8%nat, 0x1); (0x18d9d0, 1%nat, 0x0); (0x18e850, 4%nat, 0x1); (0x18e854, 1%nat, 0x0); (0x18e8f0, 8%nat, 0x0); (0x190880, 8%nat, 0x190888); (0x19089c, 1%nat, 0x1); (0x191038, 8%nat, 0x7fff8000); (0x191d18, 1%nat, 0x1); (0x191d19, 1%nat, 0x1); (0x222be0, 8%nat, 0xffffffffffffffff); (0x222ee0, 1%nat, 0x0); (0x6c3938, 8%nat, 0x182c10); (0x6c3978, 8%nat, 0x189b00); (0x6c3980, 8%nat, 0x6c43b0); (0x6c3988, 8%nat, 0x6c3904); (0x6c3998, 8%nat, 0x182c10); (0x6c39d8, 8%nat, 0x189920); (0x6c39e0, 8%nat, 0x6c43b0); (0x6c39e8, 8%nat, 0x6c390c); (0x6c39f8, 8%nat, 0x182d40); (0x6c3a38, 8%nat, 0x189b00); (0x6c3a40, 8%nat, 0x6c4540); (0x6c3a48, 8%nat, 0x6c391c); (0x6c3a58, 8%nat, 0x182d40); (0x6c3a98, 8%nat, 0x189920); (0x6c3aa0, 8%nat, 0x6c4540); (0x6c3aa8, 8%nat, 0x6c3924); (0x6c3b88, 8%nat, 0x1827b0); (0x6c3b99, 1%nat, 0x10); (0x6c3bb0, 4%nat, 0x0); (0x6c3bb8, 8%nat, 0x6c3938); (0x6c3c18, 8%nat, 0x0); (0x6c3c28, 8%nat, 0x1828d0); (0x6c3c39, 1%nat, 0x10); (0x6c3c50, 4%nat, 0x0); (0x6c3c58, 8%nat, 0x6c39f8); (0x6c3cb8, 8%nat, 0x0); (0x6c3e08, 8%nat, 0x1827b0); (0x6c3e19, 1%nat, 0x10); (0x6c3e30, 4%nat, 0x0); (0x6c3e38, 8%nat, 0x6c3998); (0x6c3e98, 8%nat, 0x0); (0x6c3ea8, 8%nat, 0x1828d0); (0x6c3eb9, 1%nat, 0x10); (0x6c3ed0, 4%nat, 0x0); (0x6c3ed8, 8%nat, 0x6c3a58); (0x6c3f38, 8%nat, 0x0); (0x6c43b0, 8%nat, 0x183288); (0x6c4540, 8%nat, 0x182fd8); (0x6c4550, 8%nat, 0x6a768); (0x6c5828, 8%nat, 0x6e5b20); (0x6e58ac, 4%nat, 0x0); (0x6e58b8, 8%nat, 0x6e58c0); (0x6e58c0, 8%nat, 0x0); (0x6e58c8, 8%nat, 0x165424); (0x6e58d0, 8%nat, 0x126ca0); (0x6e58d8, 8%nat, 0xae38c); (0x6e59c8, 8%nat, 0xd7e54); (0x6e59d0, 8%nat, 0x6c38f8); (0x6e59d8, 8%nat, 0x0); (0x6e5ac8, 4%nat, 0x0); (0x6e5aeb, 1%nat, 0x0); (0x6e6060, 8%nat, 0x0)]%Z.
Definition xk_U : list (Z * nat * Z) := [(0x6e58b0, 4%nat, 0x3); (0x189940, 8%nat, 0x0); (0x1899a8, 4%nat, 0xffffffff); (0x189b20, 8%nat, 0x0); (0x189b88, 4%nat, 0x0); (0x189b90, 4%nat, 0xa)]%Z.
Definition xk_U2 : list (Z * nat * Z) := [(0x6e58b0, 4%nat, 0x3); (0x189928, 8%nat, 0x0); (0x189930, 8%nat, 0x0); (0x189940, 8%nat, 0x6e6070); (0x189948, 8%nat, 0x6e6070); (0x189958, 8%nat, 0x6e6070); (0x1899a8, 4%nat, 0xffffffff); (0x189b20, 8%nat, 0x0); (0x189b88, 4%nat, 0x0); (0x189b90, 4%nat, 0xa)]%Z.
Definition xk_T0 : list (Z * nat * Z) := [(0x6c3694, 1%nat, 0x0); (0x6e58b0, 4%nat, 0x4); (0x6e58e0, 8%nat, 0x165424); (0x6e59e0, 8%nat, 0xe881c); (0x189940, 8%nat, 0x0); (0x1899a8, 4%nat, 0x0); (0x189b08, 8%nat, 0x0); (0x189b10, 8%nat, 0x0); (0x189b20, 8%nat, 0x6e6880); (0x189b28, 8%nat, 0x6e6480); (0x189b38, 8%nat, 0x6e6480); (0x189b88, 4%nat, 0xffffffff); (0x189b90, 4%nat, 0xffffffff)]%Z.
Definition xk_T (j : Z) : list (Z * nat * Z) := [(0x6c3694, 1%nat, 0x0); (0x6e58b0, 4%nat, 0x4); (0x6e58e0, 8%nat, 0x165424); (0x6e59e0, 8%nat, 0xe881c); (0x189940, 8%nat, 0x0); (0x1899a8, 4%nat, 0x0); (0x189b08, 8%nat, 0x0); (0x189b10, 8%nat, 0x0); (0x189b20, 8%nat, 0x6e6880); (0x189b28, 8%nat, (0x6e6480 + 2 * j)); (0x189b38, 8%nat, 0x6e6480); (0x189b48, 8%nat, 0x16cdd0); (0x189b78, 4%nat, 0x1); (0x189b88, 4%nat, 0xffffffff); (0x189b90, 4%nat, 0xffffffff)]%Z.

Definition kn_X (xk : list (Z * nat * Z)) : list kentry := kn_base ++ kn_c xk_common ++ kn_c xk.

Definition xs0 (xk : list (Z * nat * Z)) : xst := XS AEXIT x_sr (kn_X xk).

Definition XR (dirs : list bool) : xseg := XRun 40000%N [0x16cdd0] dirs (fun _ => true).
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
ltac2:(KReplay.run1 (kr_t_DvB_ExitPre ()) ["Clean"] "p'0h01nh11Hh22M'h32R'h42CXh52_Hh62AGh72CFh83CHKh92HKh:3HK'h;2HLh<3HL0h=2HRh>3HR'h?3Hmsh@1LhA1MhB2OKhC3OK'hD1RhE2RFhF2RShG3RS'hH1ShI2SBhJ2ZrhK7__arithhL4__ffhM8__varmaphN5__withO1bhP4cstrhQ5cstr0hR1ehS1fhT2mohU3mo'hV3msFhW4msF'hX4valshY1xi001xhZ1yp&0p;1p;2p;3p;4p;5p;7p;6p;<p;=p;Cp;:p;Eg0000R0p4p70g000^R1p4p710p8g001:j1?Tg001_j1\Tg002=j1iTg002`j1LTg003@j1;Tg003ek20KTg004Qk10ITg0053j2hTg005Sj21Tg0063j39j1]Tg006Mj1RTg007Jj3_Tg008Qj1vTg009Nj4[Tg00:Uj2XTg00;Jj5sTg00<Cj3rTg00=Dj2HTg00=jk10JTg00>gj54Tg00?ak20HTg00@ck10ETg00A_k30@Tg00BBR2j2GTg00B]j20j1ETg00CXj1STg00D6j17Tg00Dij7}Tg00F1j2zTg00G1j6jTg00GOj1^Tg00Goj1wTg00Hmj3NTg00ILj3tTg00Ink10LTg00Jlj16Tg00KkR3j22Tg00LCR4j2QTg00L]k20FTg00Mkk40DTg00Nfj13Tg00OER5k20ATg00Oaj2ITg00P;R6j1KTg00P[k20=Tg00Q>k30<Tg00Q[l<`Tg00R@k40:Tg00Rgj1eTg00SLj2dTg00Shk109Tg00TFk108Tg00Tdk107Tg00UOj2bTg00V2k405Tg00V]k704Tg00WAk202Tg00Wck201Tg00XOk303Tg00Xnk400Tg00Y`k406Tg00ZKj2aTg00[Gj3UTg00[ll=|TP1j6fTg00\mj3{Tg00^>mC0>Tg00_Hl:gTg00`Nj2ZTg00aJj4mTg00bJj2OTg00balEyTg00cmj3xTg00dij3>Tg00eFj2JTg00fEj1kTg00g?j4qTg00g[j3pTg00hWR1g00j5R7g00k7R8g00l3R9g00m1R:f0R;g00n3R<g00o1R=g0100R>g010nR?M:gp>0Bg011lR@g012LRA79;p=F%3;#3p=cP1g012lRBf5RCf4RD'Xf3REf2RFf1RG3U/Z;Cmp==P1P7PGP9P:P;P<P=P>P?M:gp=o11G;,O9p=uP;P1P7P9P:PGP<P=P>P?PFPEPDPCf6R=f7R:f8RHf9RIf:RJf;RKf<RLMEyp>0MAx1G;p=D11G;,O99NEFp=CA>EFG9>CD#E/J;p=YA_G>;p=<1O9;9NFGp=5A>DEF9>=C/0G=9:;p=:g013jR>PE%EF/JG#kP7Cq9pCD/G;p=8P1PFPGP?C[/G;p=B1GG;,GFp=A%6G9>EF9>CD#E/J;p=@1O9G9NEF=>D;9>=Cp=W10EF10G;59Dp=V%EG/J;p=TP1PGP;P?C[p=P1JG;#kp=nP>PGP;P7Cq9pEFp=l10EF=UDG/Z;p>0G%3;#3#3#3p>0C%3;#3#3#3#3#3#3#3p=Mg014eR>g015DR?P3P6P5g015bPCPDPEPFPGP;M<`p>0?10G;99EFp=~P1PBPF1ZG;Cmp>0;g016DRB#?R5#?#?R3#?#?#?#\R9#iRM#L%;5RN#\00KMRO%\3#iR3$0I\MRPg016iRQg0180RR1hMM#LRS11M:=9>8%RHg018f;_:P1%RIP:p,2xkRT#vRUC[P1PCPDPE1X:=RVDsAr=CHp,2fxRWPJg019b,H9RXPI&0J1RYD459Q20HU7RZ&0ETRT$0BR[p,3CHK40@%FZRZ%F[R['GP2PZP[PKPJP9f>R\g01:_#cR]'0%;B#;#;#;#;#;#;#S,H9RB%7JE=P;P1fAR^#RR_f?R`PUP7P:PGF}1z_7P>P81o;T#FX0>PGfBR_,1MR7PJEj1o7T#FPWPTfCR7%L3#^#wR3P_P^PYg01;>RU,H9Ra1uM7Rb5NMP;AtMabPGPJPIN=0MPWfDRb&0LT,H9RTP7PYD4PWPG1H9<R<P;PYD4Rc'DPMfERdPMPMPaPMPdCC%6GReP3EYRf/<GP7P;1hM?RgPdP3fFRh,1MRi,2;PMPMfGRjPM11MjRk95Ma%6ERlPG10jGG:[^0>E89Bf;3AX2P,QPX3O,QOP4POPWPdPTPbPYD4/DcPMPhPMA5MaiPeP3EYRi/<GPbP;PgPhP312;kPMPMfHRkPMPMPaPMPkCCRbPlPG10kGG:[^0>E89Bi;3AX2P,QPX3OP_P^P910d]PB%7^E=P;PWPjPTPhPYD4/DcPMPkPMPbPeP3EYRe/<GPhP;PgPkP3fIRb,1MRc,2;PMPMfJRiPM11MiRf95MaPlPG10iGG:[^0>E89Be;3AX2P,QPP4PPPWPkPTPjPYD4PWPFP<P;PYD4'DPMPbPMA5MacPFP3E@Rc/<FPjP;PgPbP312;fPMPMfKRfPMPMPa11Mf%6DFWRjPGPfPGDV[^0>E89Bc;3AX2PPhPdP910b]PB%7dE=P;PWPiPTPbPYD4PWPDP<P;PYD4'D1Tj3Rj/<DPbP;PgPfP3fLRc,1MR4,2;PMPMfMRePM11MeRl95Ma%6=PG10eGG:[^0>E89Bj;3AP2PWPfPTPiPYD4PWPCP<PGPYD4'DPMPcPMA5Ma4PCP3E@R4/<C1P4GPiPGPgPcP312;lPMPMfNRlPMPMPaPMPlCC%6:PG10lGG:[^0>E83APiPbP910e]PB%7bE=P;PWPePTPcPYD4PWP:P<PEPYD4'DPMfOR:PMPMPaPMP:CCPHP3E@RT/<H1PTDPePDPgP:P3fPR:,1MRT,2;PMPMfQRbPM11MbR495Ma%6JPG10bGG:[^0>E83AP2PMP:PMA5MaTPIP3E@RT/<IPlPCPgP:P312;4PMPMfRR4PMPMPa11M4%6KFWRJPGP4PGDV[^0>E89BTCPlPeP910b]PB%7eE=P;1TJ3/<KPMfSRJPMPMPaPMPJCCPLP3E@PbPHPgPJP3fTRJ,1MRe,2;PMPMfURlPM11MlRT95Ma%6\PG10lGG:[^0>E87BHP2PMPJPMA5Maef=ReP3E@/PIP4PIPgPJP312;TPMPMfVRTPMPMPa11MT%6`FWRJPGPTPGDV[^0>E8P4PbP910l]PB%7bE=P;1TJ3/PKPlPLPgfWRKP3fXRJ,1M,2;PMPMfYR4PM11M4RI95Ma%6_PG104GG:[^0>E8P2PTPePg%EJ/n3Cl12;IPMPMfZRIPMPMPaPMPICC%67PG10IGG:[^0>PTPlP9104]PB%7lE=P;PJP`Pg%EI/n3Clf\Rg,1M,2;PMPMf]R`PMPMPaPMP`CC%6hPG10`GG:[^0>PWP1PKPTPlP4f[RlPXPIPYPdP<P^PJP9PgP]PB%7JI0GPbP:PeP1P4PJPK1XG;Ds20FlGPlPIP`PEH0DArglDPWPiP<PhPYD459QP0%7DP=PCP9fcRY/0]RhPBP;E=XS0P=P]P>P812];X0>%3]#c$0C#M#M#M#MR0,2]%S5R5%?N#?#;#SRN+0AR<P]P51I?5P0PN1I?NJ0?fbR0,1MRi=9>8%KiRl%K8RE59?RKP>P?%]>P6%]?%KG%K;59?A9>G;20=G;40<XZ>XY>PiPl1I?lP8PE1I?EM<`PIH0:PK11MYRK#e%KK,dU%e81dUEg01;\RE#^%LE&09?&08?&07?REg01<Hg01<gRlPlg01=GRlP?1b?5g01=g1b?NH05g01>NK04202ElP;PF1I@A201;F#FdB03?UGH00bLbMbNP<P;bKbQbPb<H0612]8ePiPIEjO2PMPMP0PMA5MaiPfP3E@/a]P0P]C~R0eP0PMPMPYPMA5MaKPcP3E@R3/a]AU9;B%7=60;VXOMPWP3PcPkP=PCf^RCP`Pgf@PLPDPGM=|PhP;Efb1%7CA{CDFEfWGW5WIWCXURXWQNC0>W6W5PGP;O2n2001000000121000000W1W:PGP;O2n2001000000121000000W1W>PGP;O2n2011000000121000000W1W?PGP;O2n2011000000121000000W1X2PPGP;O2n2011000000121100000W1X3OPGP;O2n2011000000121100000bRb4bEX4[X7ZPGP;O2n2001000000121000000b8WFWBW9W=W;XJSXHSW@WTWVWAWDWXo"). Qed.
End Clean.

Lemma pre_U_ok : pre_clean_chk xk_U = true.
Proof.
ltac2:(KReplay.run1 (kr_t_DvB_ExitPre ()) [] "p;2p;1p;3g00Oaj22Tg01>nj11Tg0063j30Tg011lR0g012LR1'2g01@4#1=001do"). Qed.
Lemma pre_T0_ok : pre_clean_chk xk_T0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_DvB_ExitPre ()) [] "p;2p;1p;3g00Oaj22Tg01>nj11Tg0063j30Tg011lR0g012LR1'2g01A1#1=001do"). Qed.
Lemma pre_U2_ok : pre_clean_chk xk_U2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_DvB_ExitPre ()) [] "p;2p;1p;3g00Oaj22Tg01>nj11Tg0063j30Tg011lR0g012LR1'2g01Ao#1=001do"). Qed.
