(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed ref_exit, ref_exit_Z, ref_exit_clean and 2 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Src0Exit.v, lines 40-66, 80-136, 146-147, 155-159, 168-169. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0Exit_run1. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.LibWritev OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0Exit_run1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Exit_run2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Exit_run3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite_run1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite_run2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r1ff24_20000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4d000_4e000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Ns0Exit () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses3injI46Stdlib9micromega7EnvRing5PExpr00I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega7EnvRing5PExpr07I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK46Stdlib9micromega7EnvRing5PExpr01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:RdnPeelKit7wchainZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058;Ns0ExitBase:file_cleanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib7Mh_0055:RdnPeelKit6wch_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib<Ns0Exit_run1<atexit_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_0058;Ns0ExitBase=stdio_globalsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<Ns0Exit_run16mem_w1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<Ns0Exit_run12w1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<Ns0Exit_run16mem_w2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0Exit_run27mem_w3aC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic3and01C49OSSVerify5KrLib<Ns0Exit_run12w2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0Exit_run23w3aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_00948RefNodes:rz_exit_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_mstepsC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula06C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:RdnPeelKit?rdn_wchainZ_outC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib<Ns0Exit_run13axv00C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib<Ns0Exit_run13axv01C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib<Ns0Exit_run13axv02C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib<Ns0Exit_run13axv03C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib<Ns0Exit_run13axv04C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib<Ns0Exit_run13axv05C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib<Ns0Exit_run13axv06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8fa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8fa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007E_a8fa4C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega:ZMicromega=Zeval_formulaC59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs9ssp_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib7Mh_0058<Ns0Exit_run34w3b1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init9Datatypes3appK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_file01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03C59OSSVerify5KrLib7Mh_00368ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs;sw_post_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058<Ns0Exit_run34w3b2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite?ref_stdio_writeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rK46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~".
Ltac2 kr_t_Ns0Exit () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixI47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_00368ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs8exit_preC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib7Mh_0058;Ns0ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsc49OSSVerify5KrLib7Ns0Exit>ref_exit_cleanC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib7Ns0Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsc49OSSVerify5KrLib7Ns0Exit>ref_exit_flushC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01c49OSSVerify5KrLib7Ns0Exit8ref_exitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI47Corelib7Numbers7BinNums1N00".
(* [comment removed for export] *)
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
  | |- _ => rdn_hyp
  end.
Local Ltac rdn_solve ::= rdn_solve_fast.

Ltac zaddr_rec H := zaddr H.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xc6cc0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa92d0 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC as [ec_sp ec_tp ec_a0 ec_splo ec_sphi ec_sok ec_tplo ec_tphi ec_tid ec_mtid ec_lock ec_fe ec_fs ec_fa ec_comp ec_g1 ec_dso ec_ax ec_cb ec_g2 ec_glob ec_err].
  destruct ec_ax as [ax AX].
  (* [comment removed for export] *)
  destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1, ax_writes; destruct ax; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve. }
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_a8fa4 | exact E_a8fa4 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa92d0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrdr.
  destruct EC as [ec_sp ec_tp ec_a0 ec_splo ec_sphi ec_sok ec_tplo ec_tphi ec_tid ec_mtid ec_lock ec_fe ec_fs ec_fa ec_comp ec_g1 ec_dso ec_ax ec_cb ec_g2 ec_glob ec_err].
  destruct ec_ax as [ax AX]. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1, ax_writes; destruct ax; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve. }
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0xaea24) with (0xaea24 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write scfg regs3 mem3 model (bv_unsigned sp - 32) 0xc6cc0 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0xaea24 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; rdn_solve
    | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_a8fa4 | exact E_a8fa4 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

#[using="Type"] Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa92d0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
  - eapply srz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  srealizes RSEGS scfg (mkCfg (mkst regs (Z_to_bv 64 0xa92d0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0xa92d0) with (0xa92d0 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
