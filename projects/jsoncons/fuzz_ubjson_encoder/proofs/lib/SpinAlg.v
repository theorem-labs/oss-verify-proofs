(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the place_declined_b premise of the mmap decline; the vDSO; the read-only-backing form of the system-call steps; the model's access_ok checks; imports; new lemmas; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/SpinAlg.v, 187 lines within its lines 14-478. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec FPSteps FrmKeepC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SpinAlg () := "C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7set_regI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_tailI47Corelib4Init5Logic2or00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8FrmKeepC4FRMC=word_frm_safeC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K47Corelib4Init9Datatypes4list01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C4ELinuxProcessSemantics?LinuxProcessSem3RunHmi_account_step_projectsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8FrmKeepC4FRMC7step_fzC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPSteps8frm_zeroC13~~~K47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:fz_set_regC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event03C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8frm_safeC13~~~I47Corelib4Init5Logic3and00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes001C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_altC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7node_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgCis_prefix_app_splitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg?is_prefix_nil_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8wr_indexC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes01C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9frm_guardC13~~~i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes000C13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg<sstep_cfg_fzC13~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic5proj2C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_nilC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes002C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSimBis_prefix_app_monoC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSim7to_spin00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5bm_onC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes003C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4t_eqC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes004C13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAbudget_refused_atk79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes005C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg<realizes_indC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSim8spinningC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_nodeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_haltC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srz_conseqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_spinC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg>srealizes0_indC13~~~C47Corelib4Init5Logic5proj1C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_alt_unitC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgBsrealizes_nonemptyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg=t_emit_nil_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_eq_transC13~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3sum01K47Corelib4Init9Datatypes3sum02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_alt2C13~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic3iffC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:node_instrC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg;srz_silent1C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_stepC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim:msteps_indC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LazyFrameEaccesses_outside_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LazyFrameHmi_account_step_disjointC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C47Corelib4Init5Logic6eq_symC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgFnode_ok_of_pnode_instrC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgCnode_instr_disjointC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:rz_silent1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim7fd1chanC13~~~C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim;buf_modeledC13~~~I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init6Specif9proj1_sigC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7wr_fullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg;node_write1C13~~~K47Corelib4Init6Specif3sig01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_write_chC13~~~C47Corelib4Init9Datatypes6lengthI47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00I47Corelib4Init6Specif3sig00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ExitSim:is_exit_noC13~~~C45stdpp9bitvector;definitions6bv_andC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7rz_exitC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgEsrealizes_of_realizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim>munmap_args_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim:munmap_effC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim=page_round_upC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim<munmap_modelC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg;node_munmapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim<mmap_args_okC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim:mmap_modelC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg>mmap_grant_effC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg9node_mmapC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srz_cases1C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim8grant_okC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgAnode_mmap_nograntC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4ScfgCstar_cfg_halted_nilC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_subC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSim=spin_star_nilC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg<star_cfg_oneC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4ScfgAobs_trace_cfg_nilC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgCsrealizes_star_onlyC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgAsrealizes_pclosedC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg@srealizes_admitsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgAsstep_halted_noneC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSimDspinning_silent_loopC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=sstep_cfg_subC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSimAsilent_loop_sstepC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg=srz0_spinningC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSimCspin_no_sstep_errorC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_pathC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg>srealizes_stepC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg=srz_path_starC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgDsrealizes_no_sserrorC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunJreaches_budget_refused_cfgK4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgFsrealizes0_bm_transferC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgAsrealizes0_of_offC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srz_mstepsC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7MmapSim?mmap_model_lazyC13~~~".
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Common.Cfg Require RomBase RomWrite.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Context {bmK : BMode}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Inductive srealizes0 : config -> TSet -> Prop :=
| srz0_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs scfg c I evs nx ->
    RomBase.sys_rob segs c ->   (* [comment removed for export] *)
    (forall i, srealizes0 (nx i) (T i)) ->
    srealizes0 c (t_alt (fun i => t_emit (evs i) (T i)))
| srz0_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes0 c t_nil
| srz0_spin : forall c,
    to_spin segs (cfg_ms c) (cfg_model c) ->
    m_halted (cfg_model c) = None ->
    bm_on = false ->
    srealizes0 c t_nil
| srz0_conseq : forall c T T',
    srealizes0 c T -> t_eq T T' -> srealizes0 c T'
| srz0_brefused : forall c T,
    bm_on = true -> budget_refused_at segs c ->
    RomBase.sys_rob segs c ->   (* [comment removed for export] *)
    T [] -> srealizes0 c T.

Definition frm_safe : Prop :=
  (forall seg, In seg segs -> seg_executable seg && seg_writable seg = false)
  /\ (forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> FRMC.word_frm_safe w = true).
Definition frm_guard (c : config) : Prop := frm_safe /\ frm_zero (ms_fcsr (cfg_ms c)).
Definition srealizes (c : config) (T : TSet) : Prop := T [] /\ (frm_guard c -> srealizes0 c T).

Lemma fz_set_reg ms r v : ms_fcsr (set_reg ms r v) = ms_fcsr ms.
Proof. unfold set_reg. destruct (bv_eqb r 0); reflexivity. Qed.
(* At 08b1429 [sstep_cfg] has a vDSO-call arm whose successor is [vdso_post]: it writes
   integer registers, the frame and the pc, and leaves the floating-point CSR alone. *)
Lemma fz_vdso_write_regs : forall rs vs ms, ms_fcsr (vdso_write_regs ms rs vs) = ms_fcsr ms.
Proof.
  induction rs as [|r rs IH]; intros [|v vs] ms; cbn [vdso_write_regs]; try reflexivity.
  rewrite IH. apply fz_set_reg.
Qed.
Lemma fz_vdso_post : forall ms model f eff, ms_fcsr (vdso_post segs ms model f eff) = ms_fcsr ms.
Proof.
  intros ms model f eff. unfold vdso_post, vdso_set_pc, vdso_with_mem, apply_effect. cbn [ms_fcsr].
  rewrite fz_set_reg. cbn [ms_fcsr]. apply fz_vdso_write_regs.
Qed.
Lemma sstep_cfg_fz : forall c e c', frm_safe -> sstep_cfg segs scfg c e (SNext c') ->
  frm_zero (ms_fcsr (cfg_ms c)) -> frm_zero (ms_fcsr (cfg_ms c')).
Proof.
  intros c e c' [NWX FS] H. inversion H; subst; cbn [cfg_ms]; intros Z.
  - match goal with A : mi_account_step _ _ _ = MachineOk _ |- _ => apply mi_account_step_projects in A; exact (FRMC.step_fz segs NWX FS _ _ A Z) end.
  - rewrite fz_vdso_post. exact Z.
  - unfold advance_past_svc, apply_effect. cbn [ms_fcsr]. rewrite fz_set_reg. exact Z.
  - exact Z.
  - exact Z.
Qed.

Lemma srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
    node_ok segs scfg c I evs nx -> RomBase.sys_rob segs c -> (forall i, srealizes (nx i) (T i)) -> srealizes c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hnode Hrob Hk. split; [exists i0; left; apply is_prefix_nil|].
  intros [S Z]. apply (srz0_node c I evs nx T i0 Hnode Hrob). intros i. apply (proj2 (Hk i)). split; [exact S|].
  destruct Hnode as [Hc _]. exact (sstep_cfg_fz c (evs i) (nx i) S (Hc i) Z).
Qed.
Lemma srz_halt : forall c, m_halted (cfg_model c) <> None -> srealizes c t_nil.
Proof. intros c H. split; [reflexivity| intros _; exact (srz0_halt c H)]. Qed.
Lemma srz_spin : forall c, to_spin segs (cfg_ms c) (cfg_model c) -> m_halted (cfg_model c) = None -> bm_on = false -> srealizes c t_nil.
Proof. intros c H1 H2 H3. split; [reflexivity| intros _; exact (srz0_spin c H1 H2 H3)]. Qed.
Lemma srz_conseq : forall c T T', srealizes c T -> t_eq T T' -> srealizes c T'.
Proof. intros c T T' [NE H] Heq. split; [apply Heq; exact NE| intros G; exact (srz0_conseq c T T' (H G) Heq)]. Qed.
Lemma srz_brefused : forall c T, bm_on = true -> budget_refused_at segs c -> RomBase.sys_rob segs c -> T [] -> srealizes c T.
Proof. intros c T H1 H2 Hr H3. split; [exact H3| intros _; exact (srz0_brefused c T H1 H2 Hr H3)]. Qed.

Lemma srealizes0_of_realizes : forall c T, realizes segs scfg c T -> srealizes0 c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz0_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz0_halt c Hh).
  - exact (srz0_conseq c T T' IH Heq).
Qed.
Lemma srz0_spinning : bm_on = false -> forall c, spinning segs c -> srealizes0 c t_nil.
Proof. intros BOFF c [Hspin Hh]. exact (srz0_spin c Hspin Hh BOFF). Qed.
Lemma srz_fz : forall c T, T [] -> (frm_zero (ms_fcsr (cfg_ms c)) -> srealizes c T) -> srealizes c T.
Proof. intros c T NE H. split; [exact NE|]. intros G. exact (proj2 (H (proj2 G)) G). Qed.
Lemma srealizes0_of : forall c T, frm_guard c -> srealizes c T -> srealizes0 c T.
Proof. intros c T G [_ H]. exact (H G). Qed.
Lemma srealizes_of0 : forall c T, T [] -> srealizes0 c T -> srealizes c T.
Proof. intros c T NE H. split; [exact NE| intros _; exact H]. Qed.

Lemma srealizes_of_realizes : forall c T,
  realizes segs scfg c T -> srealizes c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

Lemma srz_spinning : bm_on = false -> forall c, spinning segs c -> srealizes c t_nil.
Proof. intros BOFF c [Hspin Hh]. exact (srz_spin c Hspin Hh BOFF). Qed.

Lemma srealizes0_nonempty : forall c T, srealizes0 c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
  - exact HT0.
Qed.
Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof. intros c T H. exact (proj1 H). Qed.

Lemma srz_silent1 : forall c c' T,
  node_ok segs scfg c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

Lemma srz_emit1 : forall c c' e T,
  node_ok segs scfg c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs scfg c (IA + IB) (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode Hrob).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

Lemma srz_cases1 : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs scfg c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob Hc.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (Hc i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Ht).
Qed.

Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

Lemma node_instr_disjoint : forall ms model ms' ranges,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' ranges Hh Hsvc Hstep Hout.
  pose proof (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
    as Hacc.
  apply node_ok_of_pnode_instr; [exact Hsvc|].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model); assumption.
  - intros e st Hss.
    inversion Hss; subst; try congruence.
    match goal with
    | H : mi_account_step _ _ _ = MachineOk _ |- _ =>
        rewrite Hacc in H; injection H; intros; subst
    end.
    exists tt. split; reflexivity.
Qed.

Lemma rz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  realizes segs scfg (mkCfg ms' model) T ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply rz_silent1; [eapply node_instr_disjoint; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply srz_silent1; [eapply node_instr_disjoint; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [ShapeAlg.node_write1] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 segs scfg ms model x8 buf); assumption.
  - eapply RomWrite.write1_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma srz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs scfg ms model x8); assumption.
Qed.

Lemma srz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs scfg c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (HT i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Lemma srz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sc_alloc scfg = false ->
  srealizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Halloc Hc.
  eapply srz_silent1; [apply (node_munmap segs scfg ms model x8); assumption | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_215)) | exact Hc].
Qed.

Lemma srz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sc_alloc scfg = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hdecl Halloc HB Hex.
  destruct Hex as [a0 Ha0].
  apply (srz_cases1 (mkCfg ms model) _ _ B (exist _ a0 Ha0)
           (node_mmap segs scfg ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Halloc (ex_intro _ a0 Ha0))
           (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))).
  intros [a Ha]. cbn [proj1_sig]. apply HB. exact Ha.
Qed.

Lemma srz_mmap_nogrant : forall ms model x8 A,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  srealizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model) A ->
  srealizes (mkCfg ms model) A.
Proof.
  intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hdecl Hnone HA.
  eapply srz_silent1; [apply (node_mmap_nogrant segs scfg ms model x8); assumption | exact (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222)) | exact HA].
Qed.

End WithSegs.

Section WithSegsOff.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Local Notation srealizes := (@srealizes0 bm_off_inst segs scfg).

Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
  - discriminate Hon.
Qed.

Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star_cfg segs scfg c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs scfg c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_star_nil segs ms model tr c' Hspin Hh (star_cfg_sub _ _ _ _ _ Hstar)).
  - apply Heq. eapply IH; exact Hstar.
  - discriminate Hon.
Qed.

Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace_cfg segs scfg c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
  - discriminate Hon.
Qed.

Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace_cfg segs scfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

Lemma srealizes_step : forall c T e c',
  srealizes c T -> sstep_cfg segs scfg c e (SNext c') -> exists T', srealizes c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct (silent_loop_sstep segs (spinning segs) c e (SNext c')
                (spinning_silent_loop segs) (conj Hspin Hh) (sstep_cfg_sub _ _ _ _ _ Hss))
      as (_ & c'' & Heq2 & Hsp').
    injection Heq2 as ->.
    exists t_nil. exact (@srz0_spinning bm_off_inst segs scfg eq_refl _ Hsp').
  - eapply IH; exact Hss.
  - discriminate Hon.
Qed.

Lemma srealizes_no_sserror : forall c T e,
  srealizes c T -> ~ sstep_cfg segs scfg c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_no_sstep_error segs ms model Hspin Hh e (sstep_cfg_sub _ _ _ _ _ Hss)).
  - eapply IH; exact Hss.
  - discriminate Hon.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizes c T.

Lemma srz_path_star : forall c tr c',
  srz_path c -> star_cfg segs scfg c tr c' -> srz_path c'.
Proof.
  intros c tr c' Hp Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH].
  - exact Hp.
  - apply IH. destruct Hp as [T HT].
    destruct (srealizes_step c1 T evs c2 HT Hss) as [T' HT']. exists T'. exact HT'.
Qed.

Theorem srealizes_no_error : forall c T,
  srealizes c T -> ~ reaches_error_cfg segs scfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  assert (Hp : srz_path c') by (eapply srz_path_star; [exists T; exact H | exact Hstar]).
  destruct Hp as [T' HT']. exact (srealizes_no_sserror c' T' evs HT' Herr).
Qed.

End WithSegsOff.

Section BmTransfer.
Context {bmK : BMode}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma srealizes0_bm_transfer : forall c T,
  @srealizes0 bmK segs scfg c T ->
  ~ reaches_budget_refused_cfg segs scfg c ->
  @srealizes0 bm_off_inst segs scfg c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros Hnr.
  - apply (@srz0_node bm_off_inst segs scfg c I evs nx T i0 Hnode Hrob).
    intros i. apply IH. intros (tr & c' & Hstar & Hb). apply Hnr.
    exists (evs i ++ tr), c'. split; [| exact Hb].
    destruct Hnode as [Hcomp _]. eapply star_cfg_step; [apply Hcomp | exact Hstar].
  - exact (@srz0_halt bm_off_inst segs scfg c Hh).
  - exact (@srz0_spin bm_off_inst segs scfg c Hspin Hh eq_refl).
  - exact (@srz0_conseq bm_off_inst segs scfg c T T' (IH Hnr) Heq).
  - exfalso. apply Hnr. exists [], c. split; [apply star_cfg_refl | exact Hbr].
Qed.

Lemma srealizes0_of_off : forall c T,
  @srealizes0 bm_off_inst segs scfg c T -> bm_on = false -> @srealizes0 bmK segs scfg c T.
Proof.
  intros c T H BOFF;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c Hspin Hh Hboff | c T T' H IH Heq | c T Hon Hbr Hbrob HT0].
  - exact (srz0_node segs scfg c I evs nx T i0 Hnode Hrob IH).
  - exact (srz0_halt segs scfg c Hh).
  - exact (srz0_spin segs scfg c Hspin Hh BOFF).
  - exact (srz0_conseq segs scfg c T T' IH Heq).
  - discriminate Hon.
Qed.

Lemma srealizes_bm_transfer : forall c T,
  @srealizes bmK segs scfg c T ->
  ~ reaches_budget_refused_cfg segs scfg c ->
  @srealizes bm_off_inst segs scfg c T.
Proof. intros c T [NE H] Hnr. split; [exact NE|]. intros G. exact (srealizes0_bm_transfer c T (H G) Hnr). Qed.
Lemma srealizes_of_off : forall c T,
  @srealizes bm_off_inst segs scfg c T -> bm_on = false -> @srealizes bmK segs scfg c T.
Proof. intros c T [NE H] BOFF. split; [exact NE|]. intros G. exact (srealizes0_of_off c T (H G) BOFF). Qed.

End BmTransfer.

Ltac chain_mst_sp :=
  first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
        | chain_mst ].

Lemma chain_mst_srealizes : forall segs scfg ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes segs scfg (mkCfg ms' model) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros segs scfg ms ms' model T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.

Lemma chain_mst_srealizes_mmap : forall segs scfg ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes segs scfg (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  srealizes segs scfg (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
  intros segs scfg ms ms' model a n T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.
