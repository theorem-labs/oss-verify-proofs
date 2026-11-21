(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (20 recorded proofs replaced by written proofs (is_prefix_app_r, is_prefix_app_split, is_prefix_nil_r and 17 more); node_write1, rz_write1, node_write_ch and 1 more restated for the revision's model; rz_munmap, cat_realizes, exitline_realizes_aux and 3 more re-proved; adds rz_silent_all; rz_node takes RomBase.sys_rob, so rz_silent1, rz_silent_all, rz_emit1 and rz_alt2 take it too, discharged at the instruction, write (RomWrite.write1_rob, write_ch_rob), exit and munmap nodes; imports RomBase, RomWrite). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim CatSim MmapSim AllocSim WallSim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RomBase RomWrite.
Ltac2 kr_t_ShapeAlg () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List:fold_rightC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init6Specif9proj1_sigC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic3iffC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib2AS8ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg?is_prefix_nil_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib2AS8ShapeAlg=t_writes_pickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:t_write_chC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics?LinuxProcessSem5State5event02c59OSSVerify5KrLib2AS8ShapeAlg8t_writesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg;t_writes_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib2AS8ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib2AS6CatSim:wevents_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib2AS8ShapeAlg@t_writes_ch_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim7weventsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib2AS8ShapeAlgDt_writes_ch_exit_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib2AS7WallSim>wevents_ch_fd1C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes6lengthK47Corelib4Init6Specif3sig01C47Corelib5Lists7ListDef5skipnC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List7map_appc59OSSVerify5KrLib2AS8ShapeAlg7wr_fullC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC56Stdlib5Arith8PeanoNat3Nat7le_reflC46Stdlib5Lists4List9skipn_allI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init6Specif3sig00C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveI47Corelib5Lists7ListDef6Forall00I59OSSVerify5KrLib2AS6CatSim5wpick00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim5wpick01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim=wpick_weventsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim5wpick02C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indc59OSSVerify5KrLib2AS8ShapeAlgIt_writes_ch_pick_exit_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg8pnode_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg?cfg_transparentC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C59OSSVerify5KrLib3Lib3Cfg<sstep_of_cfgC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib3Cfg@alloc_no_b_falseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgDtransparent_nonallocC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem3RunAalloc_mark_sysnosI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02k59OSSVerify5KrLib2AS8ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib2AS8ShapeAlg<realizes_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgCstar_cfg_halted_nilC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00C59OSSVerify5KrLib3Lib3Cfg<star_cfg_oneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C59OSSVerify5KrLib3Lib3CfgAobs_trace_cfg_nilC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgc59OSSVerify5KrLib2AS8ShapeAlgBrealizes_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@realizes_pclosedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg?realizes_admitsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C59OSSVerify5KrLib3Lib3CfgEsstep_cfg_halted_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7rz_pathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=realizes_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgc59OSSVerify5KrLib2AS8ShapeAlg<rz_path_starC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgCrealizes_no_sserrorC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib2AS8ShapeAlg:t_alt_unitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3sum01K47Corelib4Init9Datatypes3sum02c59OSSVerify5KrLib2AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib3Lib3CfgAtransparent_instrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C59OSSVerify5KrLib2AS7ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:node_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:rz_silent1C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim:msteps_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim7fd1chanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC59OSSVerify5KrLib2AS6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgGtransparent_nonalloc_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC59OSSVerify5KrLib2AS6CatSim;write1_ok_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?sstep_write_invC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00c59OSSVerify5KrLib2AS8ShapeAlg;node_write1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedc59OSSVerify5KrLib2AS8ShapeAlgCtransparent_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib2AS7ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06C59OSSVerify5KrLib2AS7ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8ShapeAlg8realizes02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg8rz_emit1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andK47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib2AS7MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:munmap_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim9munmap_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimCmunmap_model_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimDmunmap_model_no_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim@sstep_munmap_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim=page_round_upC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgAt_writes_pick_nilC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib2AS8ShapeAlg9rz_write1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgBt_writes_pick_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<to_wexit_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib2AS8ShapeAlgEexitline_realizes_auxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7WallSim7to_wall10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:t_alt_wallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7WallSim7to_wall00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7WallSim>to_wall_mutindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7WallSim;to_wallexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgAexitline_realizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg<rz_wall1_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgHt_writes_ch_exit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=t_writes_consC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7MmapSim3twm10C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7MmapSim3twm00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimDmunmap_model_fd1chanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim?munmap_model_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg9rz_munmapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7MmapSim3twm20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:twm_mutindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@twm_realizes_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@t_writes_ch_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim6fdchanC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C59OSSVerify5KrLib2AS6CatSim=write_ch_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimBsstep_write_ch_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=node_write_chC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim;to_wexit_ch00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg;rz_write_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgEt_writes_ch_pick_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?to_wexit_ch_indC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Hh11Th22trp;1p;4p;2g00B7j12Tg00EEj41Tg00I7j20Tg00Ilg00Ja#2f1R0f0R1O1R2f2P0O1[R0P0P1X02R2P2C1W21011eW1o"). Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h02H1h12H2h22H0h31Hh41Th52T'h62trp;2p;1p;5p;4g00I7j21Tg00B7j14Tg00KWj22Tg00L0j50Tg00EEj43Tg00IlR0f1R1f0R2'1g00Ja#4f2R3P2O1R4f4R5P1O1R6[f3R7P2O1R8P7P1O1R9[1269R9f5R6P3O1R:P6P7O1R6[R;P5P3O1R<f6R=P7O1[R>P:f7P5O1R:\6R6P2X1:P2P7O1O1W1X0;P2D0W0P3P1O1R:O1X24P;P>P<P=P5O1P2W0P1P7O1O1X16X0;P2D0X09P:O1X28C3W61113eW3X50W4o"). Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

(* [comment removed for export] *)
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

(* [comment removed for export] *)
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Tp;2g00Dkj20Tg00IlR0f0,00W0o"). Qed.
Lemma t_writes_pick_cons : forall buf bufs T,
  t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
  t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_writes_nil : forall T, t_writes [] T = T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Tp;2g00Dkj20Tg00IlR0f0,00W0o"). Qed.
Lemma t_writes_cons : forall buf bufs T,
  t_writes (buf :: bufs) T
  = t_emit (map (WriteEv (Z_to_bv 64 1)) buf) (t_writes bufs T).
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : forall ch buf bufs T,
  t_writes_ch ch (buf :: bufs) T
  = t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
  intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
    apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_exit_iff : forall ch bufs code fs tr,
  t_writes_ch ch bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]).
Proof.
  intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
  - cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
    + intro H. left. exact H.
  - rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
    unfold t_emit at 1. split.
    + intros [H | (tr' & -> & Hc)].
      * apply is_prefix_app_r; exact H.
      * apply is_prefix_app_mono. apply IH. exact Hc.
    + intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
      * left; exact H.
      * right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.

Lemma t_writes_exit_iff : forall bufs code fs tr,
  t_writes bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents bufs ++ [ExitEv code fs]).
Proof.
  intros bufs code fs tr. unfold t_writes.
  rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_pick_exit_iff : forall ch bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (fold_right (t_write_ch ch) (t_exit code fs) bufs tr
   <-> exists full, wpick ch bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof.
  intros ch bufs code fs tr Hall; revert tr;
    induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
  - cbn [fold_right]. unfold t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)].
      * exists []. split; [apply wp_nil | exact H].
      * exists []. split; [apply wp_nil|].
        rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
    + intros (full & Hw & Hp). inversion Hw; subst full.
      left. exact Hp.
  - cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
    split.
    + intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
      destruct Hi as [H | (tr' & -> & Hc)].
      * exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
        split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
        rewrite <- app_assoc.
        eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
      * apply IH in Hc. destruct Hc as (full & Hw & Hp).
        exists (map (WriteEv ch) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption|].
        rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
    + intros (full & Hw & Hp).
      inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
      rewrite <- app_assoc in Hp.
      apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
        exists tr'. split; [reflexivity|].
        apply IH. exists tr0. split; assumption.
Qed.

Lemma t_writes_pick_exit_iff : forall bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (t_writes_pick bufs (t_exit code fs) tr
   <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.


(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition pnode_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Lemma node_ok_of_pnode : forall c I evs nx,
  cfg_transparent segs c -> pnode_ok c I evs nx -> node_ok c I evs nx.
Proof.
  intros c I evs nx Htr [Hcomp Hsound]. split.
  - intros i. apply Htr. apply Hcomp.
  - intros e st Hss. apply Hsound. exact (sstep_of_cfg segs ACFG _ _ _ Hss).
Qed.

Lemma transparent_exit_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> cfg_transparent segs (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [E|E]; apply (transparent_nonalloc segs ms model x8 Hsvc); rewrite E;
    apply alloc_no_b_false; reflexivity.
Qed.

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (* LPS 727298f3: the node's system call reads no byte the run's backing adds
       ([RomBase.sys_rob]; [RomStable.run_init] lifts a walk to the run's start) *)
    sys_rob segs c ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

(* [comment removed for export] *)
Lemma rz_path_star : forall c tr c',
  star_cfg segs ACFG c tr c' -> rz_path c -> rz_path c'.
Proof.
  intros c tr c' Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Hp; [exact Hp|].
  apply IH. destruct Hp as [T HT]. exact (realizes_step c1 T evs c2 HT Hss).
Qed.

(* [comment removed for export] *)
Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (rz_path_star c tr c' Hstar (ex_intro _ T H)) as [T' HT'].
  exact (realizes_no_sserror c' T' evs HT' Herr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') -> sys_rob segs c ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok c I (fun _ => []) nx -> sys_rob segs c ->
  (forall i, realizes (nx i) T) ->
  realizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT i0)).
  apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Lemma rz_emit1 : forall c c' e T,
  node_ok c unit (fun _ => e) (fun _ => c') -> sys_rob segs c ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok c (IA + IB) (fun _ => []) nx -> sys_rob segs c ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode Hrob).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc |]. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | apply sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma node_write1 : forall ms model x8 buf,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
buf_modeled buf ->
(1 <= length buf)%nat ->
node_ok (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model).
Proof.
intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb.
apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 64 Hsvc Hno); reflexivity |]. split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- intros e st Hss.
destruct (sstep_write_inv segs ms model x8 buf e st
Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 ms model x8 buf); assumption.
  - apply (write1_rob segs ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply node_ok_of_pnode; [exact (transparent_exit_no ms model x8 Hsvc Hx8) |]. split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - exact (sys_rob_exit segs ms model x8 Hsvc Hx8).
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes (mkCfg ms model) T.
Proof.
(* [comment removed for export] *)
(* [comment removed for export] *)
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply rz_silent1; [| | exact Hc].
(* 215 (munmap) joined Run.injected_table at #38, so [alloc_no_b 215] is TRUE and the goal
   this [reflexivity] had to close, [alloc_no_b 215 = false], is FALSE at this model rather
   than merely unproved (measured, :642 characters 90-101).  The family-OFF route is the
   one this unit's own AS/MmapSim.v:471 munmap_node_cfg already takes.  zstd/simple_decompress
   AS/ShapeAlg.v:636 states exactly this line under the same [eapply rz_silent1], and that
   file compiles in the kernel (measured). *)
  - exact (munmap_node_cfg segs ms model x8 Hh Hlazy Hsvc Hno Hargs).
  - eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_215].
Qed.

End WithSegs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cat_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wexit segs ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exitline_realizes_aux : forall segs ms bufs code model,
  to_wexit segs ms bufs code -> bufs = [] ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms bufs code model Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
    [| discriminate Hbufs |]; intro Hlazy.
  - eapply rz_exit; eassumption.
  - eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
    apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.

Lemma exitline_realizes : forall segs ms code model,
  to_wexit segs ms [] code ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms code model Hte Hh Hlazy.
  exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.

Lemma rz_wall1_mut : forall segs model,
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  (forall ms rest k, to_wall segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
  /\ (forall ms rest k, to_wall_tail segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T)).
Proof.
  intros segs model Hh Hlazy Hfd.
  apply (to_wall_mutind segs (Z_to_bv 64 1)
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
  - (* twl_write *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm T HT Hk.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest)) T)
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - apply (write1_rob segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  - (* twt_done *)
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | exact (IH Hbm T HT Hk)].
Qed.

(* [comment removed for export] *)
Lemma wall_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
  induction bufs as [|buf rest IH]; intros ms Hw Hbm.
  - exact (exitline_realizes segs ms code model Hw Hh Hlazy).
  - destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons.
    eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
    + exact Ht.
    + exact Hb.
    + unfold t_writes. apply t_writes_ch_exit_has_nil.
    + intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.

(* [comment removed for export] *)
Lemma twm_realizes_mut : forall segs,
  (forall ms model bufs code, MmapSim.twm segs ms model bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
  /\ (forall ms model rest bufs code, MmapSim.twm_pend segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model)))))
  /\ (forall ms model rest bufs code, MmapSim.twm_tail segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model))))).
Proof.
  intros segs.
  apply (MmapSim.twm_mutind segs
    (fun ms model bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))).
  - (* twm_exit *)
    intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
  - (* twm_write *)
    intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
  - (* twm_munmap *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hfail IHfail Hcut IH Hh Hlazy Hfd Hbm.
    eapply rz_munmap;
      [exact Hh | exact Hlazy | exact Hsvc | exact Hno | exact Hargs | ].
    rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
    apply IH; [rewrite munmap_model_halted; exact Hh
              | exact (munmap_model_no_lazy _ _ _ Hlazy)
              | apply munmap_model_fd1chan; exact Hfd | exact Hbm].
  - (* twm_step *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_step; try eassumption. apply IH; assumption.
  - (* twmp_write *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest))
                         (t_writes bufs (t_exit code (m_fs model))))
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - apply (write1_rob segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
    apply t_alt_wall;
      [unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
  - (* twmt_done *)
    intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq; [apply IH; assumption|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
    unfold t_writes. apply t_writes_ch_exit_has_nil.
  - (* twmt_more *)
    intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
    exact (IH Hh Hlazy Hfd Hbr Hbm).
  - (* twmt_step *)
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.

Lemma twm_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  MmapSim.twm segs ms model bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  intros segs ms model bufs code Hh Hlazy Hfd Hte.
  exact (proj1 (twm_realizes_mut segs) ms model bufs code Hte Hh Hlazy Hfd).
Qed.


(* [comment removed for export] *)

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
  t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.

Lemma node_write_ch : forall segs ms model fd ch x8 buf,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model -> fd32 fd = fd ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
buf_modeled buf ->
(1 <= length buf)%nat ->
node_ok segs (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model).
Proof.
intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb.
apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 64 Hsvc Hno); reflexivity |]. split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv ch) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ eapply write_ch_ok_n; eassumption.
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- intros e st Hss.
destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes segs
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - apply (write_ch_rob segs ms model fd ch x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma cat_realizes_ch : forall segs fd ch ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  to_wexit_ch segs fd ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_ch_pick ch bufs (t_exit code (m_fs model))).
Proof.
  intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
  revert model Hh Hlazy Hfdc.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfdc Hbm.
  - eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
