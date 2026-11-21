(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed ENOMEM_in_mprotect_errnos, Hno56, Z_to_bv_u_eq' and 181 more; added grant_ok_na_of_place, grant_ok_na_pin, grant_ok_na_pin_unpack and 7 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/RefNodes.v, 1034 lines within its lines 13-2475. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite RomWritev.
Module AgentNodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof. reflexivity. Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof. reflexivity. Qed.

Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
  ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof. reflexivity. Qed.

Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof. reflexivity. Qed.

Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof. reflexivity. Qed.

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_set. Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.

(* [comment removed for export] *)
Lemma rz_sys : forall segs scfg regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs scfg regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply srz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_write_chan : forall segs scfg regs pc mem model fd ch n bs T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 64%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdChannel ch) -> w_is0 ch = false ->
  m_channel_reader model = true ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
  (1 <= n)%nat -> (Z.of_nat n <= rw_bytes_max)%Z -> (Z.of_nat n < 2 ^ 64)%Z ->
  rdn segs mem (getr regs 11) n = Some bs ->
  (* [comment removed for export] *)
  access_okb (getr regs 11) (Z.of_nat n) = true ->
  (forall k, (1 <= k)%nat -> (k <= n)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) T) ->
  srealizes segs scfg (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
           (t_write_ch ch bs T).
Proof.
  intros segs scfg regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hrdr Hcnt Hn1 Hmax Hn64 Hrd Hok Hc.
  pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
  eapply (srz_write_ch segs scfg _ model fd ch (getr regs 17) bs T Hh Hlazy).
  - unfold fdchan. split; [exact Hlk | split; [exact Hch | exact Hrdr]].
  - apply fd32_id. exact Hfd32.
  - reflexivity.
  - exact Hno.
  - rewrite ms_gpr_epend0. exact Hfd.
  - rewrite ms_gpr_epend1, ms_gpr_epend2, Hcnt.
    rewrite (ms_read_bytes_rdn segs) by reflexivity. cbn [ms_mem epend].
    unfold word_to_nat. rewrite u64_lit by lia. rewrite Nat2Z.id. exact Hrd.
  - rewrite ms_gpr_epend1, ms_gpr_epend2, Hcnt, u64_lit by lia. exact Hok.
  - unfold buf_modeled. rewrite Hlen. exact Hmax.
  - rewrite Hlen. exact Hn1.
  - intros k Hk1 Hk2. rewrite adv_set_epend.
    replace (len_word (firstn k bs)) with (Z_to_bv 64 (Z.of_nat k)); [apply Hc; lia|].
    unfold len_word. rewrite length_firstn, Hlen. f_equal. lia.
Qed.

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
  intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rz_exit_lit : forall segs scfg regs pc mem rom model code,
  m_halted model = None -> is_exit_no (getr regs 17) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model)
           (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros segs scfg regs pc mem rom model code Hh Hx8 Ha0 Hc.
  rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.

End FPX_1.

End AgentNodes.
From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.SpecConsts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_RefNodes () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib7Mh_00368ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib7Mh_00948RefNodes6t_alt3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsI47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01I47Corelib7Numbers7BinNums1Z00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1Z02C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch9lookup_caC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch8ca_checkC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib7Mh_00307ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch:CheckedArm00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch=checked_tableK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5cmd32C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs5Ioctl;check_ioctlC59OSSVerify5KrLib7Mh_00437FileSim;in_sysno_siC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys6Kernel4ForkEcheck_set_tid_addressC59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes8rz_casesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00i59OSSVerify5KrLib7Mh_00948RefNodes5three00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00948RefNodes5three01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00948RefNodes5three02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00948RefNodes5three03C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00c59OSSVerify5KrLib7Mh_00948RefNodes;node_of_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim;adv_eff_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes5ependC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00388AllocSim?apply_zeros_oneC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC59OSSVerify5KrLib7Mh_00387MmapSim5zfillC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_00387MmapSim6unfillC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0038:StreamExec?adv_apply_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open;check_closeC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idc59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim@check_syscall_57C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@with_fds_halted'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes=with_fds_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0c59OSSVerify5KrLib7Mh_0094:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5NodesBrz_ret_only_silentC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes6rz_sysC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFK46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry07K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry08K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry09c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@check_syscall_29C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Ioctl@tty_only_requestC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06I4ELinuxProcessSemantics?LinuxProcessSem5State9SockState00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry0:C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite:check_readC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State7in_wmemC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5State>rw_count_clampC4ELinuxProcessSemantics?LinuxProcessSem5State=stream_take_zC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem5State;stream_takeC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude9listN_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude7wmem_okC4ELinuxProcessSemantics?LinuxProcessSem5State:with_stdinK4ELinuxProcessSemantics?LinuxProcessSem5State5event01K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7UaccessDcheck_access_ok_zeroC4ELinuxProcessSemantics?LinuxProcessSem5State:net_take_zC4ELinuxProcessSemantics?LinuxProcessSem5State8net_takeK4ELinuxProcessSemantics?LinuxProcessSem5State9SockState04C4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State=pipe_end_liveC4ELinuxProcessSemantics?LinuxProcessSem5State9pipe_takeC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:writes_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State<pipe_consumeC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_insertC4ELinuxProcessSemantics?LinuxProcessSem5State:with_pipesC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteBcheck_read_urandomC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib7Mh_00948RefNodesCaccess_okb_intro_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim@check_syscall_63C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@modeled_rw_rangeC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteJcheck_socket_pending_errorC4ELinuxProcessSemantics?LinuxProcessSem5State:ECONNRESETC4ELinuxProcessSemantics?LinuxProcessSem5State9ETIMEDOUTC4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRC4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State8ENOTCONNI4ELinuxProcessSemantics?LinuxProcessSem5State9NetStream00C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes;rz_read_dirC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib7Mh_00437FileSim@length_file_readC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEread_bytes_map_prefixC59OSSVerify5KrLib7Mh_00437FileSim:in_wmem_siC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC5ELinuxProcessSemantics?LinuxProcessSem3Sys7UaccessDrw_count_clamp_of_rwC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEcheck_ret_only_ok_iffC47Corelib4Init5Logic7and_indC47Corelib4Init9Datatypes9andb_propC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<listN_eqb_eqK4ELinuxProcessSemantics?LinuxProcessSem5State7FdState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC47Corelib4Init5Logic5proj2C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeKcheck_ret_only_no_unmodeledC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib7Mh_0007:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib7Classes?RelationClasses>iff_TransitiveC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00438AgentLibJread_bytes_map_of_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib7Mh_0094:AgentNodesFms_writable_byte_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes?read_file_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes=adv_ret_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@adv_write1_ependC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes6rz_detC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=clear_copyinsC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenAcheck_open_resultC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=check_copyinsC59OSSVerify5KrLib7Mh_00437FileSimQcheck_open_result_never_unmodeledC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeCcheck_copyins_afterC59OSSVerify5KrLib7Mh_00437FileSimIcheck_open_result_copyinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264Scfg=fam_on_openatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes5Hno56C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open<check_openatC59OSSVerify5KrLib7Mh_00437FileSim<open_copyinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9read_cstrC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open@check_openat_sepC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>path_is_dirrefC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBmodeled_open_flagsC4ELinuxProcessSemantics?LinuxProcessSem5State6in_memC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenAcheck_openat_bodyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenEcheck_openat_resolvedC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z3eqbC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenAcheck_openat_readC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenCcheck_openat_createC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>is_excl_createC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenAcheck_openat_exclC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open@check_openat_dirC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenCcheck_openat_appendC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>rdwr_open_wordC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open8flag_setC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenAcheck_openat_rdwrC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenCis_rdwr_excl_createC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenFcheck_openat_rdwr_exclc59OSSVerify5KrLib7Mh_0094:AgentNodesBms_read_byte_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim9in_mem_siC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenEmodeled_open_flags_rdC59OSSVerify5KrLib7Mh_00437FileSim@check_syscall_56C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateCcstr_access_len_auxC4ELinuxProcessSemantics?LinuxProcessSem5State8path_maxI4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result00C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTC4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:AT_FDCWD32C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open?wr_create_flagsC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;O_DIRECTORYC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenCappend_create_flagsC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi7O_CREATC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi7O_TRUNCC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSimHread_cstr_toolong_of_rdnC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC59OSSVerify5KrLib7Mh_00437FileSimLcheck_copyins_after_ret_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesAopenat_check_headC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5NodesJrz_ret_only_copyins_silentC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result02c59OSSVerify5KrLib7Mh_00948RefNodes7path_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addK4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result01C59OSSVerify5KrLib7Mh_00437FileSim@read_cstr_of_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes<path_at_cstrC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenAopenat_plain_nameC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenJopenat_plain_name_nodirrefC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenIopenat_plain_name_noslashC59OSSVerify5KrLib7Mh_00437FileSim<path_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdc59OSSVerify5KrLib7Mh_00948RefNodesOcheck_copyins_after_open_resultC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenGpath_is_dirref_no_slashC49OSSVerify5KrLib5Nodes7rz_openC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosc59OSSVerify5KrLib7Mh_00948RefNodes@fam_on_openat_msC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@rz_openat_dirrefC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathC4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib7Mh_00387MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim=page_round_upC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<mmap_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim>adv_mmap_grantC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim8grant_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg@srz_mmap_nograntC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC59OSSVerify5KrLib7Mh_00387MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib7Mh_00388AllocSimFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_00387MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesAadv_unmaps1_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:munmap_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_munmapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removec59OSSVerify5KrLib7Mh_00948RefNodesAwith_vmmaps_lazy'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesBvm_forget_range_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSimAbrk_resolution_okC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okC46Stdlib4Bool4Bool<orb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC4ELinuxProcessSemantics?LinuxProcessSem3Run=brk_refusal_bC59OSSVerify5KrLib7Mh_00388AllocSimDin_arg0_sys_input214C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC59OSSVerify5KrLib7Mh_00264Scfg=refusal_b_brkC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsC59OSSVerify5KrLib7Mh_00388AllocSim9brk_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim<brk_ok_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim>brk_step_shapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes7brk_admC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00C47Corelib4Init6Specif9proj1_sigc59OSSVerify5KrLib7Mh_00948RefNodes7brk_effC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK47Corelib4Init6Specif3sig01C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC59OSSVerify5KrLib7Mh_00264ScfgIinjected_family_off_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264Scfg?not_spurious_onC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC59OSSVerify5KrLib7Mh_00388AllocSim:brk_ok_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@refusal_b_brk_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264ScfgCnot_spurious_forcedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264ScfgGnot_spurious_nonrefusalC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib7Mh_00264Scfg>spurious_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes>brk_r_ok_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim@brk_no_unmodeledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8node_svcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib7Mh_00948RefNodes=brk_adm_queryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes8node_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes?with_vmmaps_etaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes:vmmaps_etaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim?brk_model_queryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim?brk_unmaps_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim?brk_zeros_queryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_cases1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@srz_brk_query_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=brk_budget_okC56Stdlib6ZArith6BinInt1Z:ltb_irreflC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_00948RefNodesCbrk_r_ok_grow_casesC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_grantsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapDmaps_subtract_rangesC59OSSVerify5KrLib7Mh_00388AllocSim?brk_grants_keepC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_subC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC45stdpp9bitvector;definitions?bv_sub_unsignedC59OSSVerify5KrLib7Mh_00388AllocSim?brk_unmaps_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim?brk_grants_growC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesBbrk_adm_grow_casesC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_page_rangec59OSSVerify5KrLib7Mh_00948RefNodes=Z_to_bv_u_eq'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesAbrk_model_grow_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib7Mh_00388AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib7Mh_00388AllocSim>brk_zeros_growC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes>brk_model_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim>brk_zeros_keepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@adv_zeros1_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes?srz_brk_grow_atC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosC49OSSVerify5KrLib5Nodes;node_chk_spC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00c59OSSVerify5KrLib7Mh_00948RefNodesCnode_chk_grant_onlyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedc59OSSVerify5KrLib7Mh_00948RefNodes;grant_ok_naC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib7Program6Basics4implc59OSSVerify5KrLib7Mh_00948RefNodesBgrant_ok_na_unpackC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valc59OSSVerify5KrLib7Mh_00948RefNodesEmmap_noaccess_args_okC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC46Stdlib4Bool4Bool:andb_assocc59OSSVerify5KrLib7Mh_00948RefNodes:mmap_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes>noaccess_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTc59OSSVerify5KrLib7Mh_00948RefNodesCmmap_noaccess_checkC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFpage_round_up_Z_nonnegc59OSSVerify5KrLib7Mh_00948RefNodesGinjected_family_off_222C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqc59OSSVerify5KrLib7Mh_00948RefNodesBgrant_na_not_errnoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesAerrno_ret_in_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264Scfg>refusal_b_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSimBwith_vmmaps_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesBnode_mmap_noaccessC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesDsrz_mmap_noaccess_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes>mprotect_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_grows_conflict_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib7Mh_00948RefNodesAcheck_syscall_226C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextc59OSSVerify5KrLib7Mh_00948RefNodes>mprotect_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesGinjected_family_off_226C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesEerrno_ret_in_mprotectC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00264ScfgBrefusal_b_mprotectC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes?srz_mprotect_atC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_introC49OSSVerify5KrLib5Nodes8node_detC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg;srz_silent1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesIENOMEM_in_mprotect_errnosC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesDfixed_noaccess_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesEfixed_destroyed_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesBmmap_fixed_args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@mmap_fixed_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesFvm_forget_range_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesHvm_forget_range_lazy_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesJsrz_mmap_fixed_noaccess_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes5tid_IC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes8node_chkC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidc59OSSVerify5KrLib7Mh_00948RefNodes@check_syscall_96C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC59OSSVerify5KrLib7Mh_00306CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7m_credsC4ELinuxProcessSemantics?LinuxProcessSem5StateBm_setsid_succeededC4ELinuxProcessSemantics?LinuxProcessSem5State9m_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State?procst_childrenC4ELinuxProcessSemantics?LinuxProcessSem5State9m_utsnameC4ELinuxProcessSemantics?LinuxProcessSem5StateGm_sigaltstack_installedC4ELinuxProcessSemantics?LinuxProcessSem5State=procst_killedC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_sigabrt_pendingC4ELinuxProcessSemantics?LinuxProcessSem5State@m_abort_terminalC4ELinuxProcessSemantics?LinuxProcessSem5State:m_statpinsK4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState01c59OSSVerify5KrLib7Mh_00948RefNodes?with_tid_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes=with_tid_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<injected_armC59OSSVerify5KrLib7Mh_00264ScfgHinjected_family_off_noneC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;InjectedArm00C59OSSVerify5KrLib7Mh_00264Scfg?injected_arm_96C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes<node_set_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes:one_tid_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes>srz_set_tid_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes:rz_exit_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes@bv_and_255_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backed_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topc59OSSVerify5KrLib7Mh_00948RefNodesIbrk_grow_ok_aligned_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSimEregion_free_above_topC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesFvm_backing_used_simpleC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib7Mh_00387MmapSim@region_free_consC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>andb_false_iffC46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool:orb_true_rc59OSSVerify5KrLib7Mh_00948RefNodes?map_remove_skipC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractC46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_00948RefNodesCiv_subtract_coveredC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes=u64_roundtripC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_lC56Stdlib6ZArith6BinInt1Z5min_lC56Stdlib6ZArith6BinInt1Z5min_rC56Stdlib6ZArith6BinInt1Z5max_rI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_00948RefNodesAiv_subtract_sizesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;incl_filterC46Stdlib5Lists4List;incl_ForallC46Stdlib5Lists4List:length_appC47Corelib4Init3Nat3mulC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulc59OSSVerify5KrLib7Mh_00948RefNodesIlive_bytes_iv_subtract_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes>live_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<transitivityC47Corelib7Classes?RelationClassesCPreOrder_Transitivec59OSSVerify5KrLib7Mh_00948RefNodesKlive_bytes_maps_subtract_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesFmaps_subtract_all_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderc59OSSVerify5KrLib7Mh_00948RefNodesOlive_bytes_maps_subtract_all_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesGvm_backed_bytes_le_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesGvm_backing_used_le_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSim>with_vmmaps_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesFmprotect_model_next_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesCfile_read_length_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8prod_indc59OSSVerify5KrLib7Mh_00948RefNodes:zconflictbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes9zconflictC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltK46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib7Mh_00948RefNodes4candC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat=lt_trichotomyK46Stdlib9micromega=RingMicromega5Psatz07c59OSSVerify5KrLib7Mh_00948RefNodes<cand_spacingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC35stdpp7tactics<f_equal_helpC46Stdlib9micromega;ZifyClasses:impl_morphI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List<NoDup_filterc59OSSVerify5KrLib7Mh_00948RefNodes?zconflictb_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes?conflict_uniqueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesGfilter_keep_all_but_oneC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9filter_InC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List9seq_NoDupC46Stdlib5Lists4List:length_seqc59OSSVerify5KrLib7Mh_00948RefNodes>pick_candidateC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List6in_seqC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z7mul_modC56Stdlib6ZArith6BinInt1Z9mul_assocc59OSSVerify5KrLib7Mh_00948RefNodesIregion_free_of_noconflictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesCgrant_exists_na_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC59OSSVerify5KrLib7Mh_00387CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesCalloc_top_ge_windowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodes@grant_exists_genC1?~~~~~~~~~~~~~~~".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite RomWritev.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rob_mf Heq :=
  eapply RomBase.sys_rob_memfree;
    [ first [reflexivity | eassumption]
    | rewrite Heq; first [RomBase.memfree_lit | rewrite u64_lit by lia; RomBase.memfree_lit] ].

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
  intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma access_okb_intro_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma mmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z ->
  check_syscall (sys_input segs ms x8) eff model
  = check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 215%Z ->
  check_syscall (sys_input segs ms x8) eff model = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma ioctl_tty_rob : forall ms model x8, ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true -> RomBase.sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hno Htty. apply RomBase.sys_rob_of_check. intros r x8' Hr Hs' eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_29 _ x8 eff model Hno).
  change (ms_gpr (RomBase.wrom ms r) 0) with (ms_gpr ms 0).
  change (ms_gpr (RomBase.wrom ms r) 1) with (ms_gpr ms 1).
  unfold check_ioctl. rewrite Htty. destruct (fd_lookup _ _) as [[]|]; lazy beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma check_syscall_226 : forall ms x8 eff m,
  bv_unsigned x8 = 226%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Inductive three : Type := T1 | T2 | T3.

Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs scfg c three (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  srealizes segs scfg (nx T1) A -> srealizes segs scfg (nx T2) B -> srealizes segs scfg (nx T3) C ->
  srealizes segs scfg c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode Hrob HA HB HC.
  apply (srz_conseq segs scfg c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs scfg c three nx _ T1 Hnode Hrob). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  (forall i, sstep_cfg segs scfg c (evs i) (SNext (nx i))) ->
  (forall e st, sstep_cfg segs scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  node_ok segs scfg c I evs nx.
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | rob_mf H17 | | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
  - rewrite with_fds_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_ioctl_winsz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  (* [comment removed for export] *)
  match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end = true ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hnd H11 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity
                             | eapply ioctl_tty_rob; [reflexivity | rewrite H17; apply u64_lit; lia
                                                     | rewrite ms_gpr_epend1, H11; reflexivity]
                             | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
  unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
  destruct e; first [reflexivity | discriminate Hnd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_read_dir : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  (bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hts Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | rob_mf H17 | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite (access_okb_intro_le _ _ (proj1 (bv_unsigned_in_range 64 (getr regs 12))) Hts).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_read_dir_cnt : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt -> (0 <= cnt)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H12 Hc0 Hts Hc.
  eapply (rz_read_dir regs pc mem model w fd K); try eassumption.
  rewrite H12, u64_lit; [exact Hts|]. unfold TASK_SIZE in Hts. pose proof (u64_range (getr regs 11)). lia.
Qed.

(* [comment removed for export] *)
Lemma read_file_check : forall ms x8 model fd p off data wv,
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some wv ->
  (0 < bv_unsigned (ms_gpr ms 2))%Z -> (bv_unsigned (ms_gpr ms 2) <= 65536)%Z ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  let bs := file_read data off (ms_gpr ms 2) in
  let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
  (forall eff mx evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk mx evs <->
     (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [] /\ mx = m' /\ evs = []))
  /\ (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled).
Proof.
  intros ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs Hw Hpos Hcnt65 Haok bs m'.
  assert (Hcnt : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by (pose proof rw_bytes_max_ge17; lia).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hred : forall eff, check_syscall (sys_input segs ms x8) eff model =
    match bs, eff with
    | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
    | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
        if bv_eqb a (ms_gpr ms 1) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
        then CheckOk m' [] else CheckReject
    | _ :: _, _ => CheckReject
    end).
  { intros eff. rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite H0, (fd32_id fd Hfd32), Hlk. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta. rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    fold bs. fold m'.
    destruct bs as [|b bsr]; reflexivity. }
  split.
  - intros eff mx evs. rewrite Hred. destruct bs as [|b bsr].
    + rewrite check_ret_only_ok_iff. cbn [delivered_writes]. unfold len_word. cbn [length Z.of_nat]. tauto.
    + destruct eff as [ret ws zs us cs ci]. split.
      * intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))%bool eqn:E;
          [|discriminate].
        apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
        apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst.
        injection H; intros; subst. repeat split; reflexivity.
      * intros (E1 & -> & ->). cbn [delivered_writes] in E1. injection E1; intros; subst.
        rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff. rewrite Hred. destruct bs as [|b bsr].
    + apply check_ret_only_no_unmodeled.
    + destruct eff as [ret ws zs us cs ci].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate.
      destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (_ && _)%bool; discriminate.
Qed.

Lemma rz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 65536)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  let bs := file_read data off (getr regs 12) in
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hts bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; apply access_okb_intro_le; lia)) as [Hchk Hnu].
  unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  subst bs. revert Hc Hchk.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
  eapply (rz_det segs scfg _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | rob_mf H17 | exact Hchk | exact Hnu
    | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
  - unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_copyins_after_open_result : forall reads eff m mk,
  Prelude.check_copyins_after reads eff (check_open_result (clear_copyins eff) m mk)
  = check_open_result_copyins reads eff m mk.
Proof.
  intros reads eff m mk. unfold Prelude.check_copyins_after, check_open_result_copyins.
  destruct (check_open_result (clear_copyins eff) m mk) eqn:E; [reflexivity|reflexivity|].
  exfalso. exact (check_open_result_never_unmodeled _ _ _ E).
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.
  (* [comment removed for export] *)
  Hypothesis Hfs_on : sc_fs scfg = true.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  Lemma fam_on_openat_ms : fam_on segs scfg ms.
  Proof. apply (fam_on_openat segs scfg ms (getr regs 17)); [reflexivity | exact Hno56 | exact Hfs_on]. Qed.

  (* [comment removed for export] *)
  Lemma openat_check_head : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = Prelude.check_copyins_after (open_copyins ms) eff
      match read_cstr (mrb segs mem) (getr regs 11) with
      | CstrTooLong => check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG) model []
      | CstrFault => check_ret_only (clear_copyins eff) (errno_ret EFAULT) model []
      | CstrOk p =>
          if path_eqb p [] then check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
          else if path_has_slash p then Open.check_openat_sep p (getr regs 12) (clear_copyins eff) model  (* [comment removed for export] *)
          else if path_is_dirref p then
                 check_open_result (clear_copyins eff) model (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
               else match fs_lookup (m_fs model) p with
                    | None => check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
                    | Some _ => check_open_result (clear_copyins eff) model
                                  (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
                    end
      end.
  Proof.
    intros eff. cbv delta [ms].
    rewrite (check_syscall_56 segs _ _ eff model Hno56). unfold check_openat.
    rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2.
    rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota zeta.
    unfold Open.check_openat_body. rewrite in_mem_si, ms_read_byte_epend.
    unfold open_copyins. rewrite ms_read_byte_epend, ms_gpr_epend1.
    destruct (read_cstr (mrb segs mem) (getr regs 11)) as [p| |]; [|reflexivity|reflexivity].
    destruct (path_eqb p []); [reflexivity|].
    rewrite H10. norm_fd32. rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved.
    destruct (path_has_slash p); [reflexivity|].
    rewrite Hfl. cbn [Z.eqb]. reflexivity.
  Qed.

  Lemma openat_node_rob : read_cstr (mrb segs mem) (getr regs 11) <> CstrFault ->
    RomBase.sys_rob segs (mkCfg ms model).
  Proof.
    intros Hnf. apply (RomWrite.openat_rob segs ms model (getr regs 17) eq_refl Hno56).
    unfold ms. rewrite ms_read_byte_epend, ms_gpr_epend1. exact Hnf.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    (* [comment removed for export] *)
    (bv_unsigned (getr regs 11) + 4096 <= TASK_SIZE)%Z ->
    srealizes segs scfg (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hts Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hts Hrd) as Hp.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | apply openat_node_rob; rewrite Hp; discriminate
                                      | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, Hp. apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ (bv_unsigned (getr regs 11) + Z.of_nat (length p) < TASK_SIZE)%Z
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3 & H4). apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_empty : forall K,
    path_at [] ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | apply openat_node_rob; rewrite (path_at_cstr [] Hp); discriminate
                                      | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, (path_at_cstr [] Hp). apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_absent : forall p K,
    path_at p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hpl Hfs Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | apply openat_node_rob; rewrite (path_at_cstr p Hp); discriminate
                                      | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
    rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
    apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma rz_openat_dirref : forall p KA KB,
    path_at p -> path_is_dirref p = true ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hdr HA HB. cbv delta [post] in *.
    assert (Hne : p <> []) by (intros ->; discriminate Hdr).
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | apply openat_node_rob; rewrite (path_at_cstr _ Hp); discriminate
                    | | | | exact Hfree | exact fam_on_openat_ms | |].
    - intros eff. fold ms. rewrite openat_check_head, (path_at_cstr _ Hp).
      rewrite (path_eqb_neq _ _ Hne), (path_is_dirref_no_slash _ Hdr), Hdr.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  Lemma rz_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof. intros KA KB Hp. apply (rz_openat_dirref dot_path KA KB Hp). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_file : forall p d KA KB,
    path_at p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | apply openat_node_rob; rewrite (path_at_cstr _ Hp); discriminate
                    | | | | exact Hfree | exact fam_on_openat_ms | |].
    - intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
      rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

(* [comment removed for export] *)
Lemma alloc_fd_init : forall e0 e1 e2,
  alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. reflexivity. Qed.

Lemma fd_lookup_init_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_mmap_anon : forall regs (pc : word) mem model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  sc_alloc scfg = false ->
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z len) = false ->
  let n := page_round_up_Z len in
  (exists a, grant_ok (getr regs 10) model a n = true) ->
  (forall a, grant_ok (getr regs 10) model a n = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (mmap_model a (Z_to_bv 64 n) model)) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Halloc Hdecl n Hex HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  destruct Hex as (a0 & Ha0).
  eapply (srz_mmap segs scfg ms model (getr regs 17) KB Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs
            ltac:(rewrite H0, Hu1; exact Hdecl) Halloc).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
  - rewrite H0, Hu1. exists a0. exact Ha0.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_anon_nogrant : forall regs (pc : word) mem model w (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (* The no-grant producer of the same arm: with no placement admissible the
     node is the ENOMEM refusal, which [check_mmap] only answers when the
     decline did NOT fire -- a declined call is [CheckUnmodeled], not an errno.
     Same shape as the model's [mmap_fail_ok], which is premised. *)
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z len) = false ->
  (forall a, grant_ok (getr regs 10) model a (page_round_up_Z len) = false) ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem (seg_rom segs)) model) KA ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KA.
Proof.
  intros regs pc mem model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hdecl Hng HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply (srz_mmap_nogrant segs scfg ms model (getr regs 17) KA Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs
            ltac:(rewrite H0, Hu1; exact Hdecl)).
  - rewrite H0, Hu1. exact Hng.
  - unfold ms. rewrite adv_set_epend. exact HA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_munmap : forall regs (pc : word) mem model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->      (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  (* [comment removed for export] *)
  sc_alloc scfg = false ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Halloc Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg.srz_munmap segs scfg ms model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs | exact Halloc |].
  unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

Lemma munmap_model_simple : forall (a n : word) m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  munmap_model a n m = with_vmmaps (mmap_fixed_destroyed_next (m_vmmaps m) a n) m.
Proof.
  intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
  apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                 (brk_unmaps r (vm_brk (m_vmmaps model))) [] [].

(* [comment removed for export] *)
Definition brk_adm (model : Model) (req r : word) : Prop :=
  brk_resolution_ok model req r
  /\ (sc_alloc scfg = false -> brk_refusal_b model req r = true ->
      forall r', brk_resolution_ok model req r' -> brk_refusal_b model req r' = true).

(* [comment removed for export] *)
Lemma brk_r_ok_cases : forall m req r,
  brk_resolution_ok m req r -> r = vm_brk (m_vmmaps m) \/ r = req.
Proof.
  intros m req r H. unfold brk_resolution_ok, Mmap.brk_r_ok in H. cbv zeta in H.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m)))%Z)%bool.
  - left. apply bv_eqb_eq. exact H.
  - destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z.
    + apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H; auto.
    + apply andb_true_iff in H as [H _]. apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H; auto.
Qed.

Lemma refusal_b_brk_ms : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof.
  intros ms x8 model r Hno. rewrite (refusal_b_brk (sys_input segs ms x8) model r)
    by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input214. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_brk : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs scfg (mkCfg ms model)
    {r : word | brk_adm model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno.
  set (req := ms_gpr ms 0).
  assert (Hshape : forall r, brk_resolution_ok model req r ->
            m_halted (brk_model req r model) = None /\ m_vm_lazy (brk_model req r model) = []).
  { intros r Hr.
    destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr))
      as (_ & Hh' & _ & _ & Hlazy'). rewrite Hlazy in Hlazy'. split; assumption. }
  apply (node_svc segs scfg ms model x8 {r : word | brk_adm model req r}
           (fun i => brk_eff ms model (proj1_sig i))
           (fun i => brk_model req (proj1_sig i) model)
           (fun _ => []) Hh Hsvc).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r [Hr Hf]]. cbn [proj1_sig].
    destruct (sc_alloc scfg) eqn:Ealloc.
    + apply not_spurious_on. rewrite (injected_family_off_alloc scfg _ 214%Z);
        [rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
    + destruct (brk_refusal_b model req r) eqn:Eref.
      * apply not_spurious_forced. intros eff' m' evs' Hspec.
        apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec.
        destruct Hspec as (_ & _ & Hok' & _).
        rewrite (refusal_b_brk_ms ms x8 model _ Hno). apply (Hf eq_refl eq_refl). exact Hok'.
      * apply not_spurious_nonrefusal. unfold brk_eff. cbn [eff_ret].
        rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Eref.
  - intros eff m' ev Hspec.
    pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hspec) as (Heff & -> & Hok & ->).
    fold req in Heff, Hok.
    assert (Hmem : brk_adm model req (eff_ret eff) ->
              exists i : {r : word | brk_adm model req r},
                eff = brk_eff ms model (proj1_sig i) /\ brk_model req (eff_ret eff) model = brk_model req (proj1_sig i) model /\ ([] : list event) = []).
    { intros Hadm. exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. unfold brk_eff.
      split; [exact Heff | split; reflexivity]. }
    destruct (sc_alloc scfg) eqn:Ealloc.
    + left. apply Hmem. split; [exact Hok | intros E; rewrite Ealloc in E; discriminate E].
    + destruct (brk_refusal_b model req (eff_ret eff)) eqn:Eref.
      * (* [comment removed for export] *)
        assert (Hrq : negb (w_is0 req) = true /\ (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps model)))%Z = false
                      /\ bv_eqb req (vm_brk (m_vmmaps model)) = false /\ eff_ret eff = vm_brk (m_vmmaps model)).
        { unfold brk_refusal_b in Eref. cbv zeta in Eref.
          apply andb_true_iff in Eref as [Eref E4]. apply andb_true_iff in Eref as [Eref E3].
          apply andb_true_iff in Eref as [E1 E2].
          apply negb_true_iff in E2. apply negb_true_iff in E3. apply bv_eqb_eq in E4. auto. }
        destruct Hrq as (E1 & E2 & E3 & E4).
        destruct (Mmap.brk_r_ok model req req) eqn:Egrant.
        -- right. split; [| apply (proj1 (Hshape _ Hok))].
           apply (spurious_intro scfg (sys_input segs ms x8) model eff (brk_eff ms model req)
                    (brk_model req req model) []).
           ++ rewrite (injected_family_off_alloc scfg _ 214%Z);
                [rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
           ++ rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Eref.
           ++ apply (brk_ok_intro segs ms x8 model req Hno). exact Egrant.
           ++ unfold brk_eff. cbn [eff_ret]. rewrite (refusal_b_brk_ms ms x8 model _ Hno).
              unfold brk_refusal_b. cbv zeta. fold req. rewrite E3. apply andb_false_r.
        -- left. apply Hmem. split; [exact Hok|]. intros _ _ r' Hr'.
           destruct (brk_r_ok_cases model req r' Hr') as [-> | ->].
           ++ unfold brk_refusal_b. cbv zeta. fold req. rewrite E2, E3, bv_eqb_refl.
              destruct (w_is0 req); [discriminate E1 | reflexivity].
           ++ unfold brk_resolution_ok in Hr'. rewrite Egrant in Hr'. discriminate Hr'.
      * left. apply Hmem. split; [exact Hok|]. intros _ E. rewrite Eref in E. discriminate E.
  - apply brk_no_unmodeled. exact Hno.
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply (proj1 (Hshape r Hr)).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply (proj2 (Hshape r Hr)).
Qed.

(* [comment removed for export] *)
Lemma brk_adm_query : forall model r,
  brk_adm model (Z_to_bv 64 0) r <-> r = vm_brk (m_vmmaps model).
Proof.
  intros model r. unfold brk_adm, brk_resolution_ok, Mmap.brk_r_ok, brk_refusal_b. cbv zeta.
  unfold w_is0. rewrite bv_eqb_refl. cbn [orb negb andb]. rewrite bv_eqb_eq. split.
  - intros [H _]. exact H.
  - intros H. split; [exact H | intros _ E; discriminate E].
Qed.

(* [comment removed for export] *)
Lemma srz_brk_query_at : forall ms model x8 K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] [])))
                             model) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 K Hh Hlazy Hsvc Hno H0 Hc.
  assert (Hq : brk_adm model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (rewrite H0; apply brk_adm_query; reflexivity).
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ _ Hq) (node_brk ms model x8 Hh Hlazy Hsvc Hno)
           ltac:(rob_mf Hno)).
  intros [r Hr]. cbn [proj1_sig].
  assert (Er : r = vm_brk (m_vmmaps model)) by (apply (brk_adm_query model); rewrite <- H0; exact Hr). subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  exact Hc.
Qed.

Lemma rz_brk_query : forall regs (pc : word) mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w K HF HE Hh Hlazy H17 H10 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (srz_brk_query_at _ model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 |].
  rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_adm_grow_cases : forall m req r,
  let h := m_vmmaps m in
  sc_alloc scfg = false ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) < bv_unsigned req)%Z ->
  brk_adm m req r <->
  r = (if Mmap.brk_grow_ok m req req then req else vm_brk h).
Proof.
  intros m req r. cbv zeta. intros Halloc Hs Hb.
  set (b := vm_brk (m_vmmaps m)) in *.
  pose proof (proj1 (bv_unsigned_in_range 64 b)) as Hb0.
  assert (Hpos : (0 < bv_unsigned req)%Z) by lia.
  assert (Hble : (bv_unsigned b <= bv_unsigned req)%Z) by lia.
  assert (Hneq : bv_eqb req b = false).
  { apply bv_eqb_neq. intros E. rewrite E in Hb. lia. }
  assert (Href : forall r', brk_refusal_b m req r' = bv_eqb r' b).
  { intros r'. unfold brk_refusal_b. cbv zeta. fold b. unfold min_brk.
    replace (w_is0 req) with false
      by (symmetry; unfold w_is0, bv_eqb; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; apply Z.eqb_neq; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hneq. reflexivity. }
  pose proof (fun r' => brk_r_ok_grow_cases m req r' Hpos Hs Hble) as Hcases. cbv zeta in Hcases. fold b in Hcases.
  unfold brk_adm. rewrite (Hcases r).
  destruct (Mmap.brk_grow_ok m req req) eqn:Eg; split.
  - intros [[-> | [-> _]] Hf]; [| reflexivity].
    exfalso.
    assert (E1 : brk_refusal_b m req b = true) by (rewrite Href; apply bv_eqb_refl).
    assert (E2 : brk_refusal_b m req req = true).
    { apply (Hf Halloc E1 req). apply (proj2 (Hcases req)). right. split; [reflexivity | first [exact Eg | reflexivity]]. }
    rewrite Href, Hneq in E2. discriminate E2.
  - intros ->. split; [right; split; [reflexivity | first [exact Eg | reflexivity]]|]. rewrite Href, Hneq. intros _ E. discriminate E.
  - intros [[-> | [-> Habs]] _]; [reflexivity | rewrite ?Eg in Habs; discriminate Habs].
  - intros ->. split; [left; reflexivity|]. intros _ _ r' Hr'. rewrite Href.
    destruct (proj1 (Hcases r') Hr') as [-> | [-> Habs]]; [apply bv_eqb_refl | rewrite ?Eg in Habs; discriminate Habs].
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite Hureq.
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Zplus_mod, Hbal, Hdal; reflexivity]).
  unfold brk_page_range. rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned b + d))) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (Z_to_bv 64 (bv_unsigned b)) with b
    by (apply bv_eq; rewrite u64_lit by lia; reflexivity).
  replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_brk_grow_at : forall ms model x8 (d : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  sc_alloc scfg = false ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  ms_gpr ms 0 = Z_to_bv 64 (bv_unsigned b + d) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false ->
   srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU b [] [] [] [] []))) model) K) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms
                                 (mkEffectU (Z_to_bv 64 (bv_unsigned b + d)) [] [(b, Z_to_bv 64 d)] [] [] [])))
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 d K Hh Hlazy Hsvc Hno Halloc h b Hbal Hdal Hd Hb0 Hnw Hs H0 HA HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hcases : forall r, brk_adm model (ms_gpr ms 0) r <-> r = (if Mmap.brk_grow_ok model req req then req else b)).
  { intros r. rewrite H0. apply (brk_adm_grow_cases model req r Halloc); fold h; fold b; rewrite Hureq; lia. }
  set (r0 := if Mmap.brk_grow_ok model req req then req else b).
  assert (Hr0 : brk_adm model (ms_gpr ms 0) r0) by (apply Hcases; reflexivity).
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ r0 Hr0) (node_brk ms model x8 Hh Hlazy Hsvc Hno)
           ltac:(rob_mf Hno)).
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  destruct (Mmap.brk_grow_ok model req req) eqn:Eg.
  - (* [comment removed for export] *)
    assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    assert (Hreq0 : req <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    apply HB. first [exact Eg | reflexivity].
  - (* [comment removed for export] *)
    fold b. rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
    apply HA. first [exact Eg | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow : forall regs (pc : word) mem model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  sc_alloc scfg = false ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false ->
   srealizes segs scfg (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w d K HF HE Hh Hlazy H17 Halloc h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (srz_brk_grow_at (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17) d K
           Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Halloc Hbal Hdal Hd Hb0 Hnw Hs
           ltac:(rewrite ms_gpr_epend0; exact H10)).
  - intros Eg. rewrite adv_ret_epend. apply HA. exact Eg.
  - intros Eg. rewrite adv_zeros1_epend. apply HB. exact Eg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_ret_in_mmap : forall r, errno_ret_in mmap_errnos r = bv_eqb r (errno_ret ENOMEM).
Proof. intros r. unfold errno_ret_in, mmap_errnos. cbn [existsb]. apply orb_false_r. Qed.

Lemma errno_ret_in_mprotect : forall r, errno_ret_in mprotect_errnos r = bv_eqb r (errno_ret ENOMEM).
Proof. intros r. unfold errno_ret_in, mprotect_errnos. cbn [existsb]. apply orb_false_r. Qed.

(* [comment removed for export] *)
Lemma node_chk_grant_only : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off scfg (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
       (exists i, eff = effs i /\ m' = ms' i /\ evs = [])
    \/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs scfg (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' i0 Hh Hsvc Hoff Hok Hnr Hinv Hnu Hh' Hlazy.
  apply (node_chk_sp segs scfg ms model x8 I effs ms' Hh Hsvc Hok).
  - intros i. apply not_spurious_nonrefusal. apply Hnr.
  - intros eff m' evs Hc. destruct (Hinv eff m' evs Hc) as [Hm | [Hr Hhm]]; [left; exact Hm | right].
    split; [| exact Hhm].
    apply (spurious_intro scfg _ model eff (effs i0) (ms' i0) []); [exact Hoff | exact Hr | | apply Hnr].
    apply check_syscall_ok_iff. apply Hok.
  - exact Hnu.
  - exact Hh'.
  - exact Hlazy.
Qed.

Lemma injected_family_off_222 : forall ms x8,
  bv_unsigned x8 = 222%Z -> sc_alloc scfg = false ->
  injected_family_off scfg (sys_input segs ms x8) = true.
Proof.
  intros ms x8 Hno Halloc. rewrite (injected_family_off_alloc scfg _ 222%Z);
    [rewrite Halloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
Qed.

Lemma injected_family_off_226 : forall ms x8,
  bv_unsigned x8 = 226%Z -> sc_alloc scfg = false ->
  injected_family_off scfg (sys_input segs ms x8) = true.
Proof.
  intros ms x8 Hno Halloc. rewrite (injected_family_off_alloc scfg _ 226%Z);
    [rewrite Halloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto 6].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Definition grant_ok_na_pin (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a.

Lemma grant_ok_na_pin_unpack : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  grant_ok_na_pin hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n Hn Hnal H.
  exact (linux_place_is_admissible _ _ _ _ _ Hn Hnal H).
Qed.

(* [comment removed for export] *)
Lemma grant_ok_na_of_place : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  grant_ok_na hint m a n = true.
Proof.
  intros hint m a n Hn Hnal H.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal H) as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok_na. rewrite H, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Htop).
  reflexivity.
Qed.
Lemma grant_ok_na_place : forall hint m a n,
  grant_ok_na hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. tauto.
Qed.
Lemma grant_ok_grant_ok_na : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok in H. unfold grant_ok_na.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. destruct H as [[[[_ H1] H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma grant_na_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg. destruct (grant_ok_na_unpack _ _ _ _ Hg) as (_ & _ & Htop & _).
  apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_noaccess_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  check_syscall (sys_input segs ms x8) eff model
  = let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
             then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5) Hdecl.
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  (* [comment removed for export] *)
  destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model)) (ms_gpr ms 0)
              (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r) eqn:Hpl; [|reflexivity].
  (* [comment removed for export] *)
  assert (Hn1 : (0 < bv_unsigned (ms_gpr ms 1))%Z).
  { pose proof (u64_range (ms_gpr ms 1)) as Hr.
    assert (Hne : bv_unsigned (ms_gpr ms 1) <> 0%Z)
      by (intro Z0; apply H1, bv_eq; rewrite Z0; reflexivity).
    lia. }
  pose proof (page_round_up_Z_ge (bv_unsigned (ms_gpr ms 1))) as Hge.
  destruct (grant_ok_na_pin_unpack (ms_gpr ms 0) model r
              (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))
              ltac:(lia) (Placement.page_round_up_Z_aligned _) Hpl)
    as (Hal & Hpos & Htop & Hfree).
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
          (proj2 (Z.leb_le _ _) Htop), Hfree.
  cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_mmap_noaccess : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  (exists a, grant_ok_na (ms_gpr ms 0) model a n = true) ->
  node_ok segs scfg (mkCfg ms model)
          {a : word | grant_ok_na (ms_gpr ms 0) model a n = true}
          (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [(proj1_sig i, Z_to_bv 64 n)] [] [])))
                          (noaccess_model (proj1_sig i) (Z_to_bv 64 n) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Halloc n [a0 Ha0].
  pose proof (fun eff => mmap_noaccess_check ms x8 model eff Hno Hargs Hdecl) as Hchk. cbv zeta in Hchk. fold n in Hchk.
  assert (Hn0 : (0 <= n)%Z) by (unfold n; apply page_round_up_Z_nonneg; apply (proj1 (bv_unsigned_in_range 64 _))).
  apply (node_chk_grant_only ms model x8 {a : word | grant_ok_na (ms_gpr ms 0) model a n = true}
           (fun i => mkEffectU (proj1_sig i) [] [] [(proj1_sig i, Z_to_bv 64 n)] [] [])
           (fun i => noaccess_model (proj1_sig i) (Z_to_bv 64 n) model)
           (exist _ a0 Ha0) Hh Hsvc (injected_family_off_222 ms x8 Hno Halloc)).
  - intros [a Ha]. cbn [proj1_sig]. rewrite Hchk, (grant_na_not_errno _ _ _ _ Hn0 Ha), Ha.
    cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros [a Ha]. cbn [proj1_sig eff_ret].
    rewrite (refusal_b_mmap (sys_input segs ms x8) model a) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite <- errno_ret_in_mmap. exact (grant_na_not_errno _ _ _ _ Hn0 Ha).
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Er.
    + destruct us; [|discriminate]. injection Hc as <- <-. right. cbn [eff_ret].
      rewrite (refusal_b_mmap (sys_input segs ms x8) model r) by (rewrite in_sysno_sys_input; exact Hno).
      rewrite <- errno_ret_in_mmap. split; [exact Er | exact Hh].
    + destruct (grant_ok_na (ms_gpr ms 0) model r n) eqn:Hg; [|discriminate].
      destruct (listNN_eqb us [(r, Z_to_bv 64 n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
      left. exists (exist _ r Hg). repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
    destruct (grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)])%bool; discriminate.
  - intros [a Ha]; cbn [proj1_sig]. unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
  - intros [a Ha]; cbn [proj1_sig]. unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.

Lemma srz_mmap_noaccess_at : forall ms model x8 K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  (exists a, grant_ok_na (ms_gpr ms 0) model a n = true) ->
  (forall a, grant_ok_na (ms_gpr ms 0) model a n = true ->
     srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] [])))
                                (noaccess_model a (Z_to_bv 64 n) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 K Hh Hlazy Hsvc Hno Hargs Hdecl Halloc n Hex HK.
  destruct Hex as [a0 Ha0].
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ a0 Ha0)
           (node_mmap_noaccess ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Halloc (ex_intro _ a0 Ha0))
           ltac:(rob_mf Hno)).
  intros [a Ha]. cbn [proj1_sig]. apply HK. exact Ha.
Qed.

Lemma rz_mmap_noaccess : forall regs (pc : word) mem model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z len) = false ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na (getr regs 10) model a n = true) ->
  (forall a, grant_ok_na (getr regs 10) model a n = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (unfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (noaccess_model a (Z_to_bv 64 n) model)) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hdecl Halloc n Hex HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  pose proof (srz_mmap_noaccess_at ms model (getr regs 17) KB Hh Hlazy eq_refl
                ltac:(rewrite H17; apply u64_lit; lia) Hargs
                ltac:(rewrite H0, Hu1; exact Hdecl) Halloc) as H.
  cbv zeta in H. rewrite Hu1, H0 in H. fold n in H. apply H; [exact Hex|].
  intros a Ha. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hvd Hna Hma.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hvd. cbn [negb]. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| first [reflexivity | destruct (errno_ret_in mprotect_errnos r); reflexivity]].
  destruct cs; [| first [reflexivity | destruct (errno_ret_in mprotect_errnos r); reflexivity]].
  destruct ci; [| first [reflexivity | destruct (errno_ret_in mprotect_errnos r); reflexivity]].
  reflexivity.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srz_mprotect_at : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  sc_alloc scfg = false ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (* [comment removed for export] *)
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                             (mprotect_model addr n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno Halloc H0 Hal H1 Hlen Hnw H2 n Hvd Hna Hma Hbud HK.
  pose proof (fun eff => mprotect_check ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hvd Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  apply (srz_cases1 segs scfg (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                           (mprotect_model addr n model)) K tt).
  3:{ intros []. exact HK. }
  2:{ rob_mf Hno. }
  apply (node_chk_grant_only ms model x8 unit (fun _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])
           (fun _ => mprotect_model addr n model) tt Hh Hsvc (injected_family_off_226 ms x8 Hno Halloc)).
  - intros []. rewrite Hchk, errno_ret_in_mprotect.
    replace (bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM)) with false by (symmetry; apply bv_eqb_neq; discriminate).
    unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. cbn [eff_ret]. rewrite (refusal_b_mprotect (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
    apply bv_eqb_neq. discriminate.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r) eqn:Er.
    + destruct zs; [|discriminate]. injection Hc as <- <-. right. cbn [eff_ret].
      rewrite (refusal_b_mprotect (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
      rewrite <- errno_ret_in_mprotect. split; [exact Er | exact Hh].
    + cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. left. exists tt. repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
    cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
  - intros []. unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh.
  - intros []. unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.

Lemma rz_mprotect : forall regs (pc : word) mem model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  sc_alloc scfg = false ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) (seg_rom segs))
                       (mprotect_model addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w addr len KB HF HE Hh Hlazy H17 Halloc H10 Hal H11 Hlen Hnw H12 n Hvd Hna Hma Hbud HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (srz_mprotect_at (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17) addr len KB
           Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Halloc
           ltac:(rewrite ms_gpr_epend0; exact H10) Hal
           ltac:(rewrite ms_gpr_epend1; exact H11) Hlen Hnw
           ltac:(rewrite ms_gpr_epend2; exact H12) Hvd Hna Hma Hbud).
  rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma srz_mprotect_blocked_at : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = false ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret ENOMEM) [] [] [] [] []))) model) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 n Hvd Hna Hma Hbud HK.
  pose proof (fun eff => mprotect_check ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hvd Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk. cbn [andb] in Hchk.
  eapply srz_silent1; [| rob_mf Hno | exact HK].
  apply (node_det segs scfg ms model x8 (mkEffectU (errno_ret ENOMEM) [] [] [] [] []) model [] Hh Hsvc).
  - intros [r ws zs us cs ci] m' evs. rewrite Hchk. split.
    + intros Hc. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er; [|discriminate].
      destruct zs; [|discriminate]. injection Hc as <- <-.
      rewrite errno_ret_in_mprotect in Er. apply bv_eqb_eq in Er. subst r. repeat split; reflexivity.
    + intros (He & -> & ->). injection He as -> -> -> -> -> ->.
      rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate | discriminate].
  - exact Hh.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma fixed_noaccess_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_noaccess_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Lemma fixed_destroyed_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_destroyed_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_fixed_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => if listNN_eqb us [(addr, n)]
                    then CheckOk (fixed_destroyed_model addr n model) []
                    else CheckReject
             end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (fixed_noaccess_model addr n model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H1' Hlen Htop n Hrf Hmc.
  pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, H0, Hu1.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 50)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  rewrite (proj2 (Z.leb_gt _ _)) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
  unfold fixed_noaccess_model, fixed_destroyed_model, with_mmap_replacement, with_mmap_backing, with_mmap_destroyed.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_noaccess_at : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_fixed_args_ok ms ->
  sc_alloc scfg = false ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                             (fixed_noaccess_model addr n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno Hargs Halloc H0 Hal Hpos H1 Hlen Htop n Hrf Hmc HK.
  pose proof (fun eff => mmap_fixed_check ms x8 model eff addr len Hno Hargs H0 Hal Hpos H1 Hlen Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Hne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|].
    pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  apply (srz_cases1 segs scfg (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                           (fixed_noaccess_model addr n model)) K tt).
  3:{ intros []. exact HK. }
  2:{ rob_mf Hno. }
  apply (node_chk_grant_only ms model x8 unit (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
           (fun _ => fixed_noaccess_model addr n model) tt Hh Hsvc (injected_family_off_222 ms x8 Hno Halloc)).
  - intros []. rewrite Hchk, Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite <- errno_ret_in_mmap. exact Hne.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Er.
    + right. cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
      rewrite <- errno_ret_in_mmap. split; [exact Er|].
      destruct us; [injection Hc as <- <-; exact Hh|].
      destruct (listNN_eqb _ _); [|discriminate]. injection Hc as <- <-.
      unfold fixed_destroyed_model. rewrite vm_forget_range_halted, with_vmmaps_halted. exact Hh.
    + destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
      left. exists tt. repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate | destruct (listNN_eqb _ _); discriminate]|].
    destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
  - intros []. unfold fixed_noaccess_model. rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
  - intros []. unfold fixed_noaccess_model. apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.

Lemma rz_mmap_fixed_noaccess : forall regs (pc : word) mem model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  sc_alloc scfg = false ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                       (fixed_noaccess_model addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w addr len KB HF HE Hh Hlazy H17 Halloc H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc HB.
  pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  apply (srz_mmap_fixed_noaccess_at ms model (getr regs 17) addr len KB Hh Hlazy eq_refl
           ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc
           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc).
  unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs scfg (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  assert (Hnode : node_ok segs scfg (mkCfg ms model) tid_I (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
  { apply (node_chk segs scfg ms model x8 tid_I effs (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
    - intros [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
      rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
    - intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
    - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
    - intros i. rewrite with_tid_halted. exact Hh.
    - intros i. rewrite with_tid_lazy. exact Hlazy.
    - intros i. apply not_spurious_on. apply injected_family_off_none. rewrite in_sysno_sys_input, Hno. exact injected_arm_96. }
  destruct Hnode as [Hfw Hbw]. split.
  - intros i. rewrite Enx. apply Hfw.
  - intros e st Hss. destruct (Hbw e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

Lemma srz_set_tid_at : forall ms model x8 K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms tid)) (with_tid tid model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 K Hh Hlazy Hsvc Hno Htid Hk.
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ (Z_to_bv 64 1) one_tid_ok)
           (node_set_tid ms model x8 Hh Hlazy Hsvc Hno Htid)
           ltac:(rob_mf Hno)).
  intros [t Ht]. cbn [proj1_sig]. apply Hk. exact Ht.
Qed.

Lemma rz_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (srz_set_tid_at _ model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid |].
  intros t Ht. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned b + d <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
  (vm_backing_used m + d <= vm_limit h)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Htop Hrf Hlive.
  pose proof (u64_range b) as Hbr.
  assert (Htb : (alloc_top h < 2 ^ 64)%Z) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok, Mmap.brk_grow_bytes. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
  replace (Z.max 0 (bv_unsigned b + d - bv_unsigned b))%Z with d by lia.
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_admissible_init : forall reserved (brk0 mbase sp : word) lim (model : Model) d,
  (reserved_top reserved <= bv_unsigned brk0)%Z ->
  (bv_unsigned brk0 mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned brk0)%Z ->
  (bv_unsigned brk0 + d <= alloc_top (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp))%Z ->
  (d <= lim)%Z ->
  m_vmmaps model = mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp ->
  m_vm_lazy model = [] -> m_vm_materialized model = [] ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned brk0 + d)) (Z_to_bv 64 (bv_unsigned brk0 + d)) = true.
Proof.
  intros reserved brk0 mbase sp lim model d Htop Hbal Hdal Hd Hb0 Hce Hlim Hvm Hlz Hmt.
  pose proof (brk_grow_ok_aligned_intro model d) as H. cbv zeta in H. rewrite Hvm in H. cbn -[alloc_top Z_to_bv bv_unsigned Z.add Z.modulo region_free] in H.
  apply H; try assumption; try lia.
  - rewrite app_nil_r. apply region_free_above_top. exact Htop.
  - rewrite vm_backing_used_simple by assumption. rewrite Hvm. cbn. lia.
Qed.

End WithSegs.
End FPX_1.

Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  rewrite map_remove_skip by (apply (H b s); left; reflexivity).
  rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : forall data (off count : word),
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : forall data (off count : word),
  (length (file_read data off count) <= word_to_nat count)%nat
  /\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cand (base N : Z) (j : nat) : Z := base + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma cand_spacing : forall base N j k, 0 <= N -> (j < k)%nat -> cand base N j + 2 * N <= cand base N k.
Proof. intros base N j k HN H. unfold cand. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : forall base N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand base N j) n p -> zconflict (cand base N k) n p -> j = k.
Proof.
  intros base N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing base N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing base N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* j removed; nothing else in js satisfies P *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : forall (base N n : Z) (l : list (word * word)) (js : list nat),
  0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  List.NoDup js -> (length l < length js)%nat ->
  exists j, In j js /\ forall p, In p l -> ~ zconflict (cand base N j) n p.
Proof.
  intros base N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand base N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique base N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.

Lemma region_free_of_noconflict : forall l (a n : Z),
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall p, In p l -> ~ zconflict a n p) ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
  cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  rewrite !u64_lit by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_na_gen : forall hint (m : Model) (N n C base : Z),
  0 < N -> N mod page_size = 0 -> 0 < n <= N -> n mod page_size = 0 ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  base mod page_size = 0 -> task_unmapped_base <= base ->
  base + C * (2 * N) + N <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na hint m a n = true.
Proof.
  intros hint m N n C base HN HNal Hn Hnal Hsz Hcnt Hbal Hb0 Hband.
  pose proof (proj1 (Z.ltb_lt _ _) (eq_refl : (0 <? task_unmapped_base)%Z = true)) as Htub.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate base N n l (seq 0 (S (length l))) ltac:(lia) Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htl. unfold two_pow_64 in Htl.
  assert (Hc : base <= cand base N j <= base + C * (2 * N)) by (unfold cand; nia).
  assert (E1 : cand base N j mod page_size = 0).
  { unfold cand. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal, Hbal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  generalize dependent (cand base N j). intros c Hfree Hc E1.
  assert (G : 0 <= c < 2 ^ 64 /\ (0 <= n < 2 ^ 64 /\ (0 < c /\ (c + n <= alloc_top (m_vmmaps m) /\ c + n < 2 ^ 64)))).
  { clear Hfree Hsz E1 HNal Hbal Hnal. generalize dependent (alloc_top (m_vmmaps m)). intros top Hband Htl. nia. }
  destruct G as (G0 & G1 & G2 & G3 & G4).
  assert (Hgf : gap_fits l task_unmapped_base (alloc_top (m_vmmaps m)) n c).
  { unfold gap_fits. split; [exact E1|]. split; [lia|]. split; [exact G3|].
    exact (region_free_of_noconflict l c n (proj1 G0) (proj1 G1) G4 Hfree). }
  assert (Hnpos : 0 < n) by lia.
  destruct (linux_place_exists (m_vmmaps m) (kb_thp (m_kernel m)) hint n Hnpos Hnal
              (ex_intro _ c (or_intror Hgf))) as [a Ha].
  destruct (linux_place_admissible _ _ _ _ _ Hnpos Hnal Ha) as (Hal & Hpos & Hhi & Hfr).
  exists (Z_to_bv 64 a). apply (grant_ok_na_of_place _ _ _ _ Hnpos Hnal).
  apply (proj2 (linux_place_is_iff _ _ _ _ _ Hnpos Hnal)). rewrite u64_lit by lia. exact Ha.
Qed.

Lemma grant_exists_gen : forall hint (m : Model) (N n C base : Z),
  0 < N -> N mod page_size = 0 -> 0 < n <= N -> n mod page_size = 0 ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  base mod page_size = 0 -> task_unmapped_base <= base ->
  base + C * (2 * N) + N <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m N n C base HN HNal Hn Hnal Hsz Hcnt Hbal Hb0 Hband Hlive.
  destruct (grant_exists_na_gen hint m N n C base HN HNal Hn Hnal Hsz Hcnt Hbal Hb0 Hband) as [a Ha].
  exists a. unfold grant_ok. unfold grant_ok_na in Ha. rewrite Ha.
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alloc_top_ge_window : forall h,
  sp_window_lo <= bv_unsigned (vm_init_sp h) -> 0x7fff7f800000 <= alloc_top h.
Proof. intros h H. unfold alloc_top. rewrite stack_max_size_val. unfold sp_window_lo in H. lia. Qed.

(* [comment removed for export] *)
Lemma task_unmapped_base_val : task_unmapped_base = 183251939328.
Proof. vm_compute. reflexivity. Qed.

Lemma grant_exists : forall hint (m : Model) (n : Z),
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  0 < n <= 2 ^ 30 -> n mod page_size = 0 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hsp Hn Hnal Hsz Hcnt Hlive.
  pose proof (alloc_top_ge_window _ Hsp).
  apply (grant_exists_gen hint m (2 ^ 30) n 40000 task_unmapped_base); try assumption;
    rewrite ?task_unmapped_base_val; unfold page_size in *; lia.
Qed.

Lemma grant_exists_na : forall hint (m : Model) (n : Z),
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  0 < n <= 2 ^ 30 -> n mod page_size = 0 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  exists a, grant_ok_na hint m a n = true.
Proof.
  intros hint m n Hsp Hn Hnal Hsz Hcnt.
  pose proof (alloc_top_ge_window _ Hsp).
  apply (grant_exists_na_gen hint m (2 ^ 30) n 40000 task_unmapped_base); try assumption;
    rewrite ?task_unmapped_base_val; unfold page_size in *; lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_big : forall hint (m : Model) (n : Z),
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  0 < n <= 2 ^ 35 -> n mod page_size = 0 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000 ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hsp Hn Hnal Hsz Hcnt Hlive.
  pose proof (alloc_top_ge_window _ Hsp).
  apply (grant_exists_gen hint m (2 ^ 35) n 1000 task_unmapped_base); try assumption;
    rewrite ?task_unmapped_base_val; unfold page_size in *; lia.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  vm_limit (m_vmmaps m) < vm_backing_used m + n ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n H. unfold grant_ok.
  (* [comment removed for export] *)
  rewrite (proj2 (Z.leb_gt _ _) H). apply andb_false_r.
Qed.

End FPX_2.

End RefNodes.
Module LibWritev.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_LibWritev () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_00948RefNodes;node_of_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesCnode_chk_grant_onlyC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes;node_chk_spC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00948RefNodes5tid_IC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes8node_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions=bv_wrap_smallC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch9lookup_caC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch8ca_checkC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite<check_writevC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I47Corelib4Init9Datatypes6option00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch:CheckedArm00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch=checked_tableK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses8symmetryC59OSSVerify5KrLib7Mh_00368ShapeAlg:t_alt_wallC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init6Specif3sig01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00368ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init6Specif9proj1_sigC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnI4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_SymmetricI47Corelib4Init6Specif3sig00C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9le_word_vC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib7Mh_00387CatExecAms_read_bytes_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC59OSSVerify5KrLib7Mh_00306CatSimHread_bytes_map_read_byteC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8read_u64I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib7Mh_00949LibWritev9iov_arrayC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State@read_iovec_entryK4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry01K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic5proj2c59OSSVerify5KrLib7Mh_00949LibWritev<read_u64_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritev<bv_add_ZformC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry03K4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry02K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import01c59OSSVerify5KrLib7Mh_00949LibWritevIread_iovec_entry_of_arrayC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem5State?copy_iovecs_auxI4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import00K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import02K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import03c59OSSVerify5KrLib7Mh_00949LibWritev8iov_bufsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem5State=gather_iovecsc59OSSVerify5KrLib7Mh_00949LibWritevBread_bytes_map_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:iovs_totalC4ELinuxProcessSemantics?LinuxProcessSem5State>cap_iovecs_auxC4ELinuxProcessSemantics?LinuxProcessSem5StateAiovs_total_nonnegc59OSSVerify5KrLib7Mh_00949LibWritev>u64_roundtrip'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z5min_rc59OSSVerify5KrLib7Mh_00949LibWritev;iov_bufs_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?iovs_access_okbC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7forallbC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@access_okb_introC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes4negbC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_00949LibWritev@access_okb_of_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_00949LibWritevEiovs_access_okb_of_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritevDcopy_iovecs_of_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idc59OSSVerify5KrLib7Mh_00949LibWritev=word_to_nat_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C4ELinuxProcessSemantics?LinuxProcessSem5State=import_iovecsK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics?LinuxProcessSem5State7IOV_MAXC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z8inj_succC4ELinuxProcessSemantics?LinuxProcessSem5State<MAX_RW_COUNTI47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprc59OSSVerify5KrLib7Mh_00949LibWritev>gather_of_bufsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDgather_iovecs_lengthC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5State?addr_is_error_bC4ELinuxProcessSemantics?LinuxProcessSem5StateCiov_prefix_accessesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite8iovcnt32C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC4ELinuxProcessSemantics?LinuxProcessSem5State:cap_iovecsC4ELinuxProcessSemantics?LinuxProcessSem5StateFimport_iovecs_accessesC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State?writev_gatheredC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>rw_pos_einvalbC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite@modeled_file_gapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem2Fs:file_writeC4ELinuxProcessSemantics?LinuxProcessSem2Fs6fs_setC4ELinuxProcessSemantics?LinuxProcessSem5State7with_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>append_new_posK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall9w_is0_posc59OSSVerify5KrLib7Mh_00949LibWritev=cap_iovecs_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=gather_prefixC56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat7eqb_neqC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBgather_prefix_fullc59OSSVerify5KrLib7Mh_00949LibWritevFimport_iovecs_of_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim9in_mem_siC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idC59OSSVerify5KrLib7Mh_00437FileSim:in_arg2_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg1_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg0_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim;in_sysno_siC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritevDcheck_syscall_writevC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAaccess_ranges_eqbK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State6in_memI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTC4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0c59OSSVerify5KrLib7Mh_00949LibWritev<writev_checkC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC59OSSVerify5KrLib7Mh_00306CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7wr_fullC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDaccess_ranges_eqb_eqC49OSSVerify5KrLib5Nodes>sstep_of_checkC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos6to_natC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC49OSSVerify5KrLib5Nodes=sstep_svc_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC59OSSVerify5KrLib7Mh_00368ShapeAlg7halt_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC56Stdlib6ZArith6BinInt1Z3maxI4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C59OSSVerify5KrLib7Mh_00264Scfg?injected_arm_66C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes5ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare5at_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritevArz_writev_pendingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes6rz_sysC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc59OSSVerify5KrLib7Mh_00949LibWritev:rz_writev2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritev7rz_wallC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib7Mh_00949LibWritev:rz_writev1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg:t_write_chC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDcopy_iovecs_accessesC49OSSVerify5KrLib5NodesJrz_ret_only_copyins_silentC1?~~~~~~~~~~~~~~~".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite RomWritev.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Section FPX_1. Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
  intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.

Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma access_okb_of_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma check_syscall_writev : forall i eff m,
  bv_unsigned (in_sysno i) = 66%Z ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_alt_wall_nat : forall (ch : word) (bs : list byte) (K : TSet),
  K [] -> (1 <= length bs)%nat ->
  t_eq (t_alt (fun k : nat =>
          fun tr => (1 <= k <= length bs)%nat /\
            t_emit (map (WriteEv ch) (firstn k bs)) (t_emit (map (WriteEv ch) (skipn k bs)) K) tr))
       (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros ch bs K HK Hnb tr. rewrite <- (t_alt_wall ch bs K HK Hnb tr). unfold t_alt. split.
  - intros [k [Hk Ht]]. exists (exist _ k Hk). exact Ht.
  - intros [[k Hk] Ht]. exists k. split; [exact Hk | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma rz_wall : forall segs scfg c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  srealizes segs scfg c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  srealizes segs scfg c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs scfg c ch bs K Hnb HK H. eapply srz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma read_u64_rdn : forall ms a v,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (ms_read_byte ms) a = Some v.
Proof.
  intros ms a v Hrom H. unfold read_u64.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

Lemma read_bytes_map_rdn : forall ms a (n : word) bs,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a (word_to_nat n) = Some bs ->
  read_bytes_map (ms_read_byte ms) a n = Some bs.
Proof.
  intros ms a n bs Hrom H.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

Lemma read_iovec_entry_of_array : forall ms b n r iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov ((b, n) :: r) ->
  read_iovec_entry (ms_read_byte ms) iov = IovEntry b n.
Proof.
  intros ms b n r iov Hrom (Hb & Hn & Hlt & _). unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.

Lemma copy_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov iovs ->
  copy_iovecs_aux (ms_read_byte ms) iov (length iovs) = ImpOk iovs.
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
  cbn [length copy_iovecs_aux].
  rewrite (read_iovec_entry_of_array ms b n r iov Hrom Ha).
  destruct Ha as (_ & _ & _ & Hr).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hrom Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

Lemma gather_of_bufs : forall ms iovs bss,
  ms_rom ms = seg_rom segs ->
  iov_bufs (ms_mem ms) iovs bss ->
  gather_iovecs (ms_read_byte ms) iovs = Some (concat bss).
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.

Lemma cap_iovecs_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite u64_roundtrip', IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs_ok (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_bufs_ok r
  end.

Lemma iovs_access_okb_of_ok : forall iovs, iov_bufs_ok iovs -> iovs_access_okb iovs = true.
Proof.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.

(* [comment removed for export] *)
Lemma import_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
  intros ms iovs iov Hrom Hcnt Hok Harr Hbok. unfold import_iovecs.
  destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
  destruct r as [|[b2 n2] r2].
  - (* one entry *)
    cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
    rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array ms b n [] iov Hrom Harr).
    destruct Hbok as [Hb _]. pose proof (u64_range n).
    rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
      by (unfold MAX_RW_COUNT in *; lia).
    reflexivity.
  - (* two or more entries *)
    set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
    assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
    assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    rewrite E1, E0. rewrite u64_lit by lia.
    replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    rewrite (access_okb_of_le iov (16 * cnt)) by lia.
    rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
    rewrite (copy_iovecs_of_array ms _ iov Hrom Harr).
    rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.

Lemma writev_rob : forall ms model x8 ch iovs bs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  fd_lookup (m_fds model) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
  import_iovecs (ms_read_byte ms) (ms_gpr ms 1) (iovcnt32 (ms_gpr ms 2)) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  RomBase.sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 ch iovs bs Hs Hno Hfd Himp Hg.
  apply RomBase.sys_rob_of_check. intros r x8' Hr Hs' eff. cbn [cfg_ms] in Hs'.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_writev _ eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite RomBase.sys_input_wrom.
  change (in_arg (RomBase.with_mem (sys_input segs ms x8) (ms_read_byte (RomBase.wrom ms r))) 0)
    with (in_arg (sys_input segs ms x8) 0).
  change (in_arg (RomBase.with_mem (sys_input segs ms x8) (ms_read_byte (RomBase.wrom ms r))) 1)
    with (in_arg (sys_input segs ms x8) 1).
  change (in_arg (RomBase.with_mem (sys_input segs ms x8) (ms_read_byte (RomBase.wrom ms r))) 2)
    with (in_arg (sys_input segs ms x8) 2).
  apply (RomWritev.check_writev_chan_ext _ _ _ _ _ eff model ch iovs bs).
  - rewrite in_arg0_si. exact Hfd.
  - rewrite in_mem_si. apply RomBase.mem_ext_read_byte_wrom. exact Hr.
  - rewrite in_mem_si, in_arg1_si, in_arg2_si. exact Himp.
  - rewrite in_mem_si. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma writev_check : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  ms_rom ms = seg_rom segs ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  let tot := iovs_total iovs in
  (1 <= tot)%Z -> (tot <= rw_bytes_max)%Z -> (tot <= 2 ^ 30)%Z ->
  let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
  Z.of_nat (length bs) = tot /\
  forall eff, check_syscall (sys_input segs ms x8) eff model
    = match eff with
      | mkEffectU ret [] [] [] [] ci =>
          if (1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret)
          then if access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
               then CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
               else CheckReject
          else CheckReject
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Htmax Ht30 CA.
  pose proof (gather_of_bufs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  split; [exact Hlen|].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms x8) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false
    by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  rewrite in_mem_si, Hcnt32.
  rewrite (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
  (* [check_writev] has no [modeled_iovs_total] gate, so there is no
     [iovs_total_in_range] rewrite; [Htmax] stays a premise for the callers' sake. *)
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
  cbv beta iota zeta. fold tot.
  replace ((tot =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Hrdr. change (negb true) with false.
  assert (Hlw : bv_unsigned (len_word bs) = tot).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  cbv beta iota.
  destruct eff as [ret ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity].
  rewrite Hlen. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pending : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= rw_bytes_max)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  srealizes segs scfg (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Htmax Ht30 Hk.
  destruct (writev_check ms x8 model fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Htmax Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  3:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  2:{ assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs)))
        by (unfold iovcnt32, abi_low32; rewrite u64_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (Hcap : cap_iovecs iovs = iovs)
        by (unfold cap_iovecs; apply cap_iovecs_id; unfold MAX_RW_COUNT; try fold tot; lia).
      apply (writev_rob ms model x8 (Z_to_bv 64 fd) iovs (concat bss) Hsvc Hno).
      - rewrite H0, fd32_id by (rewrite u64_lit; lia). exact Hfd.
      - rewrite H1, H2, Hcnt32. exact (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
      - rewrite Hcap. exact (gather_of_bufs ms iovs bss Hrom Hbufs). }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  (* [comment removed for export] *)
  apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Htmax Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Htmax Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Htmax Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Htmax Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_ch : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_write_ch (Z_to_bv 64 fd) (bs1 ++ bs2) K).
Proof.
  intros. unfold t_write_ch.
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma iovec_entry_accesses_of_array : forall ms b n r iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov ((b, n) :: r) ->
  iovec_entry_accesses (ms_read_byte ms) iov = [(iov, 16%nat)].
Proof.
  intros ms b n r iov Hrom (Hb & Hn & _). unfold iovec_entry_accesses.
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn), (read_u64_rdn ms iov b Hrom Hb).
  reflexivity.
Qed.

Lemma rz_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  (0 <= rw_bytes_max)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hmax Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    exact (iovec_entry_accesses_of_array ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr). }
  assert (Hrob : RomBase.sys_rob segs (mkCfg ms model)).
  { apply (writev_rob ms model (getr regs 17) (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] [] eq_refl Hno).
    - unfold ms. rewrite ms_gpr_epend0, H10, fd32_id by (rewrite u64_lit; lia). exact Hfd.
    - unfold ms. rewrite ms_gpr_epend1, ms_gpr_epend2, H11, H12.
      change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). exact Himp.
    - reflexivity. }
  eapply (rz_ret_only_copyins_silent segs scfg ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | exact Hrob | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si, Himp, Hacc.
  (* [comment removed for export] *)
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.

End WithSegs.

End FPX_1.

End LibWritev.
Module LibWritevX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase RomWrite RomWritev.
Import ListNotations.
Open Scope bv_scope.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.LibWritev.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_LibWritevX () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_00948RefNodes;node_of_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00948RefNodesCnode_chk_grant_onlyC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes;node_chk_spC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00948RefNodes5tid_IC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes8node_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memc59OSSVerify5KrLib7Mh_00949LibWritev9iov_arrayC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritev;iov_bufs_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritev8iov_bufsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatC4ELinuxProcessSemantics?LinuxProcessSem5State:iovs_totalc59OSSVerify5KrLib7Mh_00949LibWritev>gather_of_bufsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem5State=gather_iovecsC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDgather_iovecs_lengthC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallC56Stdlib6ZArith6BinInt1Z3lebC4ELinuxProcessSemantics?LinuxProcessSem5State?addr_is_error_bC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem5StateCiov_prefix_accessesC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite<check_writevK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite8iovcnt32C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC4ELinuxProcessSemantics?LinuxProcessSem5State=import_iovecsC4ELinuxProcessSemantics?LinuxProcessSem5State:cap_iovecsC4ELinuxProcessSemantics?LinuxProcessSem5StateFimport_iovecs_accessesC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State?writev_gatheredC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>rw_pos_einvalbC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite@modeled_file_gapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem2Fs:file_writeC4ELinuxProcessSemantics?LinuxProcessSem2Fs6fs_setC4ELinuxProcessSemantics?LinuxProcessSem5State7with_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>append_new_posK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05K46Stdlib9micromega5Tauto8GFormula03C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall9w_is0_posK4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03c59OSSVerify5KrLib7Mh_00949LibWritev=cap_iovecs_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=gather_prefixC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat7eqb_neqC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBgather_prefix_fullc59OSSVerify5KrLib7Mh_00949LibWritevFimport_iovecs_of_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim9in_mem_siC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idC59OSSVerify5KrLib7Mh_00437FileSim:in_arg2_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg1_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg0_siC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib7Mh_00437FileSim;in_sysno_siC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritevDcheck_syscall_writevC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes4andbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAaccess_ranges_eqbC47Corelib5Lists7ListDef6firstnK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics?LinuxProcessSem5State6in_memC47Corelib4Init5Logic6eq_symK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFI4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import00C4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State<MAX_RW_COUNTK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:LibWritevX=writev_checkXC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC59OSSVerify5KrLib7Mh_00306CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7wr_fullC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I47Corelib4Init5Logic2ex00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDaccess_ranges_eqb_eqC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith4Znat5Nat2Z2idC49OSSVerify5KrLib5Nodes>sstep_of_checkC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos6to_natC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib7Mh_00949LibWritev>u64_roundtrip'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib5Nodes=sstep_svc_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC59OSSVerify5KrLib7Mh_00368ShapeAlg7halt_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC47Corelib4Init6Specif9proj1_sigK47Corelib4Init6Specif3sig01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00C59OSSVerify5KrLib7Mh_00264Scfg?injected_arm_66C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes5ependC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare5at_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:LibWritevXBrz_writev_pendingXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0094:AgentNodes6rz_sysC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib5Lists4List:length_appC47Corelib5Lists7ListDef5skipnC49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc59OSSVerify5KrLib7Mh_0094:LibWritevX;rz_writev2XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritev7rz_wallC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib7Mh_0094:LibWritevX;rz_writev1XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg:t_write_chC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC4ELinuxProcessSemantics?LinuxProcessSem5State@read_iovec_entryC56Stdlib6ZArith6BinInt1Z3minC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State?copy_iovecs_auxC4ELinuxProcessSemantics?LinuxProcessSem5State?iovs_access_okbK4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry01c59OSSVerify5KrLib7Mh_00949LibWritev@access_okb_of_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00949LibWritevIread_iovec_entry_of_arrayC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC4ELinuxProcessSemantics?LinuxProcessSem5StateDcopy_iovecs_accessesC56Stdlib6ZArith6BinInt1Z5min_rC4ELinuxProcessSemantics?LinuxProcessSem5State>cap_iovecs_auxC49OSSVerify5KrLib5NodesJrz_ret_only_copyins_silentC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import02I4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry00K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import03C4ELinuxProcessSemantics?LinuxProcessSem5State7IOV_MAX".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma writev_checkX : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  ms_rom ms = seg_rom segs ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  let tot := iovs_total iovs in
  (1 <= tot)%Z -> (tot <= 2 ^ 30)%Z ->
  let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
  Z.of_nat (length bs) = tot /\
  forall eff, check_syscall (sys_input segs ms x8) eff model
    = match eff with
      | mkEffectU ret [] [] [] [] ci =>
          if (1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret)
          then if access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
               then CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
               else CheckReject
          else CheckReject
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model fd iov iovs bss Hrom Hfd Hcr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Ht30 CA.
  pose proof (gather_of_bufs segs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  split; [exact Hlen|].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms x8) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold check_writev. rewrite Hfd, Hcr. cbn [negb].
  replace (w_is0 (Z_to_bv 64 fd)) with false
    by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  rewrite in_mem_si, Hcnt32.
  rewrite (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok).
  (* [comment removed for export] *)
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
  cbv beta iota zeta. fold tot.
  replace ((tot =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  assert (Hlw : bv_unsigned (len_word bs) = tot).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  cbv beta iota.
  destruct eff as [ret ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity].
  rewrite Hlen. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pendingX : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  srealizes segs scfg (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hcr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Ht30 Hk.
  destruct (writev_checkX ms x8 model fd iov iovs bss Hrom Hfd Hcr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  3:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  2:{ assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs)))
        by (unfold iovcnt32, abi_low32; rewrite u64_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (Hcap : cap_iovecs iovs = iovs)
        by (unfold cap_iovecs; apply cap_iovecs_id; unfold MAX_RW_COUNT; try fold tot; lia).
      apply (writev_rob segs ms model x8 (Z_to_bv 64 fd) iovs (concat bss) Hsvc Hno).
      - rewrite H0, fd32_id by (rewrite u64_lit; lia). exact Hfd.
      - rewrite H1, H2, Hcnt32. exact (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok).
      - rewrite Hcap. exact (gather_of_bufs segs ms iovs bss Hrom Hbufs). }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  (* [comment removed for export] *)
  apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2X : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hcr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pendingX (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hcr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1X : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hcr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pendingX (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hcr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_wallX : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hcr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2X regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wallX : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hcr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1X regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_chX : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_write_ch (Z_to_bv 64 fd) (bs1 ++ bs2) K).
Proof.
  intros. unfold t_write_ch.
  eapply (rz_writev2X regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_writev1_zeroX : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hcr Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    exact (iovec_entry_accesses_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr). }
  assert (Hrob : RomBase.sys_rob segs (mkCfg ms model)).
  { apply (writev_rob segs ms model (getr regs 17) (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] [] eq_refl Hno).
    - unfold ms. rewrite ms_gpr_epend0, H10, fd32_id by (rewrite u64_lit; lia). exact Hfd.
    - unfold ms. rewrite ms_gpr_epend1, ms_gpr_epend2, H11, H12.
      change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). exact Himp.
    - reflexivity. }
  eapply (rz_ret_only_copyins_silent segs scfg ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | exact Hrob | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si, Himp, Hacc.
  (* [comment removed for export] *)
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.

End WithSegs.

End FPX_1.
End LibWritevX.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State. From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
Module RefPrintfLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma alu_add_Z : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 a + Z_to_bv 64 b)%bv.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma alu_and3_Z : forall a, 0 <= a ->
  alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3) = Z_to_bv 64 (a mod 4).
Proof.
  intros a Ha. apply bv_eq.
  change (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3)) with (bv_and (Z_to_bv 64 a) (Z_to_bv 64 3)).
  rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (3 mod 2 ^ 64) with (Z.ones 2). rewrite Z.land_ones by lia.
  change (2 ^ 2) with 4.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma bt_eq0_Z : forall a, 0 <= a < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 0) = (a =? 0).
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma bt_ne0_Z : forall a, 0 <= a < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 0) = negb (a =? 0).
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bt_and3 : forall c (w k : Z) (t : bool), 0 <= w + k ->
  match c with BC_EQ => ((w + k) mod 4 =? 0) = t | BC_NE => negb ((w + k) mod 4 =? 0) = t | _ => False end ->
  branch_taken c (alu64 ALU_AND (alu64 ALU_ADD (Z_to_bv 64 w) (Z_to_bv 64 k)) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
  intros c w k t Hw Hc. rewrite alu_add_Z, alu_and3_Z by lia.
  pose proof (Z.mod_pos_bound (w + k) 4 ltac:(lia)).
  destruct c; try contradiction.
  - rewrite bt_eq0_Z by lia. exact Hc.
  - rewrite bt_ne0_Z by lia. exact Hc.
Qed.

Lemma bt_and3_0 : forall c (w : Z) (t : bool), 0 <= w ->
  match c with BC_EQ => (w mod 4 =? 0) = t | BC_NE => negb (w mod 4 =? 0) = t | _ => False end ->
  branch_taken c (alu64 ALU_AND (Z_to_bv 64 w) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
  intros c w t Hw Hc. rewrite alu_and3_Z by lia.
  pose proof (Z.mod_pos_bound w 4 ltac:(lia)).
  destruct c; try contradiction.
  - rewrite bt_eq0_Z by lia. exact Hc.
  - rewrite bt_ne0_Z by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rdn_2 : forall segs m (a : word) b0 b1,
  (bv_unsigned a + 2 <= 2 ^ 64)%Z ->
  rdn segs m a 1 = Some [b0] -> rdn segs m (Z_to_bv 64 (bv_unsigned a + 1)) 1 = Some [b1] ->
  rdn segs m a 2 = Some [b0; b1].
Proof.
  intros segs m a b0 b1 Hnw H0 H1. cbn [rdn] in *.
  destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [x|]; [|discriminate].
  injection H0 as ->.
  replace (a + 1)%bv with (Z_to_bv 64 (bv_unsigned a + 1)).
  2:{ apply bv_eq. rewrite u64_lit by (pose proof (u64_range a); lia). symmetry. apply u_add1. lia. }
  destruct (match m (Z_to_bv 64 (bv_unsigned a + 1)) with Some b => Some b | None => seg_rom segs _ end) as [y|];
    [|discriminate].
  injection H1 as ->. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lin_neg1_val : forall (x : word) c,
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c) = Z_to_bv 64 (c - bv_unsigned x).
Proof.
  intros x c. apply bv_eq.
  change (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c))
    with ((Z_to_bv 64 (-1) * x) + Z_to_bv 64 c)%bv.
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  rewrite <- Z.add_mod by lia.
  replace ((2 ^ 64 - 1) * bv_unsigned x + c) with ((c - bv_unsigned x) + bv_unsigned x * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma bt_geu_Z : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Hab Ha. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
  apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.

Lemma bt_geu_Z_false : forall a b, 0 <= a < b -> b < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b Hab Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
  apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.

Lemma bt_ltu_Z : forall a b (t : bool), 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  (a <? b) = t -> branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = t.
Proof. intros a b t Ha Hb Ht. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia. exact Ht. Qed.
End FPX_2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_3. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma mod4_shift : forall w k r, w mod 4 = r -> (w + k) mod 4 = (r + k) mod 4.
Proof. intros w k r H. rewrite <- Zplus_mod_idemp_l, H. reflexivity. Qed.

Lemma even_mod4 : forall w, w mod 2 = 0 -> w mod 4 = 0 \/ w mod 4 = 2.
Proof. intros w H. lia. Qed.

Lemma mod4_cases : forall w, w mod 4 = 0 \/ w mod 4 = 1 \/ w mod 4 = 2 \/ w mod 4 = 3.
Proof. intros w. lia. Qed.
End FPX_3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

End RefPrintfLib.
