(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (v_lui_4096, c_lts_0_0, write_to_mem_below and 5 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import ExitSim PropExec CatSim CatExec SeqExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_StreamExec () := "K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib2AS7CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib2AS7CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib2AS7CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib2AS:StreamExecBwrite_to_mem_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01c59OSSVerify5KrLib2AS:StreamExecBwrite_to_mem_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib2AS7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib2AS8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K45stdpp9bitvector;definitions2bv01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib2AS8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC45stdpp9bitvector;definitions4BvWfI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesc59OSSVerify5KrLib2AS:StreamExec?adv_apply_writeC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write_to_mem_below : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  (bv_unsigned a < bv_unsigned buf)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Hnw Ha.
  rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Ha.
  rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
  intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply write_to_mem_above. lia.
  - apply write_to_mem_below; [exact Hnb | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
  intros segs data mem buf Hnw.
  rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  destruct data as [|b rest]; [|apply adv_apply_write].
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes
       delivered_writes write_to_mem].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.
End WithFP1.
