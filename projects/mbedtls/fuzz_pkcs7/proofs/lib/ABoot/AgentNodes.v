(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (rz_write_chan written out in plain text instead of its encoded CDefT form, with two new premises: the model has a channel reader, and the write range passes access_ok). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AgentLib.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AgentNodes () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "asanreflect_fx"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "epend"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_writable_byte"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.with_copyins"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "OSSVerify.KrLib.ABoot.ShapeAlg.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0"; "Corelib.Init.Datatypes.false"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.rw_bytes_max"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_write_ch"; "OSSVerify.KrLib.ABoot.ExitSim.is_exit_no"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_exit"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "(0.O5.(1.$2.)O4.(3.(4.&40.)O1.)(5.(4.&40.))(6.$2.)O3.O2.)")
(* [comment removed for export] *).

Lemma step_ecall_epend : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Psegs,(7.$8.)Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Pw,(4.&20.)P,(;.(:.(4.&20.))(<.R6.R4.)(3.(4.&20.)R1.))P,(;.$=.(>.R2.)$?.)(;.(10.$11.)(12.R8.(13.$2.R7.R6.R5.R4.))(14.$11.(15.R7.R6.R5.R4.(16.R7.(17.&5.+11.$18.)))))")
(* [comment removed for export] *).
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

Lemma ms_writable_byte_epend : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Psegs,(7.$8.)Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Px8,(4.&40.)(;.Paddr,(4.&40.)(:.(4.&8.))(19.R6.(15.R5.R4.R3.R2.R1.))(1:.R6.R3.))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof. reflexivity. Qed.

Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof. reflexivity. Qed.

Lemma adv_set_epend : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Px8,(4.&40.)Pv,(4.&40.)(;.$11.(1;.(1<.(15.R6.R5.R4.R3.R2.)R1.))(13.$2.(1=.R6.(17.&5.+:.$18.)R1.)(1>.R5.+4.)R4.R3.))")
(* [comment removed for export] *).
Proof. intros. unfold epend. apply adv_set. Qed.

Lemma adv_eff_ret_epend : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Px8,(4.&40.)Pr,(4.&40.)(;.$11.(1;.(1?.(15.R6.R5.R4.R3.R2.)(20.R1.(21.(22.(4.&40.)(7.(4.&8.))))(21.(22.(4.&40.)(4.&40.)))(21.(22.(4.&40.)(4.&40.)))(21.$23.)(21.(22.(4.&40.)$24.)))))(13.$2.(1=.R6.(17.&5.+:.$18.)R1.)(1>.R5.+4.)R4.R3.))")
(* [comment removed for export] *).
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_eff_ret_copyins_epend : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Px8,(4.&40.)Pr,(4.&40.)Preads,(7.(22.(4.&40.)$24.))(;.$11.(1;.(1?.(15.R7.R6.R5.R4.R3.)(25.R1.(20.R2.(21.(22.(4.&40.)(7.(4.&8.))))(21.(22.(4.&40.)(4.&40.)))(21.(22.(4.&40.)(4.&40.)))(21.$23.)(21.(22.(4.&40.)$24.))))))(13.$2.(1=.R7.(17.&5.+:.$18.)R2.)(1>.R6.+4.)R5.R4.))")
(* [comment removed for export] *).
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.

(* [comment removed for export] *)
Lemma rz_sys : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Psegs,(7.$8.)Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Pmodel,$26.Pw,(4.&20.)PT,$27.P,(;.(:.(4.&40.))(28.R3.)(5.(4.&40.)))P,(;.(7.(22.(4.&40.)(4.&40.)))(29.R4.)(21.(22.(4.&40.)(4.&40.))))P,(;.(:.(4.&20.))(<.R:.R8.)(3.(4.&20.)R4.))P,(;.$=.(>.R5.)$?.)P,(2:.R<.(2;.(15.R;.R:.R9.R8.(16.R;.(17.&5.+11.$18.)))R7.)R5.)(2:.R=.(2;.(13.$2.R<.R;.R:.R9.)R8.)R6.)")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_write_chan : forall segs regs pc mem model fd ch n bs T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 64%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdChannel ch) -> w_is0 ch = false ->
  m_channel_reader model = true ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
  (1 <= n)%nat -> (Z.of_nat n <= rw_bytes_max)%Z -> (Z.of_nat n < 2 ^ 64)%Z ->
  rdn segs mem (getr regs 11) n = Some bs ->
  (* the range [vfs_write]'s [access_ok] accepts on the count [n]; see
     [CatSim.write1_check_n] *)
  access_okb (getr regs 11) (Z.of_nat n) = true ->
  (forall k, (1 <= k)%nat -> (k <= n)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) T) ->
  realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
           (t_write_ch ch bs T).
Proof.
  intros segs regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hrdr Hcnt Hn1 Hmax Hn64 Hrd Hok Hc.
  pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
  eapply (rz_write_ch segs _ model fd ch (getr regs 17) bs T Hh Hlazy).
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
  intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rz_exit_lit : ltac2:(CDefT.buildp (gd_tbl_AgentNodes ()) "Psegs,(7.$8.)Pregs,(9.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(:.(4.&8.))Prom,P,(4.&40.)(:.(4.&8.))Pmodel,$26.Pcode,$2<.P,(;.(:.(4.&40.))(28.R2.)(5.(4.&40.)))P,(3>.(16.R7.(17.&5.+11.$18.)))P,(;.(4.&40.)(16.R8.(17.&5.+:.$18.))(36.&40.R3.))P,(3?.(39.=R4.)(2>.R4.+100.))(2:.R;.(2;.(15.R:.R9.R8.R7.(16.R:.(17.&5.+11.$18.)))R6.)(40.(36.&40.R5.)(41.R6.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom model code Hh Hx8 Ha0 Hc.
  rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.
