(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_FileSim () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.LinuxProcessSem.State.with_copyins"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "Stdlib.Lists.List.filter"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.Fs.file_read"; "Stdlib.Arith.PeanoNat.Nat.min"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "Corelib.Init.Nat.sub"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Nat.add"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_byte"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "WithFP1.mrb"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.S"; "stdpp.bitvector.definitions.bv_add"; "Corelib.Init.Peano.lt"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.State.cstr_result"; "LinuxProcessSemantics.LinuxProcessSem.State.read_cstr_aux"; "LinuxProcessSemantics.LinuxProcessSem.State.CstrOk"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.State.read_cstr"; "LinuxProcessSemantics.LinuxProcessSem.State.CstrTooLong"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_stack_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "OSSVerify.KrLib.ABoot.CatExec.cat_argv_ptr"; "Corelib.Lists.ListDef.nth"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "WithFP1.WithSegs.to_fout"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec"; "WithFP1.WithSegs.fout_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "WithFP1.fout_trace"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "LinuxProcessSemantics.LinuxProcessSem.Run.all_traces_error"; "OSSVerify.KrLib.ABoot.ExitSim.is_exit_no"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.check_openat"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.fd32"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.check_close"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.check_read"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.check_write"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.check_open_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_fd"; "LinuxProcessSemantics.LinuxProcessSem.State.eff_copyins"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.clear_copyins"; "WithFP1.check_open_result_copyins"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_copyins_after"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_ret_only"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_ret_only_copyins"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.AT_FDCWD"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path_eqb"; "Corelib.Init.Datatypes.false"; "Stdlib.ZArith.BinInt.Z.ldiff"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.open_ignored_flags"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_plain_name"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "WithFP1.open_copyins"; "LinuxProcessSemantics.LinuxProcessSem.State.with_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.wr_create_flags"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei.fs_under"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFileW"; "LinuxProcessSemantics.LinuxProcessSem.State.with_fs"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_set"; "LinuxProcessSemantics.LinuxProcessSem.State.EISDIR"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.modeled_open_flags"; "LinuxProcessSemantics.LinuxProcessSem.State.ENAMETOOLONG"; "WithFP1.to_fout"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOENT"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_map"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_writable_byte"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.rw_bytes_max"; "LinuxProcessSemantics.LinuxProcessSem.State.access_okb"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.delivered_writes"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite.modeled_file_gap"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0"; "LinuxProcessSemantics.LinuxProcessSem.Fs.file_write"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_remove"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "OSSVerify.KrLib.ABoot.StreamSim.wseg_ok"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "WithFP1.fout_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"; "LinuxProcessSemantics.LinuxProcessSem.Run.behavior"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fs_fs : forall f m, m_fs (with_fs f m) = f.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fs_halted : forall f m, m_halted (with_fs f m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fs_fds : forall f m, m_fds (with_fs f m) = m_fds m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma adv_eff_ret : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Px8,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pr,(1.&40.)(3.$4.(5.(6.(7.R6.(8.Vfx,)R5.(9.(1.&40.)R4.)(:.(1.&40.))(;.Vfx,)R3.R2.)(<.R1.(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.)))))(12.Vfx,(13.R6.(14.&5.+:.$15.)R1.)(16.R5.+4.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros regs pc x8 mem rom r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_eff_ret_copyins : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Px8,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pr,(1.&40.)Pcopyins,(?.(>.(1.&40.)$11.))(3.$4.(5.(6.(7.R7.(8.Vfx,)R6.(9.(1.&40.)R5.)(:.(1.&40.))(;.Vfx,)R4.R3.)(17.R1.(<.R2.(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))))(12.Vfx,(13.R7.(14.&5.+:.$15.)R2.)(16.R6.+4.)R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros regs pc x8 mem rom r copyins.
  unfold with_copyins.
  apply adv_eff_ret.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_wmem_si : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
  intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. congruence.
Qed.

#[using="Type"] Lemma fs_lookup_set_eq : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof.
  induction fs as [|[q dq] fs IH]; intros p d; cbn.
  - rewrite path_eqb_refl. reflexivity.
  - destruct (path_ltb p q); cbn.
    + rewrite path_eqb_refl. reflexivity.
    + destruct (path_eqb p q) eqn:E; cbn.
      * rewrite path_eqb_refl. reflexivity.
      * rewrite E. apply IH.
Qed.

#[using="Type"] Lemma fs_lookup_set_neq : forall fs p d q, q <> p ->
  fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof.
  induction fs as [|[r dr] fs IH]; intros p d q Hne; cbn.
  - rewrite path_eqb_neq by exact Hne. reflexivity.
  - destruct (path_ltb p r); cbn.
    + rewrite path_eqb_neq by exact Hne. reflexivity.
    + destruct (path_eqb p r) eqn:E; cbn.
      * apply path_eqb_eq in E. subst r.
        rewrite path_eqb_neq by exact Hne. reflexivity.
      * destruct (path_eqb q r); [reflexivity | apply IH; exact Hne].
Qed.

#[using="Type"] Lemma path_ltb_irrefl : forall p, path_ltb p p = false.
Proof.
  induction p as [|a p IH]; cbn; [reflexivity|].
  unfold bv_ltu. rewrite Z.ltb_irrefl, bv_eqb_refl, IH. reflexivity.
Qed.

#[using="Type"] Lemma fs_set_set : forall fs p d d', fs_set (fs_set fs p d) p d' = fs_set fs p d'.
Proof.
  induction fs as [|[q dq] fs IH]; intros p d d'; cbn.
  - rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
  - destruct (path_ltb p q) eqn:EL; cbn.
    + rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
    + destruct (path_eqb p q) eqn:EE; cbn.
      * rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
      * rewrite EL, EE, IH. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
  fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
  intros fds k e fd Hne. cbn.
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_cons_None : forall fds k e fd,
  fd_lookup ((k, e) :: fds) fd = None -> k <> fd /\ fd_lookup fds fd = None.
Proof.
  intros fds k e fd H. cbn in H.
  destruct (bv_eqb k fd) eqn:E; [discriminate|].
  split; [|exact H].
  intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

#[using="Type"] Lemma fd_filter_id : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pfds,(?.(>.(1.&40.)$18.))Pfd,(1.&40.)P,(3.(2.$18.)(19.R2.R1.)(:.$18.))(3.(?.(>.(1.&40.)$18.))(1:.(>.(1.&40.)$18.)Lp,(>.(1.&40.)$18.)(1;.(1<.&40.(1=.(1.&40.)$18.R1.)R3.))R3.)R3.)")
(* [comment removed for export] *).
Proof.
  induction fds as [|[k e] fds IH]; intros fd H; [reflexivity|].
  apply fd_lookup_cons_None in H. destruct H as [Hne H].
  cbn [List.filter fst]. rewrite (bv_eqb_neq k fd Hne). cbn [negb].
  rewrite IH by exact H. reflexivity.
Qed.

#[using="Type"] Lemma fd_insert_fresh : forall fds fd e,
  fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof.
  intros fds fd e H. unfold fd_insert. rewrite fd_filter_id by exact H.
  reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_filter_neq : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pfds,(?.(>.(1.&40.)$18.))Pfd,(1.&40.)Pfd',(1.&40.)P,(1>.(3.(1.&40.)R1.R2.))(3.(2.$18.)(19.(1:.(>.(1.&40.)$18.)Lp,(>.(1.&40.)$18.)(1;.(1<.&40.(1=.(1.&40.)$18.R1.)R4.))R4.)R2.)(19.R4.R2.))")
(* [comment removed for export] *).
Proof.
  induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
  cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Hk.
  - apply bv_eqb_eq in Hk. subst k.
    cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
    rewrite bv_eqb_neq by congruence. reflexivity.
  - cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

#[using="Type"] Lemma fd_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.

#[using="Type"] Lemma fd_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
  fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
  intros fds fd e fd' Hne. unfold fd_insert.
  rewrite fd_lookup_cons_neq by congruence.
  apply fd_lookup_filter_neq. exact Hne.
Qed.

#[using="Type"] Lemma fd_lookup_remove_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd'.
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.

#[using="Type"] Lemma fd_lookup_some_none_neq : forall fds a b ea,
  fd_lookup fds a = Some ea -> fd_lookup fds b = None -> a <> b.
Proof. intros fds a b ea Ha Hb ->. congruence. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_fd_after_open : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Px,$18.Py,$18.Pz,$18.Pfdin,(1.&40.)Pe,$18.(1?.(1.&40.)Lw,(1.&40.)(20.(3.(2.$18.)(19.(21.(22.(>.(1.&40.)$18.)(23.(1.&40.)$18.(24.&40.=)R6.)(22.(>.(1.&40.)$18.)(23.(1.&40.)$18.(24.&40.+1.)R5.)(22.(>.(1.&40.)$18.)(23.(1.&40.)$18.(24.&40.+2.)R4.)(=.(>.(1.&40.)$18.)))))R3.R2.)R1.)(:.$18.))(25.(26.&40.R1.)(27.+2.+1?.))))")
(* [comment removed for export] *).
Proof.
  intros x y z fdin e.
  destruct (decide (fdin = Z_to_bv 64 3)) as [->|Hne].
  - exists (Z_to_bv 64 4). split.
    + rewrite fd_lookup_insert_neq
        by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
      reflexivity.
    + change (bv_unsigned (Z_to_bv 64 4)) with 4%Z. lia.
  - exists (Z_to_bv 64 3). split.
    + rewrite fd_lookup_insert_neq by congruence. reflexivity.
    + change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
Qed.

#[using="Type"] Lemma filter_fd_cons_keep : forall {B} (fds : list (word * B)) k (e : B) fd,
  k <> fd ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) ((k, e) :: fds)
  = (k, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
  intros B fds k e fd Hne. cbn [List.filter fst].
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

#[using="Type"] Lemma filter_fd_cons_drop : forall {B} (fds : list (word * B)) fd (e : B),
  List.filter (fun p => negb (bv_eqb (fst p) fd)) ((fd, e) :: fds)
  = List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
  intros B fds fd e. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma length_file_read : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pdata,(?.(1.&8.))Poff,(1.&40.)Pcount,(1.&40.)(3.$11.(28.(1.&8.)(29.R3.R2.R1.))(2:.(2;.R1.)(2<.(28.(1.&8.)R3.)(2;.R2.))))")
(* [comment removed for export] *).
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

#[using="Type"] Lemma file_read_nil : forall data off count,
  (length data <= word_to_nat off)%nat -> file_read data off count = [].
Proof.
  intros data off count H. rewrite file_read_unguarded.
  rewrite skipn_all2 by exact H. apply firstn_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma file_write_append : forall data off bs,
  word_to_nat off = length data -> file_write data off bs = data ++ bs.
Proof.
  intros data off bs Hoff. unfold file_write.
  destruct bs as [|b bs]; [now rewrite app_nil_r|]. cbv zeta.
  rewrite Hoff, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
  rewrite firstn_all.
  rewrite skipn_all2 by lia.
  rewrite app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma firstn_add {A} : forall (l : list A) n m,
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction l as [|x l IH]; intros n m.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma copy_step : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pdata,(?.(1.&8.))Poff,(1.&40.)Pcount,(1.&40.)(3.(?.(1.&8.))(2=.(1.&8.)(2>.(1.&8.)(2;.R2.)R3.)(29.R3.R2.R1.))(2>.(1.&8.)(2?.(2;.R2.)(2:.(2;.R1.)(2<.(28.(1.&8.)R3.)(2;.R2.))))R3.))")
(* [comment removed for export] *).
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite firstn_add. f_equal.
  destruct (Nat.le_ge_cases (word_to_nat count)
              (length data - word_to_nat off)) as [H|H].
  - rewrite Nat.min_l by exact H. reflexivity.
  - rewrite Nat.min_r by exact H.
    rewrite firstn_all2 by (rewrite length_skipn; lia).
    rewrite firstn_all2 by (rewrite length_skipn; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

#[using="Type"] Lemma ms_read_byte_mrb : forall segs regs pc mem,
  ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_read_byte_rec_mrb : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pregs,(0.&5.(1.&40.))Pfr,(0.&5.(1.&40.))Ppc,(1.&40.)Psv,(2.(1.&40.))Prv,(2.(1.&40.))Pfc,(1.&20.)Pmem,P,(1.&40.)(2.(1.&8.))(3.Paddr,(1.&40.)(2.(1.&8.))(31.(7.R7.R6.R5.R4.R3.R2.R1.(32.R8.)))(33.R8.R1.))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mrb_first : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_tail : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pmem,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pn,$11.Pb,(1.&8.)Prest,(?.(1.&8.))P,(3.(2.(?.(1.&8.)))(34.R6.R5.R4.(35.R3.))(9.(?.(1.&8.))(22.(1.&8.)R2.R1.)))(3.(2.(?.(1.&8.)))(34.R7.R6.(36.&40.R5.(14.&40.+1.$15.))R4.)(9.(?.(1.&8.))R2.))")
(* [comment removed for export] *).
Proof.
  intros segs mem a n b rest H. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; reflexivity.
Qed.

#[using="Type"] Lemma read_cstr_aux_of_rdn : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pstr,(?.(1.&8.))Pfuel,$11.Pmem,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)P,(37.(28.(1.&8.)R4.)R3.)P,(1>.(38.(1.&8.)(24.&8.=)R5.))P,(3.(2.(?.(1.&8.)))(34.R7.R4.R3.(2?.(28.(1.&8.)R6.)#1.))(9.(?.(1.&8.))(2=.(1.&8.)R6.(22.(1.&8.)(24.&8.=)(=.(1.&8.))))))(3.$39.(3:.(33.R8.R5.)R4.R6.)(3;.R7.))")
(* [comment removed for export] *).
Proof.
  intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
      by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
    cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    cbn [read_cstr_aux]. cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    assert (Hfirst : mrb segs mem a = Some b)
      by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Htail : rdn segs mem (a + 1) (length str + 1)
                    = Some (str ++ [Z_to_bv 8 0]))
      by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia)
               ltac:(intro; apply Hnz; right; assumption) Htail).
    reflexivity.
Qed.

#[using="Type"] Lemma read_cstr_of_rdn : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pmem,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pstr,(?.(1.&8.))P,(3<.(28.(1.&8.)R1.)#???.)P,(1>.(38.(1.&8.)(24.&8.=)R2.))P,(3.(2.(?.(1.&8.)))(34.R6.R5.R4.(2?.(28.(1.&8.)R3.)#1.))(9.(?.(1.&8.))(2=.(1.&8.)R3.(22.(1.&8.)(24.&8.=)(=.(1.&8.))))))(3.$39.(3=.(33.R7.R6.)R5.)(3;.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs mem a str Hlen Hnz Hr.
  unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
  change path_max with 4096%nat. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma read_cstr_aux_toolong_of_rdn : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pfuel,$11.Pbs,(?.(1.&8.))Pmem,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)P,(3.$11.(28.(1.&8.)R3.)R4.)P,(1>.(38.(1.&8.)(24.&8.=)R4.))P,(3.(2.(?.(1.&8.)))(34.R7.R4.R3.R6.)(9.(?.(1.&8.))R5.))(3.$39.(3:.(33.R8.R5.)R4.R7.)$3>.)")
(* [comment removed for export] *).
Proof.
  intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
    [reflexivity|].
  destruct bs as [|b bs]; [cbn in Hlen; lia|].
  cbn [read_cstr_aux].
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hfirst : mrb segs mem a = Some b)
    by (apply (mrb_first segs mem a fuel b bs); exact Hr).
  assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
    by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
  rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
             ltac:(intro; apply Hnz; right; assumption) Htail).
  reflexivity.
Qed.

#[using="Type"] Lemma read_cstr_toolong_of_rdn : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pmem,P,(1.&40.)(2.(1.&8.))Pa,(1.&40.)Pbs,(?.(1.&8.))P,(3.$11.(28.(1.&8.)R1.)#1000.)P,(1>.(38.(1.&8.)(24.&8.=)R2.))P,(3.(2.(?.(1.&8.)))(34.R6.R5.R4.#1000.)(9.(?.(1.&8.))R3.))(3.$39.(3=.(33.R7.R6.)R5.)$3>.)")
(* [comment removed for export] *).
Proof.
  intros segs mem a bs Hlen Hnz Hr.
  unfold read_cstr. change path_max with 4096%nat.
  eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma read_argv_cstr_k : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pph,$3?.Psegs,(?.$30.)Psp,(1.&40.)Pav,(?.(?.(1.&8.)))Pev,(?.(?.(1.&8.)))Pk,$11.Puid,(1.&40.)Phw,(1.&40.)Prnd,$40.P,(37.R4.(28.(?.(1.&8.))R6.))P,(25.(41.(26.&40.R8.)(42.(28.(1.&8.)(43.R:.R8.R7.R6.R4.R3.R2.))))(27.+2.+40.))(3.(2.(?.(1.&8.)))(34.R:.(44.R9.(45.R;.R9.R8.R7.R5.R4.R3.))(46.R9.R8.R7.R6.)(2?.(28.(1.&8.)(47.(?.(1.&8.))R6.R8.(=.(1.&8.))))#1.))(9.(?.(1.&8.))(2=.(1.&8.)(47.(?.(1.&8.))R6.R8.(=.(1.&8.)))(22.(1.&8.)(24.&8.=)(=.(1.&8.))))))")
(* [comment removed for export] *).
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [exact E | | exact Hnw].
  rewrite length_app. cbn [length]. lia.
Qed.

#[using="Type"] Lemma read_argv_prefix_k : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pph,$3?.Psegs,(?.$30.)Psp,(1.&40.)Pav,(?.(?.(1.&8.)))Pev,(?.(?.(1.&8.)))Pk,$11.Pn,$11.Puid,(1.&40.)Phw,(1.&40.)Prnd,$40.P,(37.R5.(28.(?.(1.&8.))R7.))P,(3<.R5.(28.(1.&8.)(47.(?.(1.&8.))R6.R8.(=.(1.&8.)))))P,(25.(41.(26.&40.R:.)(42.(28.(1.&8.)(43.R<.R:.R9.R8.R5.R4.R3.))))(27.+2.+40.))(3.(2.(?.(1.&8.)))(34.R<.(44.R;.(45.R=.R;.R:.R9.R6.R5.R4.))(46.R;.R:.R9.R8.)R7.)(9.(?.(1.&8.))(2>.(1.&8.)R7.(47.(?.(1.&8.))R8.R:.(=.(1.&8.))))))")
(* [comment removed for export] *).
Proof.
  intros ph segs sp av ev k n uid hw rnd Hk Hn Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (firstn n (nth k av []))
    ((skipn n (nth k av []) ++ [Z_to_bv 8 0]) ++ post) n) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [| |exact Hnw].
  - rewrite E. rewrite <- !app_assoc.
    rewrite (app_assoc (firstn n (nth k av [])) (skipn n (nth k av []))).
    rewrite firstn_skipn. reflexivity.
  - apply firstn_length_le. exact Hn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fout_trace (o : word * Fs.Fs) : list event := [ExitEv (fst o) (snd o)].

Section WithSegs.
Variable segs : list Segment.

Inductive to_fout : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfo_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    (forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
    to_fout ms model U
| tfo_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_fout ms' model U ->
    to_fout ms model U
| tfo_sys : forall ms model x8
    (T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
    (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
    (exists eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        to_fout (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_fout ms model U.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_fout ms' model U -> to_fout ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tfo_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_equiv : forall ms model U V,
  to_fout ms model U ->
  (forall o, V o <-> U o) ->
  to_fout ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros V HV.
  - apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
    intro o. rewrite (HV o). apply HU.
  - eapply tfo_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tfo_sys ms model x8 T V);
      [exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
    intro o. rewrite (HV o). apply HU.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_fout_nonempty : forall ms model U,
  to_fout ms model U -> exists o, U o.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ].
  - exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
    apply HU. reflexivity.
  - exact IH.
  - destruct Hrec as (eff & model' & evs & Hspec).
    destruct (IH eff model' evs Hspec) as [o Ho].
    exists o. apply HU. exists eff, model', evs. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_fsys_inv : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pevs,(?.$49.)Pst,$4:.P,(3.(2.(1.&40.))(4;.R4.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R5.)(=.(>.(1.&40.)(1.&40.))))P,(3.(2.(1.&40.))(4=.R7.)(9.(1.&40.)R5.))P,(1>.(4>.(4?.Vsegs,R8.R6.)R7.(50.$51.)))P,Peff,$51.Pmodel',$48.Pevs',(?.$49.)P,(4>.(4?.Vsegs,R<.R:.)R;.(52.$51.R3.R2.R1.))(20.(3.(?.$49.)R2.(=.$49.))(20.(3.(2.(1.&40.))(4;.R3.)(:.(1.&40.)))(3.(?.(>.(1.&40.)(1.&40.)))(4<.R3.)(=.(>.(1.&40.)(1.&40.))))))P,(53.Vsegs,(54.R:.R9.)R7.R6.)(1?.$51.Leff,$51.(1?.$48.Lmodel',$48.(20.(4>.(4?.Vsegs,R=.R;.)R<.(52.$51.R2.R1.(=.$49.)))(20.(3.(?.$49.)R:.(=.$49.))(3.$4:.R9.(55.(54.(5.(6.R=.R2.))R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (He & _ & Hlazy');
      subst evs0;
      match goal with
      | Hmat : materialize_model_accesses model' _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
          inversion Hmat; subst model''
      end;
      exists eff, model'; auto
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (_ & _ & Hlazy');
      rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
      congruence
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fout_post (U : (word * Fs.Fs) -> Prop) : post :=
  fun tr o => exists out, U out /\ tr = fout_trace out /\ exits_with (fst out) tr o.

#[using="Type"] Lemma to_fout_exec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.PU,P,(>.(1.&40.)$56.)SpP,(57.R3.R2.R1.)P,(3.(2.(1.&40.))(4;.R3.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R4.)(=.(>.(1.&40.)(1.&40.))))(58.Vsegs,(54.R6.R5.)(59.R4.))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros Hh Hlazy.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_si. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold fout_post. cbn beta.
        exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
        split; [apply HU; reflexivity |].
        split; [unfold fout_trace; cbn [fst snd app]; reflexivity |].
        cbn [exits_with cfg_model fst]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - (* [comment removed for export] *)
    apply exec_step; [exact Hh | | |].
    + destruct Hrec as (eff & model' & evs & Hspec).
      destruct (Hshape eff model' evs Hspec) as (-> & Hh' & Hlazy').
      eexists; eexists.
      apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
      rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
    + intros evs Hss.
      destruct (sstep_fsys_inv ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_fsys_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
      eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' Hlazy') |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [cbn [app]; exact Heq | exact Hx].
Qed.

#[using="Type"] Lemma to_fout_star_only : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.PU,P,(>.(1.&40.)$56.)SpP,(57.R3.R2.R1.)P,(3.(2.(1.&40.))(4;.R3.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R4.)(=.(>.(1.&40.)(1.&40.))))Ptr,(?.$49.)Pc,$5:.P,(5;.Vsegs,(54.R8.R7.)R2.R1.)(1?.(>.(1.&40.)$56.)Lo,(>.(1.&40.)$56.)(20.A1.R8.R1.(5<.$49.R4.(5=.R1.))))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_fout_exec ms model U Hto Hh Hlazy) Hstar))
    as (tr' & o & _ & (out & Hout & Heq & _)).
  exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma to_fout_star_admits : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.PU,P,(>.(1.&40.)$56.)SpP,(57.R3.R2.R1.)P,(3.(2.(1.&40.))(4;.R3.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R4.)(=.(>.(1.&40.)(1.&40.))))Po,(>.(1.&40.)$56.)P,A1.R5.R1.(1?.$5:.Lc,$5:.(5;.Vsegs,(54.R9.R8.)(5=.R3.)R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - (* [comment removed for export] *)
    apply HU in Ho. subst o. unfold fout_trace; cbn [fst snd].
    exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted
                              (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_si. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - (* [comment removed for export] *)
    destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - (* [comment removed for export] *)
    apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (Hshape eff model' evs Hspec) as (He & Hh' & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' Hlazy' o Ht) as [c Hstar].
    exists c.
    replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
    rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_fout_progress : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.PU,P,(>.(1.&40.)$56.)SpP,(57.R3.R2.R1.)P,(3.(2.(1.&40.))(4;.R3.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R4.)(=.(>.(1.&40.)(1.&40.))))Pevs,(?.$49.)Pst,$4:.P,(53.Vsegs,(54.R8.R7.)R2.R1.)(1?.$4.Lms',$4.(1?.$48.Lmodel',$48.(20.(3.$4:.R4.(55.(54.R2.R1.)))(5>.(1>.(3.(2.(1.&40.))(4;.R1.)(:.(1.&40.))))(20.(3.(2.(1.&40.))(4;.R1.)(:.(1.&40.)))(20.(3.(?.(>.(1.&40.)(1.&40.)))(4<.R1.)(=.(>.(1.&40.)(1.&40.))))(1?.P,(>.(1.&40.)$56.)SpLU',P,(>.(1.&40.)$56.)Sp(57.R3.R2.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy evs st Hss.
  revert evs st Hss.
  induction Hto as
    [ ms model x8 U Hsvc Hx8 HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
    intros evs st Hss.
  - (* [comment removed for export] *)
    destruct (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss)
      as [_ Hst]. subst st.
    do 2 eexists. split; [reflexivity|]. left. cbn. discriminate.
  - (* [comment removed for export] *)
    destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss)
      as [_ Hst]. subst st.
    do 2 eexists. split; [reflexivity|]. right.
    repeat split; try assumption. exists U. exact Hto.
  - (* [comment removed for export] *)
    destruct (sstep_fsys_inv ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss)
      as (eff & model' & Hspec & _ & Hst). subst st.
    destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
    do 2 eexists. split; [reflexivity|]. right.
    repeat split; try assumption.
    exists (T eff model'). exact (Hcont eff model' [] Hspec).
Qed.

Definition fon_path (c : config) : Prop := ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "(5>.(20.(3.(2.(1.&40.))(4;.(5?.O1.))(:.(1.&40.)))(20.(3.(?.(>.(1.&40.)(1.&40.)))(4<.(5?.O1.))(=.(>.(1.&40.)(1.&40.))))(1?.P,(>.(1.&40.)$56.)SpLU,P,(>.(1.&40.)$56.)Sp(57.(60.O1.)(5?.O1.)R1.))))(1>.(3.(2.(1.&40.))(4;.(5?.O1.))(:.(1.&40.)))))")
(* [comment removed for export] *).

#[using="Type"] Lemma fon_path_step : forall c evs c',
  fon_path c -> sstep segs c evs (SNext c') -> fon_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold fon_path in *; cbn in Hop |- *.
  destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
  - destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
      as (ms'' & model'' & Hst & Hcase).
    inversion Hst; subst.
    destruct Hcase as [Hhz | (Hhz & Hlazy' & U' & Hto')].
    + right. exact Hhz.
    + left. repeat split; try assumption. exists U'; exact Hto'.
  - exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma fon_path_no_error : forall c evs, fon_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold fon_path in Hop; cbn in Hop.
  destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
  - destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
      as (ms'' & model'' & Hst & _). discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma star_fon_path : forall c tr c',
  fon_path c -> star segs c tr c' -> fon_path c'.
Proof. exact (star_inv segs fon_path fon_path_step). Qed.

#[using="Type"] Lemma to_fout_no_error : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.PU,P,(>.(1.&40.)$56.)SpP,(57.R3.R2.R1.)P,(3.(2.(1.&40.))(4;.R3.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R4.)(=.(>.(1.&40.)(1.&40.))))(1>.(61.Vsegs,(54.R6.R5.)))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy. apply exec_no_error.
  eapply exec_conseq; [exact (to_fout_exec ms model U Hto Hh Hlazy) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma star_syscall_nil : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Peff,$51.Pmodel',$48.P,(3.(2.(1.&40.))(4;.R4.)(:.(1.&40.)))P,(3.(2.(1.&40.))(4=.R6.)(9.(1.&40.)R4.))P,(4>.(4?.Vsegs,R7.R5.)R6.(52.$51.R4.R3.(=.$49.)))P,(3.(2.(1.&40.))(4;.R4.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R5.)(=.(>.(1.&40.)(1.&40.))))(5;.Vsegs,(54.R:.R9.)(=.$49.)(54.(5.(6.R:.R7.))R6.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff model' Hh Hsvc Hspec Hh' Hlazy.
  apply star_one.
  apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
  rewrite (materialize_model_accesses_no_lazy model' _ Hlazy). reflexivity.
Qed.

#[using="Type"] Lemma reaches_error_star : forall c tr c',
  star segs c tr c' -> reaches_error segs c' -> reaches_error segs c.
Proof.
  intros c tr c' Hstar (tr2 & c2 & evs & Hstar2 & Hss).
  exists (tr ++ tr2), c2, evs. split; [eapply star_trans; eauto | exact Hss].
Qed.

#[using="Type"] Lemma spec_err_error : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)P,(3.(2.(1.&40.))(4;.R2.)(:.(1.&40.)))P,(3.(2.(1.&40.))(4=.R4.)(9.(1.&40.)R2.))P,(4>.(4?.Vsegs,R5.R3.)R4.(50.$51.))(61.Vsegs,(54.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hspec.
  exists [], (mkCfg ms model), []. split; [apply star_refl|].
  eapply sstep_syscall_unmodeled; eassumption.
Qed.

#[using="Type"] Lemma msteps_spec_err_error : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pms',$4.Pmodel,$48.Px8,(1.&40.)P,(3.(2.(1.&40.))(4;.R2.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R3.)(=.(>.(1.&40.)(1.&40.))))P,(62.Vsegs,R6.R5.)P,(3.(2.(1.&40.))(4=.R6.)(9.(1.&40.)R4.))P,(4>.(4?.Vsegs,R7.R5.)R6.(50.$51.))(61.Vsegs,(54.R9.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
  eapply reaches_error_star.
  - apply msteps_star_nil; eassumption.
  - eapply spec_err_error; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma spec_err_all_traces_error : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)P,(3.(2.(1.&40.))(4;.R2.)(:.(1.&40.)))P,(3.(2.(1.&40.))(4=.R4.)(9.(1.&40.)R2.))P,(4>.(4?.Vsegs,R5.R3.)R4.(50.$51.))(63.Vsegs,(54.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hspec.
  assert (Hno_ok : forall eff model' events,
      ~ syscall_spec (sys_input segs ms x8) model
          (Ok eff model' events)).
  { intros eff model' events Hok.
    pose proof Hspec as Herr.
    apply (check_syscall_complete_unmodeled _ _ eff) in Herr.
    apply check_syscall_complete_ok in Hok.
    rewrite Herr in Hok. discriminate Hok. }
  constructor.
  - exists [], SError. eapply sstep_syscall_unmodeled; eassumption.
  - intros evs c' Hnext. inversion Hnext; subst; try congruence.
    all: exfalso;
      match goal with
      | Hno : forall (eff0 : SyscallEffect) (model0 : Model)
                       (events0 : list event),
          ~ syscall_spec (sys_input ?segs0 ?ms0 ?expected) ?m0
              (Ok eff0 model0 events0),
        Hexpected : ms_svc_pending ?ms0 = Some ?expected,
        Hactual : ms_svc_pending ?ms0 = Some ?actual,
        Hok : syscall_spec (sys_input ?segs0 ?ms0 ?actual) ?m0
                (Ok ?eff ?model' ?events) |- _ =>
          assert (actual = expected) by congruence; subst actual;
          exact (Hno eff model' events Hok)
      end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_spec_err_all_traces_error : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pms',$4.Pmodel,$48.Px8,(1.&40.)P,(3.(2.(1.&40.))(4;.R2.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R3.)(=.(>.(1.&40.)(1.&40.))))P,(62.Vsegs,R6.R5.)P,(3.(2.(1.&40.))(4=.R6.)(9.(1.&40.)R4.))P,(4>.(4?.Vsegs,R7.R5.)R6.(50.$51.))(63.Vsegs,(54.R9.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
  eapply msteps_all_traces_error; [exact Hh | exact Hlazy | exact Hm |].
  eapply spec_err_all_traces_error; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_exit_code : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pcode,(1.&40.)P,(3.(2.(1.&40.))(4=.R4.)(9.(1.&40.)R2.))P,(64.R3.)P,(3.(1.&40.)(65.R6.#0.)R3.)P,(3.(1.&40.)(66.&40.R4.(24.&40.+??.))R4.)(57.R8.R7.Lo,(>.(1.&40.)$56.)(3.(>.(1.&40.)$56.)R1.(23.(1.&40.)$56.R6.(67.R8.))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 code Hsvc Hx8 Hg Hland.
  apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
  intro o. rewrite Hg, Hland. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_sys_det : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Peff,$51.Pmodel',$48.PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R6.)(9.(1.&40.)R4.))P,(4>.(4?.Vsegs,R7.R5.)R6.(52.$51.R4.R3.(=.$49.)))P,Peff2,$51.Pm2,$48.Pevs2,(?.$49.)P,(4>.(4?.Vsegs,R;.R9.)R:.(52.$51.R3.R2.R1.))(20.(3.$51.R4.R9.)(20.(3.$48.R3.R8.)(3.(?.$49.)R2.(=.$49.))))P,(1>.(4>.(4?.Vsegs,R9.R7.)R8.(50.$51.)))P,(3.(2.(1.&40.))(4;.R6.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R7.)(=.(>.(1.&40.)(1.&40.))))P,(57.(5.(6.R<.R9.))R8.R7.)(57.R=.R<.R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff model' U Hsvc Hok Huniq Hne Hh' Hlazy' Hcont.
  apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
  - exists eff, model', []. exact Hok.
  - intros eff2 m2 evs2 Hs.
    destruct (Huniq eff2 m2 evs2 Hs) as (_ & -> & ->).
    repeat split; assumption.
  - intros eff2 m2 evs2 Hs.
    destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & _). exact Hcont.
  - intro o. split.
    + intro Ho. exists eff, model', []. auto.
    + intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma check_syscall_56 : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Peff,$51.Pm,$48.P,(3.$68.(26.&40.R3.)+38.)(3.$69.(6:.(4?.R6.R5.R4.)R3.R2.)(6;.(4?.R6.R5.R4.)(6<.(65.R5.#0.))(65.R5.#1.)(65.R5.#2.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma check_syscall_57 : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Peff,$51.Pm,$48.P,(3.$68.(26.&40.R3.)+39.)(3.$69.(6:.(4?.R6.R5.R4.)R3.R2.)(6=.(6<.(65.R5.#0.))R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma check_syscall_63 : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Peff,$51.Pm,$48.P,(3.$68.(26.&40.R3.)+3?.)(3.$69.(6:.(4?.R6.R5.R4.)R3.R2.)(6>.(4?.R6.R5.R4.)(6<.(65.R5.#0.))(65.R5.#1.)(65.R5.#2.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

#[using="Type"] Lemma check_syscall_64 : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Peff,$51.Pm,$48.P,(3.$68.(26.&40.R3.)+40.)(3.$69.(6:.(4?.R6.R5.R4.)R3.R2.)(6?.(4?.R6.R5.R4.)(6<.(65.R5.#0.))(65.R5.#1.)(65.R5.#2.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fd_not_error : forall fd : word,
  (bv_unsigned fd < 2 ^ 31)%Z -> addr_is_error_b fd = false.
Proof.
  intros fd H. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma errno_ret_recover : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  (two_pow_64 - bv_unsigned (errno_ret e))%Z = e.
Proof.
  intros e H1 H2. rewrite (errno_ret_unsigned e H1 H2). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

#[using="Type"] Lemma openat_errno_range : forall e,
  In e openat_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.

#[using="Type"] Lemma check_open_result_never_unmodeled : forall eff m mk,
  check_open_result eff m mk <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs copyins] m mk.
  unfold check_open_result, check_new_fd_result.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?];
    destruct copyins as [|? ?];
    try discriminate.
  destruct (errno_ret_in openat_errnos ret); [discriminate|].
  destruct (fd_lookup (m_fds m) ret); [discriminate|].
  destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.

#[using="Type"] Lemma check_open_result_ok_iff : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Peff,$51.Pm,$48.Pmk,P,(1.&40.)$48.Pm',$48.Pevs,(?.$49.)(70.(3.$69.(71.R5.R4.R3.)(72.R2.R1.))(5>.(1?.$68.Le,$68.(20.(38.$68.R1.$73.)(20.(3.$51.R6.(<.(74.R1.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))(20.(3.$48.R3.R5.)(3.(?.$49.)R2.(=.$49.))))))(1?.(1.&40.)Lfd,(1.&40.)(20.(3.(2.$18.)(19.(75.R5.)R1.)(:.$18.))(20.(3.(1.&40.)R1.(76.(75.R5.)))(20.(3.$51.R6.(<.R1.(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))(20.(3.$48.R3.A1.R4.R1.)(3.(?.$49.)R2.(=.$49.)))))))))")
(* [comment removed for export] *).
Proof.
  intros [ret ws zs us cs copyins] m mk m' evs.
  unfold check_open_result, check_new_fd_result. split.
  - intro H.
    destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (errno_ret_in openat_errnos ret) eqn:Herr; try rewrite Herr in H.
    + inversion H; subst.
      apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
      left. exists e. auto.
    + destruct (fd_lookup (m_fds m) ret) eqn:Hlk; try rewrite Hlk in H;
        [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; try rewrite Heq in H;
        [|discriminate].
      inversion H; subst.
      right. exists ret. apply bv_eqb_eq in Heq. auto.
  - intros [ (e & HIn & Heff & -> & ->)
           | (fd & Hlk & Heq & Heff & -> & ->) ].
    + inversion Heff; subst.
      rewrite (errno_ret_in_intro _ e HIn). reflexivity.
    + inversion Heff; subst.
      rewrite errno_ret_in_alloc_fd by reflexivity.
      rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.

Definition open_copyins (ms : machine_state) : list (word * nat) :=
  [(ms_gpr ms 1,
    cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

Definition check_open_result_copyins (reads : list (word * nat))
    (eff : SyscallEffect) (m : Model) (mk : word -> Model) : check_result :=
  check_copyins reads eff (check_open_result (clear_copyins eff) m mk).

#[using="Type"] Lemma effect_from_copyins_and_clear : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Peff,$51.Preads,(?.(>.(1.&40.)$11.))Pcore,$51.P,(3.(?.(>.(1.&40.)$11.))(77.R3.)R2.)P,(3.$51.(78.R4.)R2.)(3.$51.R5.(17.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros [ret ws zs us cs copyins] reads core Hreads Hcore.
  cbn [eff_copyins] in Hreads. subst copyins.
  unfold clear_copyins, with_copyins in Hcore |- *.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies] in Hcore |- *.
  inversion Hcore. reflexivity.
Qed.

#[using="Type"] Lemma check_open_result_copyins_never_unmodeled : forall reads eff m mk,
  check_open_result_copyins reads eff m mk <> CheckUnmodeled.
Proof.
  intros reads eff m mk.
  unfold check_open_result_copyins, check_copyins.
  destruct (access_ranges_eqb (eff_copyins eff) reads);
    [apply check_open_result_never_unmodeled|discriminate].
Qed.

#[using="Type"] Lemma check_open_result_copyins_ok_iff : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Preads,(?.(>.(1.&40.)$11.))Peff,$51.Pm,$48.Pmk,P,(1.&40.)$48.Pm',$48.Pevs,(?.$49.)(70.(3.$69.(79.R6.R5.R4.R3.)(72.R2.R1.))(5>.(1?.$68.Le,$68.(20.(38.$68.R1.$73.)(20.(3.$51.R6.(17.R7.(<.(74.R1.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.)))))(20.(3.$48.R3.R5.)(3.(?.$49.)R2.(=.$49.))))))(1?.(1.&40.)Lfd,(1.&40.)(20.(3.(2.$18.)(19.(75.R5.)R1.)(:.$18.))(20.(3.(1.&40.)R1.(76.(75.R5.)))(20.(3.$51.R6.(17.R7.(<.R1.(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.)))))(20.(3.$48.R3.A1.R4.R1.)(3.(?.$49.)R2.(=.$49.)))))))))")
(* [comment removed for export] *).
Proof.
  intros reads eff m mk m' evs.
  unfold check_open_result_copyins, check_copyins.
  destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
  - apply access_ranges_eqb_eq in Hreads.
    rewrite check_open_result_ok_iff. split.
    + intros [(e & HIn & Hcore & -> & ->)
             | (fd & Hlk & Heq & Hcore & -> & ->)].
      * left. exists e. repeat split; try assumption.
        eapply effect_from_copyins_and_clear; eassumption.
      * right. exists fd. repeat split; try assumption.
        eapply effect_from_copyins_and_clear; eassumption.
    + intros [(e & HIn & Heff & -> & ->)
             | (fd & Hlk & Heq & Heff & -> & ->)].
      * left. exists e. repeat split; try assumption.
        rewrite Heff. reflexivity.
      * right. exists fd. repeat split; try assumption.
        rewrite Heff. reflexivity.
  - split; [discriminate|].
    intros [(e & _ & Heff & _)
           | (fd & _ & _ & Heff & _)].
    all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
      pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue;
      congruence.
Qed.

#[using="Type"] Lemma check_copyins_after_ret_only : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Preads,(?.(>.(1.&40.)$11.))Peff,$51.Pr,(1.&40.)Pm,$48.Pevs,(?.$49.)(3.$69.(7:.R5.R4.(7;.(78.R4.)R3.R2.R1.))(7<.R5.R4.R3.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros reads eff r m evs.
  unfold Prelude.check_copyins_after, check_ret_only_copyins.
  destruct (check_ret_only (clear_copyins eff) r m evs) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff) reads); reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma openat_rd_check : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Pmodel,$48.Pp,(?.(1.&8.))Pd,(?.(1.&8.))P,(3.$68.(26.&40.R4.)+38.)P,(3.(1.&40.)(65.R6.#0.)$7=.)P,(3.$39.(3=.(31.R7.)(65.R7.#1.))(3;.R4.))P,(3.$7>.(7?.R5.(=.(1.&8.)))$80.)P,(3.$68.(81.(26.&40.(65.R9.#2.))$82.)=)P,(3.$7>.(83.R7.)$84.)P,(3.(2.(?.(1.&8.)))(85.(67.R9.)R8.)(9.(?.(1.&8.))R7.))Peff,$51.(3.$69.(6:.(4?.R>.R=.R<.)R1.R;.)(79.(86.R=.)R1.R;.Lfd,(1.&40.)(87.(21.(75.R<.)R1.(88.R;.(24.&40.=)))R<.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read.
  rewrite ?Hdot, ?Hfs.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word =>
       with_fds
         (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
    eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma openat_wr_check : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Pmodel,$48.Pp,(?.(1.&8.))P,(3.$68.(26.&40.R3.)+38.)P,(3.(1.&40.)(65.R5.#0.)$7=.)P,(3.$39.(3=.(31.R6.)(65.R6.#1.))(3;.R3.))P,(3.$7>.(7?.R4.(=.(1.&8.)))$80.)P,(3.$68.(81.(26.&40.(65.R8.#2.))$82.)$89.)P,(3.$7>.(83.R6.)$84.)P,(3.$7>.(8:.(67.R8.)R7.)$80.)Peff,$51.(3.$69.(6:.(4?.R=.R<.R;.)R1.R:.)(79.(86.R<.)R1.R:.Lfd,(1.&40.)(87.(21.(75.R;.)R1.(8;.R:.(24.&40.=)))(8<.(8=.(67.R;.)R:.(=.(1.&8.)))R;.))))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl.
  change (wr_create_flags =? 0)%Z with false. cbv beta iota.
  rewrite Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_create, check_create_wronly.
  rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word =>
       with_fds
         (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
         (with_fs (fs_set (m_fs model) p []) model)))
    eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma openat_wr_isdir_check : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Pmodel,$48.Pp,(?.(1.&8.))P,(3.$68.(26.&40.R3.)+38.)P,(3.(1.&40.)(65.R5.#0.)$7=.)P,(3.$39.(3=.(31.R6.)(65.R6.#1.))(3;.R3.))P,(3.$7>.(7?.R4.(=.(1.&8.)))$80.)P,(3.$68.(81.(26.&40.(65.R8.#2.))$82.)$89.)P,(3.$7>.(83.R6.)$84.)P,(3.$7>.(8:.(67.R8.)R7.)$84.)Peff,$51.(3.$69.(6:.(4?.R=.R<.R;.)R1.R:.)(7<.(86.R<.)R1.(74.$8>.)R:.(=.$49.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl.
  change (wr_create_flags =? 0)%Z with false. cbv beta iota.
  rewrite Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_create.
  rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
  apply check_copyins_after_ret_only.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma openat_toolong_check : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Pms,$4.Px8,(1.&40.)Pmodel,$48.P,(3.$68.(26.&40.R2.)+38.)P,(3.$7>.(8?.(65.R4.#2.))$84.)P,(3.$39.(3=.(31.R5.)(65.R5.#1.))$3>.)Peff,$51.(3.$69.(6:.(4?.R8.R7.R6.)R1.R5.)(7<.(86.R7.)R1.(74.$90.)R5.(=.$49.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno Hfl Hpath eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite Hfl. cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath.
  unfold check_ret_only_copyins, open_copyins.
  destruct (check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG)
    model []) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff)
      [(ms_gpr ms 1,
        cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]);
      reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

Section OpenNodes.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_open_core : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Pmk,P,(1.&40.)$48.Px8,(1.&40.)Preads,(?.(>.(1.&40.)$11.))PTe,P,$68.P,(>.(1.&40.)$56.)SpPTs,P,(1.&40.)P,(>.(1.&40.)$56.)SpPU,Px,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R8.)(9.(1.&40.)R5.))P,(3.(2.(1.&40.))(4;.R8.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R9.)(=.(>.(1.&40.)(1.&40.))))P,Peff,$51.(3.$69.(6:.(4?.Vsegs,R<.R9.)R1.R;.)(79.R8.R1.R;.R:.))P,Pfd,(1.&40.)(20.(3.(2.(1.&40.))(4;.A1.R;.R1.)(:.(1.&40.)))(3.(?.(>.(1.&40.)(1.&40.)))(4<.A1.R;.R1.)(=.(>.(1.&40.)(1.&40.)))))P,Pe,$68.P,(38.$68.R1.$73.)(91.Vsegs,(5.(6.R?.(17.R;.(<.(74.R2.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))))R>.A1.R:.R2.)P,Pfd,(1.&40.)P,(3.(2.$18.)(19.(75.R>.)R1.)(:.$18.))P,(3.(1.&40.)R2.(76.(75.R?.)))(91.Vsegs,(5.(6.R11.(17.R=.(<.R3.(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))))A1.R?.R3.A1.R;.R3.)P,Po,(>.(1.&40.)$56.)(70.A1.R9.R1.(5>.(1?.$68.Le,$68.(20.(38.$68.R1.$73.)A2.R<.R1.R2.))(1?.(1.&40.)Lfd,(1.&40.)(20.(3.(2.$18.)(19.(75.R10.)R1.)(:.$18.))(20.(3.(1.&40.)R1.(76.(75.R10.)))A2.R;.R1.R2.)))))(91.Vsegs,R10.R?.R9.)")
(* [comment removed for export] *).
Proof.
  intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
  apply (tfo_sys segs ms model x8
    (fun eff model' =>
       if addr_is_error_b (eff_ret eff)
       then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
       else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
  - (* [comment removed for export] *)
    intro Hspec.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
      in Hspec.
    rewrite Hchk in Hspec.
    exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
  - (* [comment removed for export] *)
    exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
    apply check_syscall_ok_iff. rewrite Hchk.
    apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
    repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
  - (* [comment removed for export] *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_copyins_ok_iff in Hspec.
    destruct Hspec as [ (e & _ & -> & -> & ->)
                      | (fd & _ & _ & -> & -> & ->) ].
    + repeat split; assumption.
    + destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
  - (* [comment removed for export] *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_copyins_ok_iff in Hspec.
    destruct Hspec as [ (e & HIn & -> & -> & _)
                      | (fd & Hlk & Heq & -> & -> & _) ].
    + destruct (openat_errno_range e HIn) as [He1 He2].
      cbn [eff_ret with_copyins].
      rewrite (errno_ret_error_b e He1 He2).
      rewrite (errno_ret_recover e He1 He2).
      apply Herr; assumption.
    + cbn [eff_ret with_copyins].
      assert (Hne : addr_is_error_b fd = false)
        by (rewrite Heq; apply alloc_fd_not_error_b).
      rewrite Hne.
      apply Hok; assumption.
  - (* [comment removed for export] *)
    intro o. rewrite HU. split.
    + intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk.
          apply check_open_result_copyins_ok_iff. left. exists e. auto. }
        { cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
          rewrite (errno_ret_recover e He1 He2). exact Ht. }
      * exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk.
          apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
        { cbn [eff_ret with_copyins].
          assert (Hne : addr_is_error_b fd = false)
            by (rewrite Heq; apply alloc_fd_not_error_b).
          rewrite Hne. exact Ht. }
    + intros (eff & model' & evs & Hspec & Ht).
      apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
      apply check_open_result_copyins_ok_iff in Hspec.
      destruct Hspec as [ (e & HIn & -> & -> & _)
                        | (fd & Hlk & Heq & -> & -> & _) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        cbn [eff_ret with_copyins] in Ht.
        rewrite (errno_ret_error_b e He1 He2) in Ht.
        rewrite (errno_ret_recover e He1 He2) in Ht.
        left. exists e. auto.
      * cbn [eff_ret with_copyins] in Ht.
        assert (Hne : addr_is_error_b fd = false)
          by (rewrite Heq; apply alloc_fd_not_error_b).
        rewrite Hne in Ht.
        right. exists fd. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma open_ok_fd : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Pmk,P,(1.&40.)$48.Px8,(1.&40.)Preads,(?.(>.(1.&40.)$11.))Pfd,(1.&40.)P,Peff,$51.(3.$69.(6:.(4?.Vsegs,R7.R4.)R1.R6.)(79.R3.R1.R6.R5.))P,(3.(2.$18.)(19.(75.R6.)R2.)(:.$18.))P,(3.(1.&40.)R3.(76.(75.R7.)))(4>.(4?.Vsegs,R9.R6.)R8.(52.$51.(17.R5.(<.R4.(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))A1.R7.R4.(=.$49.)))")
(* [comment removed for export] *).
Proof.
  intros ms model mk x8 reads fd Hchk Hlk Hlt.
  apply check_syscall_ok_iff. rewrite Hchk.
  apply check_open_result_copyins_ok_iff. right. exists fd. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_openat_toolong : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R4.)(9.(1.&40.)R2.))P,(3.$68.(26.&40.R3.)+38.)P,(3.$7>.(8?.(65.R6.#2.))$84.)P,(3.$39.(3=.(31.R7.)(65.R7.#1.))$3>.)P,(3.(2.(1.&40.))(4;.R7.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R8.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(5.(6.R:.(17.(86.R:.)(<.(74.$90.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))))R9.R7.)(91.Vsegs,R;.R:.R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 U Hsvc Hno Hfl Hpath Hh Hlazy Hcont.
  pose proof (openat_toolong_check segs ms x8 model Hno Hfl Hpath) as Hchk.
  apply (tfo_sys_det segs ms model x8
           (with_copyins (open_copyins ms)
             (mkEffect (errno_ret ENAMETOOLONG) [] [])) model U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_openat_enoent : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pp,(?.(1.&8.))PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R5.)(9.(1.&40.)R3.))P,(3.$68.(26.&40.R4.)+38.)P,(3.(1.&40.)(65.R7.#0.)$7=.)P,(3.$39.(3=.(31.R8.)(65.R8.#1.))(3;.R5.))P,(3.$68.(81.(26.&40.(65.R9.#2.))$82.)=)P,(3.$7>.(83.R7.)$84.)P,(3.(2.(?.(1.&8.)))(85.(67.R:.)R8.)(:.(?.(1.&8.))))P,(3.(2.(1.&40.))(4;.R;.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R<.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(5.(6.R>.(17.(86.R>.)(<.(74.$92.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))))R=.R:.)(91.Vsegs,R?.R>.R;.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 p U Hsvc Hno Hdirfd Hpath Hfl Hdot Hfs Hh Hlazy Hcont.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
                 = check_ret_only_copyins (open_copyins ms) eff
                     (errno_ret ENOENT) model []).
  { intro eff. rewrite (check_syscall_56 segs ms x8 eff model Hno).
    unfold check_openat.
    rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
    unfold Prelude.check_copyins_after, Open.check_openat_body.
    rewrite in_mem_si, Hpath. cbv beta iota zeta.
    (* [comment removed for export] *)
    destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
    - apply check_copyins_after_ret_only.
    - rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
      unfold Open.check_openat_resolved.
      rewrite Hunw. cbv beta iota.
      rewrite Hfl, Z.eqb_refl. cbv beta iota.
      unfold Open.check_openat_read. rewrite Hdot, Hfs.
      apply check_copyins_after_ret_only. }
  apply (tfo_sys_det segs ms model x8
           (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] []))
           model U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma tfo_read_file : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pp,$93.Poff,(1.&40.)Pdata,(?.(1.&8.))Pw,(?.(1.&8.))PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R8.)(9.(1.&40.)R6.))P,(3.$68.(26.&40.R7.)+3?.)P,(3.(2.$18.)(19.(75.R9.)(65.R:.#0.))(9.$18.(88.R7.R6.)))P,(3.(1.&40.)(6<.(65.R;.#0.))(65.R;.#0.))P,(3.(2.(?.(1.&8.)))(85.(67.R;.)R9.)(9.(?.(1.&8.))R7.))P,(3.(2.(?.(1.&8.)))(94.(95.Vsegs,R=.)(65.R=.#1.)(65.R=.#2.))(9.(?.(1.&8.))R7.))P,(96.(26.&40.(65.R>.#2.))$97.)P,(25.=(26.&40.(65.R?.#2.)))P,(3.$7>.(98.(65.R10.#1.)(26.&40.(65.R10.#2.)))$84.)P,(3.(2.(1.&40.))(4;.R10.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R11.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(5.(6.R13.(<.(99.(1.&8.)(29.R>.R?.(65.R13.#2.)))(9:.(65.R13.#1.)(29.R>.R?.(65.R13.#2.)))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.)))))(87.(21.(75.R12.)(65.R13.#0.)(88.R10.(36.&40.R?.(99.(1.&8.)(29.R>.R?.(65.R13.#2.))))))R12.)R<.)(91.Vsegs,R14.R13.R=.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 p off data w U Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok Hh Hlazy Hcont.
  set (bs := file_read data off (ms_gpr ms 2)).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min.
    unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
               (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
    - (* [comment removed for export] *)
      cbv beta iota.
      rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
      tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr].
        apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes].
        repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
        inversion Heff; subst.
        rewrite bv_eqb_refl.
        rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
        rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
              (FdFile p (off + len_word bs))) model) U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. apply Hchk. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
    unfold check_read in Hs.
    rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    rewrite in_wmem_si in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
    cbv beta iota in Hs.
    revert Hs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + discriminate.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma tfo_write_file : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pp,$93.Poff,(1.&40.)Pdata,(?.(1.&8.))Pbs,(?.(1.&8.))PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R8.)(9.(1.&40.)R6.))P,(3.$68.(26.&40.R7.)+40.)P,(3.(2.$18.)(19.(75.R9.)(65.R:.#0.))(9.$18.(8;.R7.R6.)))P,(3.(1.&40.)(6<.(65.R;.#0.))(65.R;.#0.))P,(3.(2.(?.(1.&8.)))(94.(31.R<.)(65.R<.#1.)(65.R<.#2.))(9.(?.(1.&8.))R6.))P,(96.(26.&40.(65.R=.#2.))$97.)P,(3.(2.(?.(1.&8.)))(85.(67.R=.)R;.)(9.(?.(1.&8.))R9.))P,(3.$7>.(1;.(9;.R:.R;.R9.))$80.)P,(3.$7>.(9<.(65.R10.#2.))$80.)P,(3.(2.(1.&40.))(4;.R10.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R11.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(5.(6.R13.(17.(22.(>.(1.&40.)$11.)(23.(1.&40.)$11.(65.R13.#1.)(28.(1.&8.)R=.))(=.(>.(1.&40.)$11.)))(<.(65.R13.#2.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.))))))(87.(21.(75.R12.)(65.R13.#0.)(8;.R10.(36.&40.R?.(65.R13.#2.))))(8<.(8=.(67.R12.)R10.(9=.R>.R?.R=.))R12.))R<.)(91.Vsegs,R14.R13.R=.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hnz Hh Hlazy Hcont.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
      exfalso. apply andb_prop in Hg' as [Hnz' Hz].
      apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
      rewrite Hz in Hlen. cbn in Hlen.
      assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
      unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hnz. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (with_copyins [(ms_gpr ms 1, length bs)]
             (mkEffect (ms_gpr ms 2) [] []))
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                        (FdFileW p (off + ms_gpr ms 2)))
              (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_write_file_zero : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pp,$93.Poff,(1.&40.)Pdata,(?.(1.&8.))Pbs,(?.(1.&8.))PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R8.)(9.(1.&40.)R6.))P,(3.$68.(26.&40.R7.)+40.)P,(3.(2.$18.)(19.(75.R9.)(65.R:.#0.))(9.$18.(8;.R7.R6.)))P,(3.(1.&40.)(6<.(65.R;.#0.))(65.R;.#0.))P,(3.(2.(?.(1.&8.)))(94.(31.R<.)(65.R<.#1.)(65.R<.#2.))(9.(?.(1.&8.))R6.))P,(96.(26.&40.(65.R=.#2.))$97.)P,(3.(2.(?.(1.&8.)))(85.(67.R=.)R;.)(9.(?.(1.&8.))R9.))P,(3.$7>.(1;.(9;.R:.R;.R9.))$80.)P,(3.$7>.(9<.(65.R10.#2.))$84.)P,(3.$7>.(98.(65.R11.#1.)(26.&40.(65.R11.#2.)))$84.)P,(3.(2.(1.&40.))(4;.R11.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R12.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(5.(6.R14.(<.(65.R14.#2.)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.)))))(87.(21.(75.R13.)(65.R14.#0.)(8;.R11.(36.&40.R10.(65.R14.#2.))))(8<.(8=.(67.R13.)R11.(9=.R?.R10.R>.))R13.))R=.)(91.Vsegs,R15.R14.R>.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hz Hok Hh Hlazy Hcont.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { rewrite Hz. reflexivity. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hz. cbv beta iota.
    unfold check_access_ok_zero. rewrite Hok. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (mkEffect (ms_gpr ms 2) [] [])
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                        (FdFileW p (off + ms_gpr ms 2)))
              (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma tfo_close : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pms,$4.Pmodel,$48.Px8,(1.&40.)Pe,$18.PU,P,(>.(1.&40.)$56.)SpP,(3.(2.(1.&40.))(4=.R5.)(9.(1.&40.)R3.))P,(3.$68.(26.&40.R4.)+39.)P,(3.(2.$18.)(19.(75.R6.)(65.R7.#0.))(9.$18.R4.))P,(3.(1.&40.)(6<.(65.R8.#0.))(65.R8.#0.))P,(3.(2.(1.&40.))(4;.R8.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R9.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(5.(6.R;.(<.(24.&40.=)(=.(>.(1.&40.)(?.(1.&8.))))(=.(>.(1.&40.)(1.&40.)))(=.(>.(1.&40.)(1.&40.)))(=.$10.)(=.(>.(1.&40.)$11.)))))(87.(9>.(75.R:.)(65.R;.#0.))R:.)R7.)(91.Vsegs,R<.R;.R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 e U Hsvc Hno Hfd Hfd32 Hh Hlazy Hcont.
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only eff (Z_to_bv 64 0)
        (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) []).
  { intro eff.
    rewrite (check_syscall_57 segs ms x8 eff model Hno). unfold check_close.
    rewrite Hfd32, Hfd. reflexivity. }
  apply (tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
           (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma record_gpr : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Pfr,(0.&5.(1.&40.))Ppc,(1.&40.)Psv,(2.(1.&40.))Prv,(2.(1.&40.))Pfc,(1.&20.)Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pk,$11.(3.(1.&40.)(65.(7.R9.R8.R7.R6.R5.R4.R3.R2.)R1.)(9?.R9.(24.&5.(41.+:.(42.R1.)))))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_exit_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pcode,(1.&40.)Pfsv,$56.P,(3.$68.(26.&40.(:0.R7.(14.&5.+11.$15.)))+5=.)P,(3.(1.&40.)(9?.R8.(14.&5.+:.$15.))R3.)P,(25.(26.&40.R4.)+100.)P,(3.$56.(67.R6.)R4.)(91.Vsegs,(7.R;.(8.Vfx,)R:.(9.(1.&40.)(:0.R;.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R9.R8.)R7.Lo,(>.(1.&40.)$56.)(3.(>.(1.&40.)$56.)R1.(23.(1.&40.)$56.R7.R6.)))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model code fsv H17 H10 Hc Hfs.
  subst fsv.
  eapply (tfo_exit segs _ model (getr regs 17)).
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - intro o. rewrite record_gpr, arg_reg_0.
    rewrite H10, (land_255_small code Hc). tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_read_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pfdv,(1.&40.)Pp,$93.Poff,(1.&40.)Pdata,(?.(1.&8.))Pbuf,(1.&40.)Pcnt,(1.&40.)PU,P,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R<.(14.&5.+11.$15.)))+3?.)P,(3.(1.&40.)(9?.R=.(14.&5.+:.$15.))R8.)P,(3.(1.&40.)(9?.R>.(14.&5.+;.$15.))R5.)P,(3.(1.&40.)(9?.R?.(14.&5.+<.$15.))R5.)P,(3.(2.$18.)(19.(75.R<.)R;.)(9.$18.(88.R:.R9.)))P,(3.(1.&40.)(6<.R<.)R<.)P,(3.(2.(?.(1.&8.)))(85.(67.R>.)R<.)(9.(?.(1.&8.))R:.))P,(3.$7>.(:1.Vsegs,R:.(2;.R9.))$84.)P,(96.(26.&40.R:.)$97.)P,(25.=(26.&40.R;.))P,(3.$7>.(98.R=.(26.&40.R<.))$84.)P,(3.(2.(1.&40.))(4;.R13.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R14.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(12.Vfx,(13.R19.(14.&5.+:.$15.)(99.(1.&8.)(29.R11.R12.R?.)))(16.R18.+4.)(:2.R17.R10.(29.R11.R12.R?.))R16.)(87.(21.(75.R15.)R14.(88.R13.(36.&40.R12.(99.(1.&8.)(29.R11.R12.R?.)))))R15.)R>.)(91.Vsegs,(7.R1:.(8.Vfx,)R19.(9.(1.&40.)(:0.R1:.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R18.R17.)R16.R?.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model fdv p off data buf cnt U
    H17 H10 H11 H12 Hfd Hfd32 Hfs Hwseg Hcnt Hpos Haok Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
  apply (tfo_read_file ms model (getr regs 17) p off data w U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - rewrite Hg0. exact Hfd.
  - rewrite Hg0. exact Hfd32.
  - exact Hfs.
  - rewrite Hg1, Hg2. exact Hw.
  - rewrite Hg2. exact Hcnt.
  - rewrite Hg2. exact Hpos.
  - rewrite Hg1, Hg2. exact Haok.
  - exact Hh.
  - exact Hlazy.
  - rewrite Hg0, Hg1, Hg2. unfold ms.
    rewrite adv_apply_delivered. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_write_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pfdv,(1.&40.)Pp,$93.Poff,(1.&40.)Pdata,(?.(1.&8.))Pbs,(?.(1.&8.))Pbuf,(1.&40.)Pcnt,(1.&40.)PU,P,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R<.(14.&5.+11.$15.)))+40.)P,(3.(1.&40.)(9?.R=.(14.&5.+:.$15.))R9.)P,(3.(1.&40.)(9?.R>.(14.&5.+;.$15.))R5.)P,(3.(1.&40.)(9?.R?.(14.&5.+<.$15.))R5.)P,(3.(2.$18.)(19.(75.R=.)R<.)(9.$18.(8;.R;.R:.)))P,(3.(1.&40.)(6<.R=.)R=.)P,(3.(2.(?.(1.&8.)))(34.Vsegs,R10.R9.(2;.R8.))(9.(?.(1.&8.))R:.))P,(96.(26.&40.R9.)$97.)P,(3.(2.(?.(1.&8.)))(85.(67.R11.)R?.)(9.(?.(1.&8.))R=.))P,(3.$7>.(1;.(9;.R>.R?.R=.))$80.)P,(5>.(3.$7>.(98.R=.(26.&40.R<.))$84.)(25.=(26.&40.R<.)))P,(3.(2.(1.&40.))(4;.R14.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R15.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(12.Vfx,(13.R19.(14.&5.+:.$15.)R?.)(16.R18.+4.)R17.(32.Vsegs,))(87.(21.(75.R16.)R15.(8;.R14.(36.&40.R13.R?.)))(8<.(8=.(67.R16.)R14.(9=.R12.R13.R11.))R16.))R>.)(91.Vsegs,(7.R1:.(8.Vfx,)R19.(9.(1.&40.)(:0.R1:.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R18.(32.Vsegs,))R17.R?.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem model fdv p off data bs buf cnt U
    H17 H10 H11 H12 Hfd Hfd32 Hrd Hcnt Hfs Hgap Hok Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (w_is0 cnt) eqn:Hz.
  - (* [comment removed for export] *)
    apply (tfo_write_file_zero ms model (getr regs 17) p off data bs U).
    + unfold ms. cbn [ms_svc_pending]. reflexivity.
    + exact H17.
    + rewrite Hg0. exact Hfd.
    + rewrite Hg0. exact Hfd32.
    + rewrite Hg1, Hg2.
      rewrite read_bytes_map_read_byte.
      rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
      exact Hrd.
    + rewrite Hg2. exact Hcnt.
    + exact Hfs.
    + exact Hgap.
    + rewrite Hg2. exact Hz.
    + destruct Hok as [Hfl | Hp].
      * rewrite Hg1, Hg2. exact Hfl.
      * (* [comment removed for export] *)
        rewrite (w_is0_pos cnt Hp) in Hz. discriminate.
    + exact Hh.
    + exact Hlazy.
    + rewrite Hg0, Hg2. unfold ms.
      rewrite adv_eff_ret. exact Hcont.
  - (* [comment removed for export] *)
    apply (tfo_write_file ms model (getr regs 17) p off data bs U).
    + unfold ms. cbn [ms_svc_pending]. reflexivity.
    + exact H17.
    + rewrite Hg0. exact Hfd.
    + rewrite Hg0. exact Hfd32.
    + rewrite Hg1, Hg2.
      rewrite read_bytes_map_read_byte.
      rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
      exact Hrd.
    + rewrite Hg2. exact Hcnt.
    + exact Hfs.
    + exact Hgap.
    + rewrite Hg2. exact Hz.
    + exact Hh.
    + exact Hlazy.
    + rewrite Hg0, Hg2. unfold ms.
      rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_close_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pfdv,(1.&40.)Pe,$18.PU,P,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R8.(14.&5.+11.$15.)))+39.)P,(3.(1.&40.)(9?.R9.(14.&5.+:.$15.))R4.)P,(3.(2.$18.)(19.(75.R6.)R5.)(9.$18.R4.))P,(3.(1.&40.)(6<.R6.)R6.)P,(3.(2.(1.&40.))(4;.R8.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R9.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(12.Vfx,(13.R>.(14.&5.+:.$15.)(24.&40.=))(16.R=.+4.)R<.R;.)(87.(9>.(75.R:.)R9.)R:.)R7.)(91.Vsegs,(7.R?.(8.Vfx,)R>.(9.(1.&40.)(:0.R?.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R=.R<.)R;.R8.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model fdv e U H17 H10 Hfd Hfd32 Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  apply (tfo_close ms model (getr regs 17) e U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - rewrite Hg0. exact Hfd.
  - rewrite Hg0. exact Hfd32.
  - exact Hh.
  - exact Hlazy.
  - rewrite Hg0. unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_open_enoent_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pp,(?.(1.&8.))PU,P,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R6.(14.&5.+11.$15.)))+38.)P,(3.(1.&40.)(9?.R7.(14.&5.+:.$15.))$7=.)P,(3.(1.&40.)(9?.R8.(14.&5.+<.$15.))(24.&40.=))P,(3.$39.(3=.(33.Vsegs,R7.)(9?.R9.(14.&5.+;.$15.)))(3;.R5.))P,(3.$7>.(83.R6.)$84.)P,(3.(2.(?.(1.&8.)))(85.(67.R8.)R7.)(:.(?.(1.&8.))))P,(3.(2.(1.&40.))(4;.R9.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R:.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(12.Vfx,(13.R>.(14.&5.+:.$15.)(74.$92.))(16.R=.+4.)R<.(32.Vsegs,))R;.R9.)(91.Vsegs,(7.R?.(8.Vfx,)R>.(9.(1.&40.)(:0.R?.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R=.(32.Vsegs,))R<.R:.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem model p U H17 H10 H12 Hpath Hdot Hfs Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_openat_enoent ms model (getr regs 17) p U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
    vm_compute. reflexivity.
  - exact Hdot.
  - exact Hfs.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_open_rd_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pp,(?.(1.&8.))Pd,(?.(1.&8.))PTe,P,$68.P,(>.(1.&40.)$56.)SpPTs,P,(1.&40.)P,(>.(1.&40.)$56.)SpPU,Px,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R9.(14.&5.+11.$15.)))+38.)P,(3.(1.&40.)(9?.R:.(14.&5.+:.$15.))$7=.)P,(3.(1.&40.)(9?.R;.(14.&5.+<.$15.))(24.&40.=))P,(3.$39.(3=.(33.Vsegs,R:.)(9?.R<.(14.&5.+;.$15.)))(3;.R8.))P,(3.$7>.(7?.R9.(=.(1.&8.)))$80.)P,(3.$7>.(83.R:.)$84.)P,(3.(2.(?.(1.&8.)))(85.(67.R<.)R;.)(9.(?.(1.&8.))R:.))P,(3.(2.(1.&40.))(4;.R=.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R>.)(=.(>.(1.&40.)(1.&40.))))P,Pe,$68.P,(38.$68.R1.$73.)(91.Vsegs,(12.Vfx,(13.R14.(14.&5.+:.$15.)(74.R2.))(16.R13.+4.)R12.(32.Vsegs,))R11.A1.R>.R2.)P,Pfd,(1.&40.)P,(3.(2.$18.)(19.(75.R11.)R1.)(:.$18.))P,(3.(1.&40.)R2.(76.(75.R12.)))(91.Vsegs,(12.Vfx,(13.R16.(14.&5.+:.$15.)R3.)(16.R15.+4.)R14.(32.Vsegs,))(87.(21.(75.R13.)R3.(88.R12.(24.&40.=)))R13.)A1.R?.R3.)P,Po,(>.(1.&40.)$56.)(70.A1.R=.R1.(5>.(1?.$68.Le,$68.(20.(38.$68.R1.$73.)A2.R10.R1.R2.))(1?.(1.&40.)Lfd,(1.&40.)(20.(3.(2.$18.)(19.(75.R13.)R1.)(:.$18.))(20.(3.(1.&40.)R1.(76.(75.R13.)))A2.R?.R1.R2.)))))(91.Vsegs,(7.R15.(8.Vfx,)R14.(9.(1.&40.)(:0.R15.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R13.(32.Vsegs,))R12.R=.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem model p d Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hfs Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile p (Z_to_bv 64 0))) model)
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_rd_check segs ms (getr regs 17) model p d).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    + exact Hdot.
    + exact Hfs.
  - intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_open_wr_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pp,(?.(1.&8.))PTe,P,$68.P,(>.(1.&40.)$56.)SpPTs,P,(1.&40.)P,(>.(1.&40.)$56.)SpPU,Px,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R8.(14.&5.+11.$15.)))+38.)P,(3.(1.&40.)(9?.R9.(14.&5.+:.$15.))$7=.)P,(3.(1.&40.)(9?.R:.(14.&5.+<.$15.))(24.&40.+241.))P,(3.$39.(3=.(33.Vsegs,R9.)(9?.R;.(14.&5.+;.$15.)))(3;.R7.))P,(3.$7>.(7?.R8.(=.(1.&8.)))$80.)P,(3.$7>.(83.R9.)$84.)P,(3.$7>.(8:.(67.R;.)R:.)$80.)P,(3.(2.(1.&40.))(4;.R<.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R=.)(=.(>.(1.&40.)(1.&40.))))P,Pe,$68.P,(38.$68.R1.$73.)(91.Vsegs,(12.Vfx,(13.R13.(14.&5.+:.$15.)(74.R2.))(16.R12.+4.)R11.(32.Vsegs,))R10.A1.R>.R2.)P,Pfd,(1.&40.)P,(3.(2.$18.)(19.(75.R10.)R1.)(:.$18.))P,(3.(1.&40.)R2.(76.(75.R11.)))(91.Vsegs,(12.Vfx,(13.R15.(14.&5.+:.$15.)R3.)(16.R14.+4.)R13.(32.Vsegs,))(87.(21.(75.R12.)R3.(8;.R11.(24.&40.=)))(8<.(8=.(67.R12.)R11.(=.(1.&8.)))R12.))A1.R?.R3.)P,Po,(>.(1.&40.)$56.)(70.A1.R=.R1.(5>.(1?.$68.Le,$68.(20.(38.$68.R1.$73.)A2.R10.R1.R2.))(1?.(1.&40.)Lfd,(1.&40.)(20.(3.(2.$18.)(19.(75.R12.)R1.)(:.$18.))(20.(3.(1.&40.)R1.(76.(75.R12.)))A2.R?.R1.R2.)))))(91.Vsegs,(7.R14.(8.Vfx,)R13.(9.(1.&40.)(:0.R14.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R12.(32.Vsegs,))R11.R=.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem model p Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW p (Z_to_bv 64 0)))
                        (with_fs (fs_set (m_fs model) p []) model))
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_wr_check segs ms (getr regs 17) model p).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    + exact Hdot.
    + exact Hun.
  - intro fd. split.
    + rewrite with_fds_halted, with_fs_halted. exact Hh.
    + exact Hlazy.
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_open_wr_isdir_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$48.Pp,(?.(1.&8.))PU,P,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R6.(14.&5.+11.$15.)))+38.)P,(3.(1.&40.)(9?.R7.(14.&5.+:.$15.))$7=.)P,(3.(1.&40.)(9?.R8.(14.&5.+<.$15.))(24.&40.+241.))P,(3.$39.(3=.(33.Vsegs,R7.)(9?.R9.(14.&5.+;.$15.)))(3;.R5.))P,(3.$7>.(7?.R6.(=.(1.&8.)))$80.)P,(3.$7>.(83.R7.)$84.)P,(3.$7>.(8:.(67.R9.)R8.)$84.)P,(3.(2.(1.&40.))(4;.R:.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R;.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(12.Vfx,(13.R?.(14.&5.+:.$15.)(74.$8>.))(16.R>.+4.)R=.(32.Vsegs,))R<.R:.)(91.Vsegs,(7.R10.(8.Vfx,)R?.(9.(1.&40.)(:0.R10.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R>.(32.Vsegs,))R=.R;.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem model p U H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hchk : forall eff,
      check_syscall (sys_input segs ms (getr regs 17)) eff model
      = check_ret_only_copyins (open_copyins ms) eff
          (errno_ret EISDIR) model []).
  { intro eff. apply (openat_wr_isdir_check segs ms (getr regs 17) model p).
    - exact H17.
    - unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    - unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    - exact Hpe.
    - unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    - exact Hdot.
    - exact Hun. }
  apply (tfo_sys_det segs ms model (getr regs 17)
           (with_copyins (open_copyins ms)
             (mkEffect (errno_ret EISDIR) [] [])) model U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tfo_open_toolong_rec : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Pregs,(0.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$48.PU,P,(>.(1.&40.)$56.)SpP,(3.$68.(26.&40.(:0.R5.(14.&5.+11.$15.)))+38.)P,(3.$7>.(8?.(9?.R6.(14.&5.+<.$15.)))$84.)P,(3.$39.(3=.(33.Vsegs,R5.)(9?.R7.(14.&5.+;.$15.)))$3>.)P,(3.(2.(1.&40.))(4;.R5.)(:.(1.&40.)))P,(3.(?.(>.(1.&40.)(1.&40.)))(4<.R6.)(=.(>.(1.&40.)(1.&40.))))P,(91.Vsegs,(12.Vfx,(13.R:.(14.&5.+:.$15.)(74.$90.))(16.R9.+4.)R8.(32.Vsegs,))R7.R6.)(91.Vsegs,(7.R;.(8.Vfx,)R:.(9.(1.&40.)(:0.R;.(14.&5.+11.$15.)))(:.(1.&40.))(;.Vfx,)R9.(32.Vsegs,))R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem model U H17 Hfl Hpath Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_openat_toolong ms model (getr regs 17) U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

End OpenNodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fout_omni_run : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Ppc,$:3.Pph,$3?.Psp,(1.&40.)Pbrk0,(1.&40.)Pmb,(1.&40.)Prnd,$40.Plim,$68.Pinp,$:4.PU,P,(>.(1.&40.)$56.)SpP,(91.R:.(:5.R:.R9.R8.R7.R4.(:6.R2.)(:7.R2.)(:8.R2.)(:9.R2.))(::.(:;.R:.)R6.R5.R7.R3.R2.)R1.)(:<.(:=.R;.R:.R9.)R4.(:>.R8.R7.R6.R5.)R3.(:?.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  cbn [omni_run]. unfold init_config.
  exact (to_fout_exec segs _ _ U Hto eq_refl eq_refl).
Qed.

#[using="Type"] Lemma fout_obs_iff : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Ppc,$:3.Pph,$3?.Psp,(1.&40.)Pbrk0,(1.&40.)Pmb,(1.&40.)Prnd,$40.Plim,$68.Pinp,$:4.PU,P,(>.(1.&40.)$56.)SpP,(91.R:.(:5.R:.R9.R8.R7.R4.(:6.R2.)(:7.R2.)(:8.R2.)(:9.R2.))(::.(:;.R:.)R6.R5.R7.R3.R2.)R1.)Ptr,(?.$49.)(70.(;0.R<.(;1.R<.R;.R:.R9.R8.R7.R6.R5.R4.)R1.)(1?.(>.(1.&40.)$56.)Lo,(>.(1.&40.)$56.)(20.A1.R4.R1.(5<.$49.R2.(5=.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
    by reflexivity.
  assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [])
    by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_fout_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
      as (o & Ho & Hp').
    exists o. split; [exact Ho | eapply is_prefix_trans; eauto].
  - intros (o & Ho & Hp).
    destruct (to_fout_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    exists (fout_trace o), c. split; assumption.
Qed.

#[using="Type"] Lemma fout_no_error_run : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Ppc,$:3.Pph,$3?.Psp,(1.&40.)Pbrk0,(1.&40.)Pmb,(1.&40.)Prnd,$40.Plim,$68.Pinp,$:4.PU,P,(>.(1.&40.)$56.)SpP,(91.R:.(:5.R:.R9.R8.R7.R4.(:6.R2.)(:7.R2.)(:8.R2.)(:9.R2.))(::.(:;.R:.)R6.R5.R7.R3.R2.)R1.)(1>.(61.R;.(;1.R;.R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
  eapply exec_conseq; [exact (fout_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fout_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psource_segs,(?.$30.)Prpc,$:3.Prph,$3?.Prsp,(1.&40.)Prbrk,(1.&40.)Prmb,(1.&40.)Prrnd,$40.Ptarget_segs,(?.$30.)Papc,$:3.Paph,$3?.Pasp,(1.&40.)Pabrk,(1.&40.)Pamb,(1.&40.)Parnd,$40.PU,P,(>.(1.&40.)$56.)SpPinp,$:4.P,(91.R10.(:5.R10.R?.R>.R=.R:.(:6.R1.)(:7.R1.)(:8.R1.)(:9.R1.))(::.(:;.R10.)R<.R;.R=.$;2.R1.)R2.)P,(91.R:.(:5.R:.R9.R8.R7.R4.(:6.R2.)(:7.R2.)(:8.R2.)(:9.R2.))(::.(:;.R:.)R6.R5.R7.$;3.R2.)R3.)(;4.(:=.R12.R11.R10.)(:=.R;.R:.R9.)(:>.R?.R>.R=.R<.)(:>.R8.R7.R6.R5.)R3.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fout_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psource_segs,(?.$30.)Prpc,$:3.Prph,$3?.Prsp,(1.&40.)Prbrk,(1.&40.)Prmb,(1.&40.)Prrnd,$40.Prlim,$68.Ptarget_segs,(?.$30.)Papc,$:3.Paph,$3?.Pasp,(1.&40.)Pabrk,(1.&40.)Pamb,(1.&40.)Parnd,$40.Palim,$68.PU,P,(>.(1.&40.)$56.)SpPinp,$:4.P,(91.R12.(:5.R12.R11.R10.R?.R<.(:6.R1.)(:7.R1.)(:8.R1.)(:9.R1.))(::.(:;.R12.)R>.R=.R?.R;.R1.)R2.)P,(91.R;.(:5.R;.R:.R9.R8.R5.(:6.R2.)(:7.R2.)(:8.R2.)(:9.R2.))(::.(:;.R;.)R7.R6.R8.R4.R2.)R3.)(20.(;5.(;6.(:=.R14.R13.R12.)R=.(:>.R11.R10.R?.R>.)R3.))(;7.(;6.(:=.R14.R13.R12.)R=.(:>.R11.R10.R?.R>.)R3.)(;6.(:=.R<.R;.R:.)R5.(:>.R9.R8.R7.R6.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
    rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
    reflexivity.
  - cbn. apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma spec_err_escape_equiv : ltac2:(CDefT.buildp (gd_tbl_FileSim ()) "Psegs,(?.$30.)Ppc,$:3.Pph,$3?.Psp,(1.&40.)Pbrk0,(1.&40.)Pmb,(1.&40.)Prnd,$40.Plim,$68.Pinp,$:4.Ptarget,$;8.P,(63.R:.(;1.R:.R9.R8.R7.R6.R5.R4.R3.R2.))(;7.(;6.(:=.R;.R:.R9.)R4.(:>.R8.R7.R6.R5.)R3.)R2.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target Hall.
  left. exact Hall.
Qed.
End WithFP1.
