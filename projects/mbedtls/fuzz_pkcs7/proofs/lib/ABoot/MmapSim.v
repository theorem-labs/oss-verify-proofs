(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MmapSim () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.ABoot.PropExec.v_srli"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.Riscv.Instr.SZ1"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.bv_signed"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.KrLib.ABoot.CatExec.wbytes"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.app"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "WithFP1.zfill"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_destroyed"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.map_remove"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.leb"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "WithFP1.grant_ok"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "WithFP1.mmap_args_ok"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "WithFP1.page_round_up"; "LinuxProcessSemantics.LinuxProcessSem.Monad.outcome"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.munmap_spec"; "WithFP1.munmap_args_ok"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "WithFP1.munmap_eff"; "WithFP1.munmap_model"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_spec"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.errno_ret_in"; "WithFP1.mmap_model"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "WithFP1.unfill"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "WithFP1.WithSegs.twm"; "WithFP1.WithSegs.twm_tail"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.outcome"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "OSSVerify.KrLib.ABoot.CatSim.wevents"; "LinuxProcessSemantics.LinuxProcessSem.State.ExitEv"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exits_with"; "OSSVerify.KrLib.ABoot.CatSim.bufs_modeled"; "OSSVerify.KrLib.ABoot.CatSim.fd1chan"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec"; "WithFP1.WithSegs.twm_post"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "WithFP1.WithSegs.twm_pend"; "OSSVerify.KrLib.ABoot.CatSim.buf_modeled"; "WithFP1.WithSegs.twm_rest_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "WithFP1.WithSegs.tmw"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "WithFP1.WithSegs.tmw_post"; "WithFP1.WithSegs.two_traces"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.errors"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "WithFP1.two_traces"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "WithFP1.tmw"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "WithFP1.tmw_post"; "LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma v_srli_div : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Px,(0.&40.)Psh,$1.P,(2.(3.=R1.)(4.R1.+40.))(5.$1.(6.&40.(7.R3.R2.))(8.(6.&40.R3.)(9.+2.R2.)))")
(* [comment removed for export] *).
Proof.
  intros x sh Hsh. unfold v_srli.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (u64_range x) as Hx.
  assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
    by (apply Z.div_le_upper_bound; nia).
  assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sb_any : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pw,(0.&20.)Prs1,(0.&5.)Prs2,(0.&5.)Pimm,(0.&<.)P,(5.(=.(0.&20.))(>.R9.R7.)(?.(0.&20.)R4.))P,(5.$10.(11.R5.)$12.)P,(5.(=.(13.$14.$1.))(15.R6.)(?.(13.$14.$1.)(16.$14.$1.(17.$18.R5.R4.R3.)+4.)))P,(5.$10.(19.R<.R9.(1:.(1;.R;.R6.)(1<.&<.R4.))#1.)$1=.)(5.(1>.$1?.)(20.R=.(21.Vfx,R<.R;.R:.R9.))(22.$1?.(21.Vfx,R<.(1:.R;.+4.)(23.R:.(1:.(1;.R<.R7.)(1<.&<.R5.))(24.(0.&8.)(25.&8.(6.&40.(1;.R<.R6.)))(26.(0.&8.))))R9.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  rewrite <- N_to_le_bytes_1_small.
  apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sb_at : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pw,(0.&20.)Prs1,(0.&5.)Prs2,(0.&5.)Pimm,(0.&<.)Pa,(0.&40.)Pv,(0.&40.)Pb,(0.&8.)P,(5.(=.(0.&20.))(>.R<.R:.)(?.(0.&20.)R7.))P,(5.$10.(11.R8.)$12.)P,(5.(=.(13.$14.$1.))(15.R9.)(?.(13.$14.$1.)(16.$14.$1.(17.$18.R8.R7.R6.)+4.)))P,(5.(0.&40.)(1:.(1;.R>.R9.)(1<.&<.R7.))R6.)P,(5.(0.&40.)(1;.R?.R9.)R6.)P,(5.(0.&8.)(25.&8.(6.&40.R7.))R6.)P,(5.$10.(19.R12.R?.R9.#1.)$1=.)(5.(1>.$1?.)(20.R13.(21.Vfx,R12.R11.R10.R?.))(22.$1?.(21.Vfx,R12.(1:.R11.+4.)(23.R10.R:.(24.(0.&8.)R8.(26.(0.&8.))))R?.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
  rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wbytes_snoc : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pbs,(:.(0.&8.))Pm,P,(0.&40.)(=.(0.&8.))Pa,(0.&40.)Pb,(0.&8.)(5.P,(0.&40.)(=.(0.&8.))(23.R3.R2.(27.(0.&8.)R4.(24.(0.&8.)R1.(26.(0.&8.)))))(23.(23.R3.R2.R4.)(28.&40.R2.(29.(2:.(0.&8.)R4.)))(24.(0.&8.)R1.(26.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  induction bs as [|x bs IH]; intros m a b.
  - cbn [app wbytes length]. rewrite word_add_0. reflexivity.
  - cbn [app wbytes length].
    rewrite IH. f_equal.
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

#[using="Type"] Lemma zfill_out : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pa,(0.&40.)Pn,(0.&40.)Pm,P,(0.&40.)(=.(0.&8.))Px,(0.&40.)P,(2;.(4.(6.&40.R1.)(6.&40.R4.))(3.(2<.(6.&40.R4.)(6.&40.R3.))(6.&40.R1.)))(5.(=.(0.&8.))(2=.R5.R4.R3.R2.)A1.R3.R2.)")
(* [comment removed for export] *).
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_zfill_out : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pa,(0.&40.)Pn,(0.&40.)Pm,P,(0.&40.)(=.(0.&8.))Px,(0.&40.)Pk,$2>.P,(3.(2<.(6.&40.R2.)(2?.R1.))(9.+2.+40.))P,(2;.(3.(2<.(6.&40.R3.)(2?.R2.))(6.&40.R6.))(3.(2<.(6.&40.R6.)(6.&40.R5.))(6.&40.R3.)))(5.(=.(:.(0.&8.)))(30.R8.(2=.R7.R6.R5.)R4.R3.)(30.R8.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "(31.O3.O2.(32.(33.(34.O1.))(35.(36.(34.O1.))O3.)(37.(38.(34.O1.))(6.&40.O3.)(2<.(6.&40.O3.)(6.&40.O2.)))(39.(34.O1.))(3:.(34.O1.))(3;.(34.O1.))(3<.(34.O1.))(3=.(34.O1.)))O1.)")
(* [comment removed for export] *).

Definition mmap_model (a n : word) (m : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "(3>.(32.(33.(34.O1.))(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)O3.O2.)(36.(34.O1.)))(38.(34.O1.))(39.(34.O1.))(3:.(34.O1.))(3;.(34.O1.))(3<.(34.O1.))(3=.(34.O1.)))O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "(3?.(3?.(3?.(3?.(40.(41.(6.&40.O2.)$42.)=)(43.=(6.&40.O2.)))(44.(2<.(6.&40.O2.)O1.)(45.(34.O3.))))(46.(27.(13.(0.&40.)(0.&40.))(33.(34.O3.))(36.(34.O3.)))O2.(25.&40.O1.)))(44.(2<.(47.O3.)O1.)(3;.(34.O3.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. intros addr n m H. exact H. Qed.
#[using="Type"] Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
#[using="Type"] Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. intros a n m H. exact H. Qed.
#[using="Type"] Lemma mmap_model_lazy : forall a n m,
  m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_ok_unpack : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Phint,(0.&40.)Pm,$48.Pa,(0.&40.)Pn,$1.P,(5.$10.(49.R4.R3.R2.R1.)$1=.)(2.(5.$1.(41.(6.&40.R3.)$42.)=)(2.(4.=(6.&40.R3.))(2.(3.(2<.(6.&40.R3.)R2.)(45.(34.R4.)))(2.(5.$10.(46.(27.(13.(0.&40.)(0.&40.))(33.(34.R4.))(36.(34.R4.)))R3.(25.&40.R2.))$1=.)(3.(2<.(47.R4.)R2.)(3;.(34.R4.)))))))")
(* [comment removed for export] *).
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H5.
  auto 7.
Qed.

#[using="Type"] Lemma region_free_cons : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pb,(0.&40.)Ps,(0.&40.)Pr,(:.(13.(0.&40.)(0.&40.)))Plo,(0.&40.)Pn,(0.&40.)P,(5.$10.(46.(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)R5.R4.)R3.)R2.R1.)$1=.)(2.(2;.(3.(2<.(6.&40.R3.)(6.&40.R2.))(6.&40.R6.))(3.(2<.(6.&40.R6.)(6.&40.R5.))(6.&40.R3.)))(5.$10.(46.R4.R3.R2.)$1=.))")
(* [comment removed for export] *).
Proof.
  intros b s r lo n H. cbn [region_free] in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [|exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  apply andb_false_iff in H1.
  destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.

#[using="Type"] Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.

#[using="Type"] Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "(2.(4:.(5.(0.&40.)(4;.O1.#1.)(25.&40.=)))(2.(5.(0.&40.)(4;.O1.#2.)(25.&40.+3.))(2.(5.(0.&40.)(4;.O1.#3.)(25.&40.+22.))(2.(5.(0.&40.)(4;.O1.#4.)(25.&40.-1.))(5.(0.&40.)(4;.O1.#5.)(25.&40.=))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_args_ok_gates : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.P,(4<.R1.)(2.(5.$10.(4=.(4;.R2.#5.))$1=.)(2.(5.$10.(4>.(4;.R2.#3.))$1=.)(2.(5.$10.(4?.(4;.R2.#1.))$12.)(5.$10.(50.(4;.R2.#2.)(4;.R2.#3.)(4;.R2.#5.))$1=.))))")
(* [comment removed for export] *).
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "(2.(5.$1.(41.(6.&40.(4;.O2.#0.))$42.)=)(2.(4:.(5.(0.&40.)(4;.O2.#1.)(25.&40.=)))(2.(3.(2<.(6.&40.(4;.O2.#0.))(51.(6.&40.(4;.O2.#1.))))$52.)(5.$10.(53.(36.(34.O1.))(4;.O2.#0.)(54.(4;.O2.#1.)))$1=.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

(* [comment removed for export] *)
#[using="Type"] Lemma syscall_spec_munmap : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.Po,(55.$56.)P,(5.$1.(6.&40.R3.)+=7.)(57.(58.(59.R6.R5.R4.)R3.R2.)(5:.(4;.R5.#0.)(4;.R5.#1.)(59.R6.R5.R4.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if w_is0 r
           && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms model eff (Hal & Hlen & Hnw & Hhas).
  unfold check_munmap.
  rewrite (proj2 (Z.eqb_eq _ _) Hal).
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  cbn [negb orb]. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.

#[using="Type"] Lemma munmap_ok : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.P,(5.$1.(6.&40.R2.)+=7.)P,(5;.R4.R2.)(58.(59.R6.R5.R4.)R3.(5<.$56.(5=.R5.)(5>.(4;.R5.#0.)(54.(4;.R5.#1.))R3.)(26.$5?.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno Ha.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  unfold munmap_eff, w_is0. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

#[using="Type"] Lemma munmap_ok_inv : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.Peff,$56.Pmodel',$48.Pevs,(:.$5?.)P,(5.$1.(6.&40.R5.)+=7.)P,(5;.R7.R5.)P,(58.(59.R9.R8.R7.)R6.(5<.$56.R5.R4.R3.))(2.(5.$56.R6.(5=.R9.))(2.(5.$48.R5.(5>.(4;.R9.#0.)(54.(4;.R9.#1.))R7.))(5.(:.$5?.)R4.(26.$5?.))))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply check_munmap_complete_ok in Hspec.
  rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?]|]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (w_is0 r
            && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
    eqn:HC; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in HC as [Hr Hus].
  unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
  apply listNN_eqb_eq in Hus; subst us.
  unfold munmap_eff. auto.
Qed.

#[using="Type"] Lemma munmap_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.P,(5.$1.(6.&40.R2.)+=7.)P,(5;.R4.R2.)(4:.(58.(59.R6.R5.R4.)R3.(60.$56.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
  destruct (w_is0 (Z_to_bv 64 0)
            && listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma syscall_spec_mmap : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.Po,(55.$56.)P,(5.$1.(6.&40.R3.)+=>.)(57.(58.(59.R6.R5.R4.)R3.R2.)(61.(4;.R5.#0.)(4;.R5.#1.)(4;.R5.#2.)(4;.R5.#3.)(4;.R5.#4.)(4;.R5.#5.)(59.R6.R5.R4.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

#[using="Type"] Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.

#[using="Type"] Lemma mmap_errno_range : forall e,
  In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.

#[using="Type"] Lemma mmap_fail_ok : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.Pe,$1.P,(5.$1.(6.&40.R3.)+=>.)P,(4<.R5.)P,(62.$1.R3.$63.)(58.(59.R8.R7.R6.)R5.(5<.$56.(64.(65.R4.)(26.(13.(0.&40.)(:.(0.&8.))))(26.(13.(0.&40.)(0.&40.)))(26.(13.(0.&40.)(0.&40.)))(26.$66.)(26.(13.(0.&40.)$2>.)))R5.(26.$5?.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_not_errno : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Phint,(0.&40.)Pmodel,$48.Pa,(0.&40.)Pn,$1.P,(3.=R1.)P,(5.$10.(49.R5.R4.R3.R2.)$1=.)(5.$10.(67.$63.R4.)$12.)")
(* [comment removed for export] *).
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

#[using="Type"] Lemma mmap_succ_ok : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.Pa,(0.&40.)P,(5.$1.(6.&40.R3.)+=>.)P,(4<.R5.)P,(5.$10.(49.(4;.R6.#0.)R4.R3.(51.(6.&40.(4;.R6.#1.))))$1=.)(58.(59.R8.R7.R6.)R5.(5<.$56.(64.R4.(26.(13.(0.&40.)(:.(0.&8.))))(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)R4.(54.(4;.R7.#1.)))(26.(13.(0.&40.)(0.&40.))))(26.(13.(0.&40.)(0.&40.)))(26.$66.)(26.(13.(0.&40.)$2>.)))(68.R4.(54.(4;.R7.#1.))R5.)(26.$5?.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model a Hno Ha Hg.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite (grant_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[[H1 H2] H3] H4] H5].
  rewrite Hflags.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
  rewrite H1, H2, H3, H4, H5.
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

#[using="Type"] Lemma mmap_ok_inv : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.Peff,$56.Pmodel',$48.Pevs,(:.$5?.)P,(5.$1.(6.&40.R5.)+=>.)P,(4<.R7.)P,(58.(59.R9.R8.R7.)R6.(5<.$56.R5.R4.R3.))(2.(5.(:.$5?.)R4.(26.$5?.))(2;.(69.$1.Le,$1.(2.(62.$1.R1.$63.)(2.(5.$56.R7.(64.(65.R1.)(26.(13.(0.&40.)(:.(0.&8.))))(26.(13.(0.&40.)(0.&40.)))(26.(13.(0.&40.)(0.&40.)))(26.$66.)(26.(13.(0.&40.)$2>.))))(5.$48.R6.R8.))))(69.(0.&40.)La,(0.&40.)(2.(5.$10.(49.(4;.R:.#0.)R8.R1.(51.(6.&40.(4;.R:.#1.))))$1=.)(2.(5.$56.R7.(64.R1.(26.(13.(0.&40.)(:.(0.&8.))))(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)R1.(54.(4;.R:.#1.)))(26.(13.(0.&40.)(0.&40.))))(26.(13.(0.&40.)(0.&40.)))(26.$66.)(26.(13.(0.&40.)$2>.))))(5.$48.R6.(68.R1.(54.(4;.R:.#1.))R8.)))))))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hflags in Hspec.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite Hnr in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
    cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
              && (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
              && region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
              && (vm_backing_used model
                  + page_round_up_Z (bv_unsigned (ms_gpr ms 1))
                  <=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
      rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + unfold grant_ok. exact Hcond.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

#[using="Type"] Lemma mmap_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pms,$1?.Px8,(0.&40.)Pmodel,$48.P,(5.$1.(6.&40.R2.)+=>.)P,(4<.R4.)(4:.(58.(59.R6.R5.R4.)R3.(60.$56.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma adv_mmap_grant : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Psv,(=.(0.&40.))Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pa,(0.&40.)Pn,(0.&40.)(5.$1?.(6:.(6;.(6<.R7.(6=.Vfx,)R6.R5.(6>.(0.&40.))(6?.Vfx,)R4.R3.)(64.R2.(26.(13.(0.&40.)(:.(0.&8.))))(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)R2.R1.)(26.(13.(0.&40.)(0.&40.))))(26.(13.(0.&40.)(0.&40.)))(26.$66.)(26.(13.(0.&40.)$2>.)))))(21.Vfx,(70.R7.(71.&5.+:.$72.)R2.)(1:.R6.+4.)(2=.R2.R1.R4.)R3.))")
(* [comment removed for export] *).
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
  fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
              && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
           then None else m x.

#[using="Type"] Lemma unfill_out : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pa,(0.&40.)Pn,(0.&40.)Pm,P,(0.&40.)(=.(0.&8.))Px,(0.&40.)P,(2;.(4.(6.&40.R1.)(6.&40.R4.))(3.(2<.(6.&40.R4.)(6.&40.R3.))(6.&40.R1.)))(5.(=.(0.&8.))(73.R5.R4.R3.R2.)A1.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros a n m x Hx. unfold unfill.
  destruct Hx as [Hx | Hx].
  - rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
    rewrite andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma rdn_unfill_out : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Pa,(0.&40.)Pn,(0.&40.)Pm,P,(0.&40.)(=.(0.&8.))Px,(0.&40.)Pk,$2>.P,(3.(2<.(6.&40.R2.)(2?.R1.))(9.+2.+40.))P,(2;.(3.(2<.(6.&40.R3.)(2?.R2.))(6.&40.R6.))(3.(2<.(6.&40.R6.)(6.&40.R5.))(6.&40.R3.)))(5.(=.(:.(0.&8.)))(30.R8.(73.R7.R6.R5.)R4.R3.)(30.R8.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros y Hy. apply unfill_out. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_munmap : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Psv,(=.(0.&40.))Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pa,(0.&40.)Pn,(0.&40.)(5.$1?.(6:.(6;.(6<.R7.(6=.Vfx,)R6.R5.(6>.(0.&40.))(6?.Vfx,)R4.R3.)(64.(25.&40.=)(26.(13.(0.&40.)(:.(0.&8.))))(26.(13.(0.&40.)(0.&40.)))(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)R2.R1.)(26.(13.(0.&40.)(0.&40.))))(26.$66.)(26.(13.(0.&40.)$2>.)))))(21.Vfx,(70.R7.(71.&5.+:.$72.)(25.&40.=))(1:.R6.+4.)(73.R2.R1.R4.)R3.))")
(* [comment removed for export] *).
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
               = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
    (1 <= length buf)%nat ->
    twm_pend ms model buf bufs code ->
    twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(* [comment removed for export] *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
         (skipn n rest) bufs code) ->
    twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
    twm ms model bufs code ->
    twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
    (1 <= length rest)%nat ->
    twm_pend ms model rest bufs code ->
    twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm_tail ms' model rest bufs code ->
    twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
  with twm_pend_min := Minimality for twm_pend Sort Prop
  with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

#[using="Type"] Lemma msteps_twm : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pms',$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(74.Vsegs,R5.R4.)P,(75.R5.R4.R3.R2.)(75.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model bufs code H; induction H; [auto|].
  intro Hw. eapply twm_step; eauto.
Qed.

#[using="Type"] Lemma msteps_twm_tail : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pms',$1?.Pmodel,$48.Prest,(:.(0.&8.))Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(74.Vsegs,R6.R5.)P,(76.R6.R5.R4.R3.R2.)(76.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model rest bufs code H; induction H; [auto|].
  intro Hw. eapply twmt_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma twm_write_ret : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pmodel,$48.Pbuf,(:.(0.&8.))Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(5.$1.(6.&40.(1;.R8.(71.&5.+11.$72.)))+40.)P,(5.(0.&40.)(77.R9.(71.&5.+:.$72.))(25.&40.+1.))P,(5.(=.(:.(0.&8.)))(78.(6<.R:.(6=.Vfx,)R9.(?.(0.&40.)(1;.R:.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R8.R7.)(77.R:.(71.&5.+;.$72.))(77.R:.(71.&5.+<.$72.)))(?.(:.(0.&8.))R5.))P,(79.#1.(2:.(0.&8.)R6.))P,Pn,$2>.P,(79.#1.R1.)P,(79.R2.(2:.(0.&8.)R9.))(76.(21.Vfx,(70.R?.(71.&5.+:.$72.)(7:.(0.&8.)(7;.(0.&8.)R3.R:.)))(1:.R>.+4.)R=.R<.)R;.(7<.(0.&8.)R3.R:.)R9.R8.)(75.(6<.R=.(6=.Vfx,)R<.(?.(0.&40.)(1;.R=.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R;.R:.)R9.(24.(:.(0.&8.))R8.R7.)R6.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twm_write; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_tail_write_rec : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pmodel,$48.Prest,(:.(0.&8.))Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(5.$1.(6.&40.(1;.R8.(71.&5.+11.$72.)))+40.)P,(5.(0.&40.)(77.R9.(71.&5.+:.$72.))(25.&40.+1.))P,(5.(=.(:.(0.&8.)))(78.(6<.R:.(6=.Vfx,)R9.(?.(0.&40.)(1;.R:.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R8.R7.)(77.R:.(71.&5.+;.$72.))(77.R:.(71.&5.+<.$72.)))(?.(:.(0.&8.))R5.))P,(79.#1.(2:.(0.&8.)R6.))P,Pn,$2>.P,(79.#1.R1.)P,(79.R2.(2:.(0.&8.)R9.))(76.(21.Vfx,(70.R?.(71.&5.+:.$72.)(7:.(0.&8.)(7;.(0.&8.)R3.R:.)))(1:.R>.+4.)R=.R<.)R;.(7<.(0.&8.)R3.R:.)R9.R8.)(76.(6<.R=.(6=.Vfx,)R<.(?.(0.&40.)(1;.R=.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R;.R:.)R9.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twmt_more; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_munmap_rec : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)Pa,(0.&40.)Pnlen,(0.&40.)P,(5.$1.(6.&40.(1;.R9.(71.&5.+11.$72.)))+=7.)P,(5.(0.&40.)(77.R:.(71.&5.+:.$72.))R3.)P,(5.(0.&40.)(77.R;.(71.&5.+;.$72.))R3.)P,(5.$1.(41.(6.&40.R5.)$42.)=)P,(4:.(5.(0.&40.)R5.(25.&40.=)))P,(3.(2<.(6.&40.R7.)(51.(6.&40.R6.)))$52.)P,(5.$10.(53.(36.(34.R;.))R8.(54.R7.))$1=.)P,(75.(21.Vfx,(70.R10.(71.&5.+:.$72.)(25.&40.=))(1:.R?.+4.)(73.R9.(54.R8.)R>.)R=.)(5>.R9.(54.R8.)R<.)R;.R:.)(75.(6<.R11.(6=.Vfx,)R10.(?.(0.&40.)(1;.R11.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R?.R>.)R=.R<.R;.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  eapply twm_munmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn. auto.
  - unfold munmap_eff, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn.
    rewrite adv_munmap. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_exit_coden : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pmodel,$48.Pc,(0.&40.)P,(5.$1.(6.&40.(1;.R6.(71.&5.+11.$72.)))+5=.)P,(5.(0.&40.)(77.R7.(71.&5.+:.$72.))R2.)P,(4.(6.&40.R3.)+100.)(75.(6<.R9.(6=.Vfx,)R8.(?.(0.&40.)(1;.R9.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R7.R6.)R5.(26.(:.(0.&8.)))R4.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model c H17 H10 Hc.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply twm_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_munmap_inv : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Px8,(0.&40.)Pevs,(:.$5?.)Pst,$7=.P,(5.(=.(0.&40.))(7>.R4.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R5.)(26.(13.(0.&40.)(0.&40.))))P,(5.(=.(0.&40.))(80.R7.)(?.(0.&40.)R5.))P,(5.$1.(6.&40.R6.)+=7.)P,(5;.R9.R8.)P,(81.Vsegs,(82.R:.R9.)R7.R6.)(2.(5.(:.$5?.)R8.(26.$5?.))(5.$7=.R7.(83.(82.(6:.(6;.R;.(5=.R;.)))(5>.(4;.R;.#0.)(54.(4;.R;.#1.))R:.)))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
      subst eff model' evs0
    end.
    match goal with
    | Hmat : materialize_model_accesses
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
      rewrite (materialize_model_accesses_no_lazy _ _
        (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
      inversion Hmat; subst
    end.
    split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Heff & Hm & Hevs); subst eff model' evs0;
      rewrite (materialize_model_accesses_no_lazy _ _
        (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hm & _);
      subst model';
      assert (Hhn : m_halted
                      (munmap_model (ms_gpr ms 0)
                         (page_round_up (ms_gpr ms 1)) model) = None)
        by (rewrite munmap_model_halted; exact Hh);
      rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.

Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
    (fs : Fs.Fs) : post := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Ltr,(:.$5?.)Lo,$84.(2.(5.(:.$5?.)R2.(27.$5?.(85.(0.&8.)$5?.(86.(25.&40.+1.))O4.)(27.$5?.(87.O3.)(24.$5?.(88.O2.O1.)(26.$5?.)))))(89.O2.R2.R1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma twm_exec_mut : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "(2.Pms,$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(75.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)(8<.Vsegs,(82.R9.R8.)(8=.R7.R6.(8>.R8.)))(2.Pms,$1?.Pmodel,$48.Prest,(:.(0.&8.))Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(8?.R5.R4.R3.R2.R1.)P,(90.R4.)P,(8:.R4.)P,(5.(=.(0.&40.))(7>.R7.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R8.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R9.)(8<.Vsegs,(82.R;.R:.)(91.R9.R8.R7.(8>.R:.)))Pms,$1?.Pmodel,$48.Prest,(:.(0.&8.))Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(76.R5.R4.R3.R2.R1.)P,(90.R4.)P,(8:.R4.)P,(5.(=.(0.&40.))(7>.R7.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R8.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R9.)(8<.Vsegs,(82.R;.R:.)(91.R9.R8.R7.(8>.R:.)))))")
(* [comment removed for export] *).
Proof.
  apply (twm_mutind
    (fun ms model bufs code =>
       bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
  - (* [comment removed for export] *)
    intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
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
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
  - (* [comment removed for export] *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hbm Hh Hlazy Hfd.
    assert (Hh' : m_halted
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
      by (rewrite munmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
      by (apply munmap_model_fd1chan; exact Hfd).
    apply (exec_step_only segs _ _ []
             (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
    + apply (sstep_syscall segs ms model x8 (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_ok; [exact Hno | exact Hargs].
      * exact Hh'.
      * apply materialize_model_accesses_no_lazy.
        exact (munmap_model_no_lazy _ _ _ Hlazy).
    + intros evs st Hss.
      exact (sstep_munmap_inv ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss).
    + eapply exec_conseq;
        [exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
      intros tr o (Heq & Hx). split; [| exact Hx].
      cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
  - (* [comment removed for export] *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
  - (* [comment removed for export] *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
      intros tr o (Heq & Hx). split; [| exact Hx].
      rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
      rewrite map_app, <- !app_assoc. reflexivity.
  - (* [comment removed for export] *)
    intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
    eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
  - (* [comment removed for export] *)
    intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
    exact (IH Hbr Hbm Hh Hlazy Hfd).
  - (* [comment removed for export] *)
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma twm_exec : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(75.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)(8<.Vsegs,(82.R9.R8.)(8=.R7.R6.(8>.R8.)))")
(* [comment removed for export] *).
Proof. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.

#[using="Type"] Lemma twm_star_admits : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(75.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)(69.$92.Lc,$92.(93.Vsegs,(82.R:.R9.)(27.$5?.(87.R8.)(24.$5?.(88.R7.(8>.R9.))(26.$5?.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

#[using="Type"] Lemma twm_star_only : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(75.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)Ptr,(:.$5?.)Pc,$92.P,(93.Vsegs,(82.R;.R:.)R2.R1.)(94.$5?.R3.(27.$5?.(87.R:.)(24.$5?.(88.R9.(8>.R;.))(26.$5?.))))")
(* [comment removed for export] *).
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & Heq & _).
  rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tmw : machine_state -> Model -> list (list byte) -> word
                -> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (forall e, In e mmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
           (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    tmw ms' model bf cf bs cs ->
    tmw ms model bf cf bs cs.

#[using="Type"] Lemma msteps_tmw : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pms',$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(74.Vsegs,R7.R6.)P,(95.R7.R6.R5.R4.R3.R2.)(95.R9.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model bf cf bs cs H; induction H; [auto|].
  intro Hw. eapply tmw_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmw_mmap_rec : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pregs,(<.&5.(0.&40.))Ppc,(0.&40.)Pmem,P,(0.&40.)(=.(0.&8.))Prom,P,(0.&40.)(=.(0.&8.))Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(5.$1.(6.&40.(1;.R9.(71.&5.+11.$72.)))+=>.)P,(4:.(5.(0.&40.)(77.R:.(71.&5.+;.$72.))(25.&40.=)))P,(5.(0.&40.)(77.R;.(71.&5.+<.$72.))(25.&40.+3.))P,(5.(0.&40.)(77.R<.(71.&5.+=.$72.))(25.&40.+22.))P,(5.(0.&40.)(77.R=.(71.&5.+>.$72.))(25.&40.-1.))P,(5.(0.&40.)(77.R>.(71.&5.+?.$72.))(25.&40.=))P,Pe,$1.P,(62.$1.R1.$63.)(75.(21.Vfx,(70.R11.(71.&5.+:.$72.)(65.R2.))(1:.R10.+4.)R?.R>.)R=.R<.R;.)P,Pa,(0.&40.)P,(5.$10.(49.(77.R11.(71.&5.+:.$72.))R=.R1.(51.(6.&40.(77.R11.(71.&5.+;.$72.)))))$1=.)(75.(21.Vfx,(70.R12.(71.&5.+:.$72.)R2.)(1:.R11.+4.)(2=.R2.(54.(77.R12.(71.&5.+;.$72.)))R10.)R?.)(68.R2.(54.(77.R12.(71.&5.+;.$72.)))R>.)R;.R:.)P,(69.(0.&40.)La,(0.&40.)(5.$10.(49.(77.R12.(71.&5.+:.$72.))R>.R1.(51.(6.&40.(77.R12.(71.&5.+;.$72.)))))$1=.))(95.(6<.R12.(6=.Vfx,)R11.(?.(0.&40.)(1;.R12.(71.&5.+11.$72.)))(6>.(0.&40.))(6?.Vfx,)R10.R?.)R>.R=.R<.R;.R:.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
    Hfail Hsucc Hex.
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
  assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
  assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
  eapply tmw_mmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E11, E12, E13, E14, E15.
    auto.
  - intros e HIn. rewrite adv_set. apply Hfail; assumption.
  - intros a Hg. rewrite adv_mmap_grant.
    unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
    apply Hsucc. exact Hg.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_mmap_inv : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Px8,(0.&40.)Pevs,(:.$5?.)Pst,$7=.P,(5.(=.(0.&40.))(7>.R4.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R5.)(26.(13.(0.&40.)(0.&40.))))P,(5.(=.(0.&40.))(80.R7.)(?.(0.&40.)R5.))P,(5.$1.(6.&40.R6.)+=>.)P,(4<.R9.)P,(81.Vsegs,(82.R:.R9.)R7.R6.)(2.(5.(:.$5?.)R8.(26.$5?.))(2;.(69.$1.Le,$1.(2.(62.$1.R1.$63.)(5.$7=.R8.(83.(82.(6:.(96.R<.(65.R1.)))R;.)))))(69.(0.&40.)La,(0.&40.)(2.(5.$10.(49.(4;.R<.#0.)R;.R1.(51.(6.&40.(4;.R<.#1.))))$1=.)(5.$7=.R8.(83.(82.(6:.(6;.R<.(64.R1.(26.(13.(0.&40.)(:.(0.&8.))))(24.(13.(0.&40.)(0.&40.))(16.(0.&40.)(0.&40.)R1.(54.(4;.R<.#1.)))(26.(13.(0.&40.)(0.&40.))))(26.(13.(0.&40.)(0.&40.)))(26.$66.)(26.(13.(0.&40.)$2>.)))))(68.R1.(54.(4;.R<.#1.))R;.))))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_halted, Hh in H6; discriminate ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | assert (Hhn : m_halted
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
          by (rewrite mmap_model_halted; exact Hh);
        rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tmw_post (bf : list (list byte)) (cf : word) (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) : post := ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Ltr,(:.$5?.)Lo,$84.(2;.(2.(5.(:.$5?.)R2.(27.$5?.(87.O5.)(24.$5?.(88.O4.O1.)(26.$5?.))))(89.O4.R2.R1.))(2.(5.(:.$5?.)R2.(27.$5?.(87.O3.)(24.$5?.(88.O2.O1.)(26.$5?.))))(89.O2.R2.R1.)))")
(* [comment removed for export] *).

#[using="Type"] Lemma tmw_exec : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R5.)P,(8:.R4.)P,(5.(=.(0.&40.))(7>.R8.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R9.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R:.)(8<.Vsegs,(82.R<.R;.)(97.R:.R9.R8.R7.(8>.R;.)))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH];
    intros Hbf Hbs Hh Hlazy Hfd.
  - (* [comment removed for export] *)
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos].
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_mmap_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hss)
        as (_ & [(e & _ & Habs) | (a & _ & Habs)]); discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_mmap_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hss)
        as (-> & [(e & He & Hc') | (a & Hg & Hc')]); injection Hc' as ->.
      * (* [comment removed for export] *)
        eapply exec_conseq; [exact (twm_exec _ _ _ _ (Hfail e He) Hbf Hh Hlazy Hfd) |].
        intros tr o (Heq & Hx). left. split; [cbn [app]; exact Heq | exact Hx].
      * (* [comment removed for export] *)
        set (n := page_round_up (ms_gpr ms 1)) in *.
        assert (Hh' : m_halted (mmap_model a n model) = None)
          by (rewrite mmap_model_halted; exact Hh).
        assert (Hfd' : fd1chan (mmap_model a n model))
          by (apply mmap_model_fd1chan; exact Hfd).
        eapply exec_conseq;
          [exact (twm_exec _ _ _ _ (Hsucc a Hg) Hbs Hh'
                    (eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') |].
        intros tr o (Heq & Hx). right. split; [| exact Hx].
        cbn [app]. rewrite Heq, mmap_model_fs. reflexivity.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbf Hbs Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma tmw_star_admits_fail : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R5.)P,(5.(=.(0.&40.))(7>.R7.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R8.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R9.)(69.$92.Lc,$92.(93.Vsegs,(82.R<.R;.)(27.$5?.(87.R:.)(24.$5?.(88.R9.(8>.R;.))(26.$5?.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
  - destruct (twm_star_admits _ _ _ _ (Hfail ENOMEM ENOMEM_in_mmap_errnos)
                Hbm Hh Hlazy Hfd) as [c Hstar].
    rewrite <- apply_effect_no_write in Hstar.
    exists c.
    replace (wevents bf ++ [ExitEv cf (m_fs model)])
      with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] [])
             model model []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos].
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
    exists c.
    replace (wevents bf ++ [ExitEv cf (m_fs model)])
      with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma tmw_star_admits_succ : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R7.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R8.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R9.)(69.$92.Lc,$92.(93.Vsegs,(82.R<.R;.)(27.$5?.(87.R8.)(24.$5?.(88.R7.(8>.R;.))(26.$5?.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
  - destruct Hex as [a Hg].
    set (n := page_round_up (ms_gpr ms 1)) in *.
    assert (Hh' : m_halted (mmap_model a n model) = None)
      by (rewrite mmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan (mmap_model a n model))
      by (apply mmap_model_fd1chan; exact Hfd).
    destruct (twm_star_admits _ _ _ _ (Hsucc a Hg) Hbm Hh'
                (eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') as [c Hstar].
    rewrite mmap_model_fs in Hstar.
    exists c.
    replace (wevents bs ++ [ExitEv cs (m_fs model)])
      with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
             (mmap_model a n model) (mmap_model a n model) []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_succ_ok; [exact Hno | exact Hargs | exact Hg].
    + exact Hh'.
    + apply materialize_model_accesses_no_lazy.
      exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
  - destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
    exists c.
    replace (wevents bs ++ [ExitEv cs (m_fs model)])
      with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
Definition two_traces (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) (tr : list event) : Prop :=
  is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
  is_prefix tr (wevents bs ++ [ExitEv cs fs]).

#[using="Type"] Lemma tmw_star_only : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R5.)P,(8:.R4.)P,(5.(=.(0.&40.))(7>.R8.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R9.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R:.)Ptr,(:.$5?.)Pc,$92.P,(93.Vsegs,(82.R>.R=.)R2.R1.)(98.R=.R<.R;.R:.(8>.R>.)R3.)")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & [(Heq & _) | (Heq & _)]); [left | right];
    rewrite <- Heq; apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma tmw_no_error : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)P,(95.R9.R8.R7.R6.R5.R4.)P,(8:.R8.)P,(8:.R7.)(4:.(99.Vsegs,(82.R<.R;.)))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hh Hlazy Hfd Hte Hbf Hbs. apply exec_no_error.
  eapply exec_conseq; [exact (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) |].
  intros tr o [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_exec_not_errors : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(75.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)(4:.(8<.Vsegs,(82.R9.R8.)$9:.))")
(* [comment removed for export] *).
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm)
    as (_ & Hx).
  exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

#[using="Type"] Lemma twm_exec_code_unique : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbufs,(:.(:.(0.&8.)))Pcode,(0.&40.)P,(75.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R5.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R6.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R7.)Pcode',(0.&40.)P,(8<.Vsegs,(82.R:.R9.)(89.R1.))(5.(0.&40.)R2.R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as ->. reflexivity.
Qed.

#[using="Type"] Lemma tmw_exec_not_errors : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R5.)P,(8:.R4.)P,(5.(=.(0.&40.))(7>.R8.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R9.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R:.)(4:.(8<.Vsegs,(82.R<.R;.)$9:.))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) _ _ Hm)
    as [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmw_exec_not_fail_only : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R3.)P,(5.(=.(0.&40.))(7>.R7.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R8.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R9.)P,(4:.(94.$5?.(27.$5?.(87.R7.)(24.$5?.(88.R6.(8>.R:.))(26.$5?.)))(27.$5?.(87.R9.)(24.$5?.(88.R8.(8>.R:.))(26.$5?.)))))(4:.(8<.Vsegs,(82.R<.R;.)(8=.R:.R9.(8>.R;.))))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd Hnp Hex.
  destruct (tmw_star_admits_succ ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd) as (c & Hstar).
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
  apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma tmw_exec_not_succ_only : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pms,$1?.Pmodel,$48.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(95.R6.R5.R4.R3.R2.R1.)P,(8:.R5.)P,(5.(=.(0.&40.))(7>.R7.)(6>.(0.&40.)))P,(5.(:.(13.(0.&40.)(0.&40.)))(7?.R8.)(26.(13.(0.&40.)(0.&40.))))P,(8;.R9.)P,(4:.(94.$5?.(27.$5?.(87.R9.)(24.$5?.(88.R8.(8>.R:.))(26.$5?.)))(27.$5?.(87.R7.)(24.$5?.(88.R6.(8>.R:.))(26.$5?.)))))(4:.(8<.Vsegs,(82.R<.R;.)(8=.R8.R7.(8>.R;.))))")
(* [comment removed for export] *).
Proof.
  intros ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd Hnp Hex.
  destruct (tmw_star_admits_fail ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd) as (c & Hstar).
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
  apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma two_traces_prefix_closed : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)Pfs,$9;.Ptr,(:.$5?.)Ptr',(:.$5?.)P,(9<.R7.R6.R5.R4.R3.R2.)P,(94.$5?.R2.R3.)(9<.R9.R8.R7.R6.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros bf cf bs cs fs tr tr' [H | H] Hp;
    [left | right]; eapply is_prefix_trans; eauto.
Qed.

#[using="Type"] Lemma mmap_obs_iff_te : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Ppc,$9=.Pph,$9>.Psp,(0.&40.)Pbrk0,(0.&40.)Pmb,(0.&40.)Prnd,$9?.Plim,$1.Pinp,$:0.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(:1.R=.(:2.R=.R<.R;.R:.R7.(:3.R5.)(:4.R5.)(:5.R5.)(:6.R5.))(:7.(:8.R=.)R9.R8.R:.R6.R5.)R4.R3.R2.R1.)P,(8:.R5.)P,(8:.R4.)Ptr,(:.$5?.)(57.(:9.R11.(::.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R1.)(9<.R8.R7.R6.R5.(:;.R9.)R1.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs tr.
  unfold init_config in *.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None) by reflexivity.
  assert (Hlazy : m_vm_lazy
      (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
  assert (Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp)) by reflexivity.
  assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (tmw_star_only segs ms _ bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd
                  tr' c Hstar) as H2.
    rewrite Hfs in H2.
    eapply two_traces_prefix_closed; eauto.
  - intros [Hp | Hp].
    + destruct (tmw_star_admits_fail segs ms _ bf cf bs cs Hte Hbf Hh Hlazy Hfd)
        as [c Hstar].
      rewrite Hfs in Hstar.
      exists (wevents bf ++ [ExitEv cf (in_fs inp)]), c. split; assumption.
    + destruct (tmw_star_admits_succ segs ms _ bf cf bs cs Hte Hbs Hh Hlazy Hfd)
        as [c Hstar].
      rewrite Hfs in Hstar.
      exists (wevents bs ++ [ExitEv cs (in_fs inp)]), c. split; assumption.
Qed.

#[using="Type"] Lemma mmap_no_error_run_te : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Ppc,$9=.Pph,$9>.Psp,(0.&40.)Pbrk0,(0.&40.)Pmb,(0.&40.)Prnd,$9?.Plim,$1.Pinp,$:0.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(:1.R=.(:2.R=.R<.R;.R:.R7.(:3.R5.)(:4.R5.)(:5.R5.)(:6.R5.))(:7.(:8.R=.)R9.R8.R:.R6.R5.)R4.R3.R2.R1.)P,(8:.R5.)P,(8:.R4.)(4:.(99.R10.(::.R10.R?.R>.R=.R<.R;.R:.R9.R8.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs.
  unfold init_config.
  apply (tmw_no_error segs _ (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs);
    [reflexivity | reflexivity | reflexivity | exact Hte | exact Hbf | exact Hbs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mmap_omni_run_te : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psegs,(:.$;.)Ppc,$9=.Pph,$9>.Psp,(0.&40.)Pbrk0,(0.&40.)Pmb,(0.&40.)Prnd,$9?.Plim,$1.Pinp,$:0.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)P,(:1.R=.(:2.R=.R<.R;.R:.R7.(:3.R5.)(:4.R5.)(:5.R5.)(:6.R5.))(:7.(:8.R=.)R9.R8.R:.R6.R5.)R4.R3.R2.R1.)P,(8:.R5.)P,(8:.R4.)(:<.(:=.R10.R?.R>.)R9.(:>.R=.R<.R;.R:.)R8.(:?.R7.R6.R5.R4.(:;.R8.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs.
  cbn [omni_run]. unfold init_config.
  exact (tmw_exec segs _ _ bf cf bs cs Hte Hbf Hbs eq_refl eq_refl eq_refl).
Qed.

#[using="Type"] Lemma mmap_omni_strong_equiv_te : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psource_segs,(:.$;.)Prpc,$9=.Prph,$9>.Prsp,(0.&40.)Prbrk,(0.&40.)Prmb,(0.&40.)Prrnd,$9?.Ptarget_segs,(:.$;.)Papc,$9=.Paph,$9>.Pasp,(0.&40.)Pabrk,(0.&40.)Pamb,(0.&40.)Parnd,$9?.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)Pinp,$:0.P,(:1.R13.(:2.R13.R12.R11.R10.R=.(:3.R1.)(:4.R1.)(:5.R1.)(:6.R1.))(:7.(:8.R13.)R?.R>.R10.$;0.R1.)R5.R4.R3.R2.)P,(:1.R=.(:2.R=.R<.R;.R:.R7.(:3.R2.)(:4.R2.)(:5.R2.)(:6.R2.))(:7.(:8.R=.)R9.R8.R:.$;1.R2.)R6.R5.R4.R3.)P,(8:.R7.)P,(8:.R6.)(;2.(:=.R17.R16.R15.)(:=.R10.R?.R>.)(:>.R14.R13.R12.R11.)(:>.R=.R<.R;.R:.)R5.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp
    Hsource Htarget Hbf Hbs.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
                Hsource Hbf Hbs) |].
    intros tr o [(_ & Hx) | (_ & Hx)];
      exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
               Hsource Hbf Hbs tr).
    rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs
               Htarget Hbf Hbs tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs
             Htarget Hbf Hbs).
Qed.

#[using="Type"] Lemma mmap_strong_equiv_te : ltac2:(CDefT.buildp (gd_tbl_MmapSim ()) "Psource_segs,(:.$;.)Prpc,$9=.Prph,$9>.Prsp,(0.&40.)Prbrk,(0.&40.)Prmb,(0.&40.)Prrnd,$9?.Prlim,$1.Ptarget_segs,(:.$;.)Papc,$9=.Paph,$9>.Pasp,(0.&40.)Pabrk,(0.&40.)Pamb,(0.&40.)Parnd,$9?.Palim,$1.Pbf,(:.(:.(0.&8.)))Pcf,(0.&40.)Pbs,(:.(:.(0.&8.)))Pcs,(0.&40.)Pinp,$:0.P,(:1.R15.(:2.R15.R14.R13.R12.R?.(:3.R1.)(:4.R1.)(:5.R1.)(:6.R1.))(:7.(:8.R15.)R11.R10.R12.R>.R1.)R5.R4.R3.R2.)P,(:1.R>.(:2.R>.R=.R<.R;.R8.(:3.R2.)(:4.R2.)(:5.R2.)(:6.R2.))(:7.(:8.R>.)R:.R9.R;.R7.R2.)R6.R5.R4.R3.)P,(8:.R7.)P,(8:.R6.)(2.(;3.(;4.(:=.R19.R18.R17.)R12.(:>.R16.R15.R14.R13.)R5.))(;5.(;4.(:=.R19.R18.R17.)R12.(:>.R16.R15.R14.R13.)R5.)(;4.(:=.R11.R10.R?.)R:.(:>.R>.R=.R<.R;.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp
    Hsource Htarget Hbf Hbs.
  split.
  { apply no_error_run_modeled.
    apply (mmap_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
             Hsource Hbf Hbs). }
  right. split.
  - intro tr. cbn.
    rewrite (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
               Hsource Hbf Hbs tr).
    rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
               Htarget Hbf Hbs tr).
    reflexivity.
  - cbn. apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
                  Htarget Hbf Hbs).
Qed.
End WithFP1.
