(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  SimInv ExitSim PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg SpinAlgB.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_NoReserve () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.ABoot.LazyFrame.accesses_outside_lazy"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.with_copyins"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_eff"; "Corelib.Init.Peano.le"; "OSSVerify.KrLib.ABoot.LazyFrame.access_outside_range"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "stdpp.bitvector.definitions.Z_to_bv"; "WithFP1.mmap_args_ok_noreserve"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Numbers.BinNums.Z"; "WithFP1.grant_ok_nr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.errno_ret_in"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "OSSVerify.KrLib.ABoot.MmapSim.page_round_up"; "WithFP1.mmap_model_noreserve"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt2"; "OSSVerify.KrLib.ABoot.DivergeSim.to_spin"; "OSSVerify.KrLib.ABoot.MmapSim.mmap_args_ok"; "OSSVerify.KrLib.ABoot.MmapSim.grant_ok"; "OSSVerify.KrLib.ABoot.MmapSim.mmap_model"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_args_ok"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_model"; "OSSVerify.KrLib.ABoot.ShapeAlg.node_ok"; "Corelib.Init.Datatypes.unit"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.ABoot.CatSim.fd1chan"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "Corelib.Lists.ListDef.firstn"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "OSSVerify.KrLib.ABoot.CatSim.buf_modeled"; "OSSVerify.KrLib.ABoot.ShapeAlg.wr_index"; "Corelib.Init.Specif.proj1_sig"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_write_ch"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "WithFP1.WithSegs.msteps_acc"; "OSSVerify.KrLib.ABoot.ShapeAlg.realizes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.Riscv.Instr.branch_cond"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "LinuxProcessSemantics.Riscv.Instr.Branch"; "LinuxProcessSemantics.Riscv.Sem.branch_taken"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "OSSVerify.KrLib.ABoot.PropExec.btgt"; "stdpp.bitvector.definitions.bv_signed"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.Riscv.Instr.Jal"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "grant_ok_nr"; "msteps_acc"; "stdpp.bitvector.definitions.bv_and"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "OSSVerify.KrLib.ABoot.CatSim.wpick"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "LinuxProcessSemantics.LinuxProcessSem.State.ExitEv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].

Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma materialize_syscall_effect_nil : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pm,$0.Pr,(1.&40.)Pzs,(2.(3.(1.&40.)(1.&40.)))Pus,(2.(3.(1.&40.)(1.&40.)))(4.(5.$0.)(6.R4.(7.(8.R3.(9.(3.(1.&40.)(2.(1.&8.))))R2.R1.(9.$:.)(9.(3.(1.&40.)$;.)))))(<.$0.R4.))")
(* [comment removed for export] *).
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma materialize_syscall_effect_copyin_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pm,$0.Pr,(1.&40.)Pa,(1.&40.)Pn,$;.P,(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.R2.R1.)(9.(3.(1.&40.)$;.)))(10.R4.))(4.(5.$0.)(6.R5.(7.(11.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.R3.R2.)(9.(3.(1.&40.)$;.)))(8.R4.(9.(3.(1.&40.)(2.(1.&8.))))(9.(3.(1.&40.)(1.&40.)))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.))))))(<.$0.R5.))")
(* [comment removed for export] *).
Proof.
  intros m r a n Hout.
  exact (materialize_model_accesses_disjoint m [(a, n)] Hout).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma materialize_munmap_eff_nil : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pm,$0.Pms,$12.(4.(5.$0.)(6.R2.(7.(13.R1.)))(<.$0.R2.))")
(* [comment removed for export] *).
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma access_outside_range_mono : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa,(1.&40.)Pn,$;.Pn',$;.Plo,(1.&40.)Psz,(1.&40.)P,(14.R3.R4.)P,(15.R6.R5.R3.R2.)(15.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros a n n' lo sz Hle [Hnw Hd].
  split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma accesses_outside_lazy_incl : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Paccs,(2.(3.(1.&40.)$;.))Paccs',(2.(3.(1.&40.)$;.))Plazy,(2.(3.(1.&40.)(1.&40.)))P,Px,(3.(1.&40.)$;.)P,(16.(3.(1.&40.)$;.)R1.R3.)(16.(3.(1.&40.)$;.)R2.R5.)P,(=.R4.R2.)(=.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros accs accs' lazy Hincl Hout a n lo sz Hin Hlz.
  exact (Hout a n lo sz (Hincl _ Hin) Hlz).
Qed.

#[using="Type"] Lemma accesses_outside_lazy_app_l : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Paccs1,(2.(3.(1.&40.)$;.))Paccs2,(2.(3.(1.&40.)$;.))Plazy,(2.(3.(1.&40.)(1.&40.)))P,(=.(17.(3.(1.&40.)$;.)R3.R2.)R1.)(=.R4.R2.)")
(* [comment removed for export] *).
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. left. exact Hx.
Qed.

#[using="Type"] Lemma accesses_outside_lazy_app_r : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Paccs1,(2.(3.(1.&40.)$;.))Paccs2,(2.(3.(1.&40.)$;.))Plazy,(2.(3.(1.&40.)(1.&40.)))P,(=.(17.(3.(1.&40.)$;.)R3.R2.)R1.)(=.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. right. exact Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma accesses_outside_lazy_shrink : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa,(1.&40.)Plen,$;.Pn,$;.Plazy,(2.(3.(1.&40.)(1.&40.)))P,(14.R2.R3.)P,(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.R5.R4.)(9.(3.(1.&40.)$;.)))R2.)(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.R6.R4.)(9.(3.(1.&40.)$;.)))R3.)")
(* [comment removed for export] *).
Proof.
  intros a len n lazy Hle Hout a' n' lo sz Hin Hlz.
  destruct Hin as [Hin | []]. injection Hin as Ha Hn. subst a' n'.
  apply (access_outside_range_mono a len n lo sz Hle).
  apply (Hout a len lo sz); [left; reflexivity | exact Hlz].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

#[using="Type"] Lemma mmap_model_noreserve_halted : forall a n m,
  m_halted (mmap_model_noreserve a n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_noreserve_fs : forall a n m,
  m_fs (mmap_model_noreserve a n m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_noreserve_fd1chan : forall a n m,
  fd1chan m -> fd1chan (mmap_model_noreserve a n m).
Proof. intros a n m H. exact H. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma mmap_model_noreserve_lazy : forall a n m,
  m_vm_lazy (mmap_model_noreserve a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_args_ok_noreserve (ms : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "(18.(19.(4.(1.&40.)(1:.O1.#1.)(1;.&40.=)))(18.(4.(1.&40.)(1:.O1.#2.)(1;.&40.+3.))(18.(4.(1.&40.)(1:.O1.#3.)(1;.&40.+4022.))(18.(4.(1.&40.)(1:.O1.#4.)(1;.&40.-1.))(4.(1.&40.)(1:.O1.#5.)(1;.&40.=))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_args_ok_noreserve_gates : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.P,(1<.R1.)(18.(4.$1=.(1>.(1:.R2.#5.))$1?.)(18.(4.$1=.(20.(1:.R2.#3.))$1?.)(18.(4.$1=.(21.(1:.R2.#1.))$22.)(4.$1=.(23.(1:.R2.#2.)(1:.R2.#3.)(1:.R2.#5.))$1?.))))")
(* [comment removed for export] *).
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_noreserve_b_flags : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "(24.(24.(24.(25.(26.(27.&40.O2.)$28.)=)(29.=(27.&40.O2.)))(2:.(2;.(27.&40.O2.)O1.)(2<.(2=.O3.))))(2>.(17.(3.(1.&40.)(1.&40.))(2?.(2=.O3.))(30.(2=.O3.)))O2.(1;.&40.O1.)))")
(* [comment removed for export] *).

#[using="Type"] Lemma grant_ok_nr_unpack : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Phint,(1.&40.)Pm,$0.Pa,(1.&40.)Pn,$31.P,(4.$1=.(32.R4.R3.R2.R1.)$1?.)(18.(4.$31.(26.(27.&40.R3.)$28.)=)(18.(33.=(27.&40.R3.))(18.(34.(2;.(27.&40.R3.)R2.)(2<.(2=.R4.)))(4.$1=.(2>.(17.(3.(1.&40.)(1.&40.))(2?.(2=.R4.))(30.(2=.R4.)))R3.(1;.&40.R2.))$1?.))))")
(* [comment removed for export] *).
Proof.
  intros hint m a n H. unfold grant_ok_nr in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  auto 6.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_nr_not_errno : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Phint,(1.&40.)Pmodel,$0.Pa,(1.&40.)Pn,$31.P,(34.=R1.)P,(4.$1=.(32.R5.R4.R3.R2.)$1?.)(4.$1=.(35.$36.R4.)$22.)")
(* [comment removed for export] *).
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_nr_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fail_ok_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pms,$12.Px8,(1.&40.)Pmodel,$0.Pe,$31.P,(4.$31.(27.&40.R3.)+=>.)P,(1<.R5.)P,(16.$31.R3.$36.)(38.(39.R8.R7.R6.)R5.(3:.$3;.(8.(3<.R4.)(9.(3.(1.&40.)(2.(1.&8.))))(9.(3.(1.&40.)(1.&40.)))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))R5.(9.$3=.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_succ_ok_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pms,$12.Px8,(1.&40.)Pmodel,$0.Pa,(1.&40.)P,(4.$31.(27.&40.R3.)+=>.)P,(1<.R5.)P,(4.$1=.(32.(1:.R6.#0.)R4.R3.(3>.(27.&40.(1:.R6.#1.))))$1?.)(38.(39.R8.R7.R6.)R5.(3:.$3;.(8.R4.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R4.(3?.(1:.R7.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))(40.R4.(3?.(1:.R7.#1.))R5.)(9.$3=.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model a Hno Ha Hg.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite (grant_nr_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok_nr in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[H1 H2] H3] H4].
  rewrite Hflags.
  unfold mmap_noreserve_backed_ok, with_mmap_backing.
  rewrite mmap_noreserve_b_flags.
  rewrite H1, H2, H3, H4. cbn [andb].
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_ok_inv_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pms,$12.Px8,(1.&40.)Pmodel,$0.Peff,$3;.Pmodel',$0.Pevs,(2.$3=.)P,(4.$31.(27.&40.R5.)+=>.)P,(1<.R7.)P,(38.(39.R9.R8.R7.)R6.(3:.$3;.R5.R4.R3.))(18.(4.(2.$3=.)R4.(9.$3=.))(41.(42.$31.Le,$31.(18.(16.$31.R1.$36.)(18.(4.$3;.R7.(8.(3<.R1.)(9.(3.(1.&40.)(2.(1.&8.))))(9.(3.(1.&40.)(1.&40.)))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.))))(4.$0.R6.R8.))))(42.(1.&40.)La,(1.&40.)(18.(4.$1=.(32.(1:.R:.#0.)R8.R1.(3>.(27.&40.(1:.R:.#1.))))$1?.)(18.(4.$3;.R7.(8.R1.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R1.(3?.(1:.R:.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.))))(4.$0.R6.(40.R1.(3?.(1:.R:.#1.))R8.)))))))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hflags in Hspec.
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite mmap_noreserve_b_flags in Hspec.
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
  - rewrite andb_true_r in Hspec.
    destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
              && (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
              && region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))) eqn:Hcond;
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
    + unfold grant_ok_nr. exact Hcond.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

#[using="Type"] Lemma mmap_no_unmodeled_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pms,$12.Px8,(1.&40.)Pmodel,$0.P,(4.$31.(27.&40.R2.)+=>.)P,(1<.R4.)(19.(38.(39.R6.R5.R4.)R3.(43.$3;.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_mmap_inv_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pevs,(2.$3=.)Pst,$44.P,(4.(5.(1.&40.))(45.R4.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R6.)(<.(1.&40.)R4.))P,(4.$31.(27.&40.R5.)+=>.)P,(1<.R8.)P,(48.Vsegs,(49.R9.R8.)R6.R5.)(18.(4.(2.$3=.)R7.(9.$3=.))(41.(42.$31.Le,$31.(18.(16.$31.R1.$36.)(4.$44.R7.(4:.(49.(4;.(4<.R;.(3<.R1.)))R:.)))))(42.(1.&40.)La,(1.&40.)(18.(4.$1=.(32.(1:.R;.#0.)R:.R1.(3>.(27.&40.(1:.R;.#1.))))$1?.)(4.$44.R7.(4:.(49.(4;.(4=.R;.(8.R1.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R1.(3?.(1:.R;.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))))(40.R1.(3?.(1:.R;.#1.))R:.))))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model_noreserve a _ model) _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst eff model';
      rewrite materialize_syscall_effect_nil in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_noreserve_halted, Hh in H6; discriminate ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite mmap_model_noreserve_halted; exact Hh ] ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled_noreserve segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_mmap_noreserve : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  node_ok segs (mkCfg ms model)
    ({e : Z | In e mmap_errnos}
     + {a : word | grant_ok_nr (ms_gpr ms 0) model a
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr (exist _ a _) =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [[e He] | [a Ha]]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok_noreserve; assumption.
      * exact Hh.
      * apply materialize_syscall_effect_nil.
    + apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
               (mmap_model_noreserve a n model) (mmap_model_noreserve a n model) []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_succ_ok_noreserve; assumption.
      * rewrite mmap_model_noreserve_halted; exact Hh.
      * apply materialize_syscall_effect_nil.
  - intros e st Hss.
    destruct (sstep_mmap_inv_noreserve ms model x8 e st Hh Hsvc Hno Hargs Hss)
      as [-> [(er & Her & ->) | (a & Ha & ->)]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr (exist _ a Ha)). split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)PA,$4>.PB,$4>.P,(4.(5.(1.&40.))(45.R4.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R6.)(<.(1.&40.)R4.))P,(4.$31.(27.&40.R5.)+=>.)P,(1<.R8.)P,Pe,$31.P,(16.$31.R1.$36.)(4?.Vsegs,(49.(4;.(4<.R;.(3<.R2.)))R:.)R8.)P,Pa,(1.&40.)P,(4.$1=.(32.(1:.R;.#0.)R:.R1.(3>.(27.&40.(1:.R;.#1.))))$1?.)(4?.Vsegs,(49.(4;.(4=.R<.(8.R2.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R2.(3?.(1:.R<.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))))(40.R2.(3?.(1:.R<.#1.))R;.))R8.)P,(42.(1.&40.)La,(1.&40.)(4.$1=.(32.(1:.R<.#0.)R;.R1.(3>.(27.&40.(1:.R<.#1.))))$1?.))(4?.Vsegs,(49.R<.R;.)(50.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 A B Hh Hsvc Hno Hargs HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz_alt2 segs (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok_nr (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - apply (node_mmap_noreserve ms model x8); assumption.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_spin_noreserve : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)PB,$4>.P,(4.(5.(1.&40.))(45.R3.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R5.)(<.(1.&40.)R3.))P,(4.$31.(27.&40.R4.)+=>.)P,(1<.R7.)P,Pe,$31.P,(16.$31.R1.$36.)(51.Vsegs,(4;.(4<.R:.(3<.R2.)))R9.)P,Pa,(1.&40.)P,(4.$1=.(32.(1:.R:.#0.)R9.R1.(3>.(27.&40.(1:.R:.#1.))))$1?.)(4?.Vsegs,(49.(4;.(4=.R;.(8.R2.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R2.(3?.(1:.R;.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))))(40.R2.(3?.(1:.R;.#1.))R:.))R8.)P,(42.(1.&40.)La,(1.&40.)(4.$1=.(32.(1:.R;.#0.)R:.R1.(3>.(27.&40.(1:.R;.#1.))))$1?.))(4?.Vsegs,(49.R;.R:.)R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 B Hh Hsvc Hno Hargs Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  eapply srz_conseq.
{ (* [comment removed for export] *)
    apply (srz_node_sp_sys segs ms model x8
             ({e : Z | In e mmap_errnos}
              + {a : word | grant_ok_nr (ms_gpr ms 0) model a
                              (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
             (fun i => match i with
                | inl (exist _ e _) =>
                    mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
                | inr (exist _ a _) =>
                    mkCfg (advance_past_svc
                             (apply_effect ms
                                (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                          (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)
                end)
             (fun i => match i with inl _ => t_nil | inr _ => B end)
             (fun i => match i with inl _ => false | inr _ => true end)
             (inr (exist _ a0 Ha0)) Hsvc).
    - apply family_off_alloc. cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
    - apply (node_mmap_noreserve ms model x8); assumption.
    - reflexivity.
    - cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect. cbn [eff_ret].
      rewrite (refusal_b_mmap (sys_input segs ms x8) model) by (cbn [in_sysno sys_input]; exact Hno).
      apply (grant_nr_not_errno (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
        [apply page_round_up_Z_nonneg; pose proof (bv_unsigned_in_range 64 (ms_gpr ms 1)); lia | exact Ha0].
    - intros [[e He] | [a Ha]] HL; [discriminate HL|]. cbn. apply HB; exact Ha.
    - intros [[e He] | [a Ha]] HL; [|discriminate HL]. cbn. split.
      + apply srz0_spin; cbn; [apply Hspin; exact He | exact Hh].
      + rewrite ms_gpr0_advance_set_gpr0.
        rewrite (refusal_b_mmap (sys_input segs ms x8) model) by (cbn [in_sysno sys_input]; exact Hno).
        apply errno_ret_in_intro. exact He. }
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_mmap_inv_lazy : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pevs,(2.$3=.)Pst,$44.P,(4.(5.(1.&40.))(45.R4.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R6.)(<.(1.&40.)R4.))P,(4.$31.(27.&40.R5.)+=>.)P,(52.R8.)P,(48.Vsegs,(49.R9.R8.)R6.R5.)(18.(4.(2.$3=.)R7.(9.$3=.))(41.(42.$31.Le,$31.(18.(16.$31.R1.$36.)(4.$44.R7.(4:.(49.(4;.(4<.R;.(3<.R1.)))R:.)))))(42.(1.&40.)La,(1.&40.)(18.(4.$1=.(53.(1:.R;.#0.)R:.R1.(3>.(27.&40.(1:.R;.#1.))))$1?.)(4.$44.R7.(4:.(49.(4;.(4=.R;.(8.R1.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R1.(3?.(1:.R;.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))))(54.R1.(3?.(1:.R;.#1.))R:.))))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
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
        rewrite materialize_syscall_effect_nil in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite materialize_syscall_effect_nil in Hmat;
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
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst eff model';
      rewrite materialize_syscall_effect_nil in Hmat;
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
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite mmap_model_halted; exact Hh ] ]
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
#[using="Type"] Lemma node_mmap_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  node_ok segs (mkCfg ms model)
    ({e : Z | In e mmap_errnos}
     + {a : word | grant_ok (ms_gpr ms 0) model a
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr (exist _ a _) =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [[e He] | [a Ha]]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok; assumption.
      * exact Hh.
      * apply materialize_syscall_effect_nil.
    + apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
               (mmap_model a n model) (mmap_model a n model) []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_succ_ok; assumption.
      * rewrite mmap_model_halted; exact Hh.
      * apply materialize_syscall_effect_nil.
  - intros e st Hss.
    destruct (sstep_mmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
      as [-> [(er & Her & ->) | (a & Ha & ->)]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr (exist _ a Ha)). split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_lazy : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)PA,$4>.PB,$4>.P,(4.(5.(1.&40.))(45.R4.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R6.)(<.(1.&40.)R4.))P,(4.$31.(27.&40.R5.)+=>.)P,(52.R8.)P,Pe,$31.P,(16.$31.R1.$36.)(4?.Vsegs,(49.(4;.(4<.R;.(3<.R2.)))R:.)R8.)P,Pa,(1.&40.)P,(4.$1=.(53.(1:.R;.#0.)R:.R1.(3>.(27.&40.(1:.R;.#1.))))$1?.)(4?.Vsegs,(49.(4;.(4=.R<.(8.R2.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R2.(3?.(1:.R<.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))))(54.R2.(3?.(1:.R<.#1.))R;.))R8.)P,(42.(1.&40.)La,(1.&40.)(4.$1=.(53.(1:.R<.#0.)R;.R1.(3>.(27.&40.(1:.R<.#1.))))$1?.))(4?.Vsegs,(49.R<.R;.)(50.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 A B Hh Hsvc Hno Hargs HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz_alt2 segs (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - apply (node_mmap_lazy ms model x8); assumption.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_spin_lazy : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)PB,$4>.P,(4.(5.(1.&40.))(45.R3.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R5.)(<.(1.&40.)R3.))P,(4.$31.(27.&40.R4.)+=>.)P,(52.R7.)P,Pe,$31.P,(16.$31.R1.$36.)(51.Vsegs,(4;.(4<.R:.(3<.R2.)))R9.)P,Pa,(1.&40.)P,(4.$1=.(53.(1:.R:.#0.)R9.R1.(3>.(27.&40.(1:.R:.#1.))))$1?.)(4?.Vsegs,(49.(4;.(4=.R;.(8.R2.(9.(3.(1.&40.)(2.(1.&8.))))(>.(3.(1.&40.)(1.&40.))(?.(1.&40.)(1.&40.)R2.(3?.(1:.R;.#1.)))(9.(3.(1.&40.)(1.&40.))))(9.(3.(1.&40.)(1.&40.)))(9.$:.)(9.(3.(1.&40.)$;.)))))(54.R2.(3?.(1:.R;.#1.))R:.))R8.)P,(42.(1.&40.)La,(1.&40.)(4.$1=.(53.(1:.R;.#0.)R:.R1.(3>.(27.&40.(1:.R;.#1.))))$1?.))(4?.Vsegs,(49.R;.R:.)R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 B Hh Hsvc Hno Hargs Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  eapply srz_conseq.
{ (* [comment removed for export] *)
    apply (srz_node_sp_sys segs ms model x8
             ({e : Z | In e mmap_errnos}
              + {a : word | grant_ok (ms_gpr ms 0) model a
                              (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
             (fun i => match i with
                | inl (exist _ e _) =>
                    mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
                | inr (exist _ a _) =>
                    mkCfg (advance_past_svc
                             (apply_effect ms
                                (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                          (mmap_model a (page_round_up (ms_gpr ms 1)) model)
                end)
             (fun i => match i with inl _ => t_nil | inr _ => B end)
             (fun i => match i with inl _ => false | inr _ => true end)
             (inr (exist _ a0 Ha0)) Hsvc).
    - apply family_off_alloc. cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
    - apply (node_mmap_lazy ms model x8); assumption.
    - reflexivity.
    - cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect. cbn [eff_ret].
      rewrite (refusal_b_mmap (sys_input segs ms x8) model) by (cbn [in_sysno sys_input]; exact Hno).
      apply (grant_not_errno (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
        [apply page_round_up_Z_nonneg; pose proof (bv_unsigned_in_range 64 (ms_gpr ms 1)); lia | exact Ha0].
    - intros [[e He] | [a Ha]] HL; [discriminate HL|]. cbn. apply HB; exact Ha.
    - intros [[e He] | [a Ha]] HL; [|discriminate HL]. cbn. split.
      + apply srz0_spin; cbn; [apply Hspin; exact He | exact Hh].
      + rewrite ms_gpr0_advance_set_gpr0.
        rewrite (refusal_b_mmap (sys_input segs ms x8) model) by (cbn [in_sysno sys_input]; exact Hno).
        apply errno_ret_in_intro. exact He. }
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_munmap_inv_lazy : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pevs,(2.$3=.)Pst,$44.P,(4.(5.(1.&40.))(45.R4.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R6.)(<.(1.&40.)R4.))P,(4.$31.(27.&40.R5.)+=7.)P,(55.R8.R7.)P,(48.Vsegs,(49.R9.R8.)R6.R5.)(18.(4.(2.$3=.)R7.(9.$3=.))(4.$44.R6.(4:.(49.(4;.(4=.R:.(13.R:.)))(56.(1:.R:.#0.)(3?.(1:.R:.#1.))R9.)))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
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
      rewrite materialize_munmap_eff_nil in Hmat;
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
      rewrite materialize_munmap_eff_nil in Hmat;
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
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite munmap_model_halted; exact Hh ]
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

#[using="Type"] Lemma node_munmap_lazy : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)P,(4.(5.(1.&40.))(45.R2.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R4.)(<.(1.&40.)R2.))P,(4.$31.(27.&40.R3.)+=7.)P,(55.R6.R5.)(57.Vsegs,(49.R7.R6.)$58.L,$58.(9.$3=.)L,$58.(49.(4;.(4=.R8.(13.R8.)))(56.(1:.R8.#0.)(3?.(1:.R8.#1.))R7.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_munmap_eff_nil.
  - intros e st Hss.
    destruct (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

#[using="Type"] Lemma srz_munmap_lazy : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)PT,$4>.P,(4.(5.(1.&40.))(45.R3.)(46.(1.&40.)))P,(4.(5.(1.&40.))(47.R5.)(<.(1.&40.)R3.))P,(4.$31.(27.&40.R4.)+=7.)P,(55.R7.R6.)P,(4?.Vsegs,(49.(4;.(4=.R8.(13.R8.)))(56.(1:.R8.#0.)(3?.(1:.R8.#1.))R7.))R5.)(4?.Vsegs,(49.R9.R8.)R6.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 T Hh Hsvc Hno Hargs Hc.
  eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_write_next_inv_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pbuf,(2.(1.&8.))Pevs,(2.$3=.)Pc',$59.P,(4.(5.(1.&40.))(45.R5.)(46.(1.&40.)))P,(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.(1:.R7.#1.)(5:.(1.&8.)R4.))(9.(3.(1.&40.)$;.)))(10.R6.))P,(5;.R7.)P,(4.(5.(1.&40.))(47.R9.)(<.(1.&40.)R7.))P,(4.$31.(27.&40.R8.)+40.)P,(4.(1.&40.)(1:.R;.#0.)(1;.&40.+1.))P,(4.(5.(2.(1.&8.)))(5<.R<.(1:.R<.#1.)(1:.R<.#2.))(<.(2.(1.&8.))R9.))P,(14.#1.(5:.(1.&8.)R:.))P,(48.Vsegs,(49.R>.R=.)R:.(4:.R9.))(42.$;.Ln,$;.(18.(14.#1.R1.)(18.(14.R1.(5:.(1.&8.)R=.))(18.(4.(2.$3=.)R<.(5=.(1.&8.)$3=.(5>.(1;.&40.+1.))(5?.(1.&8.)R1.R=.)))(4.$59.R;.(49.(4;.(4<.R10.(60.(1.&8.)(5?.(1.&8.)R1.R=.))))R?.))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 buf evs c' Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
                   (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
    end.
Qed.

#[using="Type"] Lemma sstep_write_inv_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pbuf,(2.(1.&8.))Pevs,(2.$3=.)Pst,$44.P,(4.(5.(1.&40.))(45.R5.)(46.(1.&40.)))P,(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.(1:.R7.#1.)(5:.(1.&8.)R4.))(9.(3.(1.&40.)$;.)))(10.R6.))P,(5;.R7.)P,(4.(5.(1.&40.))(47.R9.)(<.(1.&40.)R7.))P,(4.$31.(27.&40.R8.)+40.)P,(4.(1.&40.)(1:.R;.#0.)(1;.&40.+1.))P,(4.(5.(2.(1.&8.)))(5<.R<.(1:.R<.#1.)(1:.R<.#2.))(<.(2.(1.&8.))R9.))P,(61.R:.)P,(14.#1.(5:.(1.&8.)R;.))P,(48.Vsegs,(49.R?.R>.)R;.R:.)(42.$;.Ln,$;.(18.(14.#1.R1.)(18.(14.R1.(5:.(1.&8.)R>.))(18.(4.(2.$3=.)R=.(5=.(1.&8.)$3=.(5>.(1;.&40.+1.))(5?.(1.&8.)R1.R>.)))(4.$44.R<.(4:.(49.(4;.(4<.R11.(60.(1.&8.)(5?.(1.&8.)R1.R>.))))R10.)))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 buf evs st Hh Hout Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv_disjoint ms model x8 buf evs c'
                Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* [comment removed for export] *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hnb H3)
          as (n & _ & Hn2 & Heff & Hm & _);
        subst eff model';
        rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
                   (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

#[using="Type"] Lemma node_write1_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pbuf,(2.(1.&8.))P,(4.(5.(1.&40.))(45.R3.)(46.(1.&40.)))P,(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.(1:.R5.#1.)(5:.(1.&8.)R2.))(9.(3.(1.&40.)$;.)))(10.R4.))P,(5;.R5.)P,(4.(5.(1.&40.))(47.R7.)(<.(1.&40.)R5.))P,(4.$31.(27.&40.R6.)+40.)P,(4.(1.&40.)(1:.R9.#0.)(1;.&40.+1.))P,(4.(5.(2.(1.&8.)))(5<.R:.(1:.R:.#1.)(1:.R:.#2.))(<.(2.(1.&8.))R7.))P,(61.R8.)P,(14.#1.(5:.(1.&8.)R9.))(57.Vsegs,(49.R=.R<.)(62.R:.)Li,(62.R:.)(5=.(1.&8.)$3=.(5>.(1;.&40.+1.))(5?.(1.&8.)(63.$;.Ln,$;.(18.(14.#1.R1.)(14.R1.(5:.(1.&8.)R<.)))R1.)R;.))Li,(62.R:.)(49.(4;.(4<.R>.(60.(1.&8.)(5?.(1.&8.)(63.$;.Ln,$;.(18.(14.#1.R1.)(14.R1.(5:.(1.&8.)R<.)))R1.)R;.))))R=.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb. split.
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
    + apply materialize_syscall_effect_copyin_disjoint.
      exact (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout).
  - intros e st Hss.
    destruct (sstep_write_inv_disjoint ms model x8 buf e st
                Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

#[using="Type"] Lemma srz_write1_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pmodel,$0.Px8,(1.&40.)Pbuf,(2.(1.&8.))PT,$4>.P,(4.(5.(1.&40.))(45.R4.)(46.(1.&40.)))P,(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.(1:.R6.#1.)(5:.(1.&8.)R3.))(9.(3.(1.&40.)$;.)))(10.R5.))P,(5;.R6.)P,(4.(5.(1.&40.))(47.R8.)(<.(1.&40.)R6.))P,(4.$31.(27.&40.R7.)+40.)P,(4.(1.&40.)(1:.R:.#0.)(1;.&40.+1.))P,(4.(5.(2.(1.&8.)))(5<.R;.(1:.R;.#1.)(1:.R;.#2.))(<.(2.(1.&8.))R8.))P,(61.R9.)P,(14.#1.(5:.(1.&8.)R:.))P,Pn,$;.P,(14.#1.R1.)P,(14.R2.(5:.(1.&8.)R=.))(4?.Vsegs,(49.(4;.(4<.R11.(60.(1.&8.)(5?.(1.&8.)R3.R>.))))R10.)R=.)(4?.Vsegs,(49.R?.R>.)(64.(1;.&40.+1.)R<.R;.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 buf T Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1_disjoint ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).

#[using="Type"] Lemma msteps_acc_one : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pms',$12.Pranges,(2.$65.)P,(4.(5.(1.&40.))(47.R3.)(46.(1.&40.)))P,(4.(66.(67.$12.))(68.Vsegs,R4.)(69.(67.$12.)(6:.$12.R3.R2.)))(6;.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' ranges Hsvc Hstep.
  rewrite <- (app_nil_r ranges).
  eapply msta_step; [exact Hsvc | exact Hstep | apply msta_refl].
Qed.

#[using="Type"] Lemma msteps_acc_trans : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pms',$12.Pms'',$12.Paccs1,(2.(3.(1.&40.)$;.))Paccs2,(2.(3.(1.&40.)$;.))P,(6;.R5.R4.R2.)P,(6;.R5.R4.R2.)(6;.R7.R5.(17.(3.(1.&40.)$;.)R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros ms ms' ms'' accs1 accs2 H; revert accs2 ms''.
  induction H as [ms | ms ms1 ms2 ranges accs Hsvc Hstep H IH];
    intros accs2 ms'' H2; [exact H2|].
  rewrite <- app_assoc. eapply msta_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_msteps_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pms',$12.Pmodel,$0.Paccs,(2.(3.(1.&40.)$;.))PT,$4>.P,(4.(5.(1.&40.))(45.R3.)(46.(1.&40.)))P,(6;.R6.R5.R3.)P,(=.R4.(10.R5.))P,(4?.Vsegs,(49.R7.R6.)R4.)(4?.Vsegs,(49.R9.R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model accs T Hh Hms; revert T;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros T Hout Hc; [exact Hc|].
  eapply srz_step_disjoint;
    [ exact Hh | exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.

#[using="Type"] Lemma rz_msteps_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pms',$12.Pmodel,$0.Paccs,(2.(3.(1.&40.)$;.))PT,$4>.P,(4.(5.(1.&40.))(45.R3.)(46.(1.&40.)))P,(6;.R6.R5.R3.)P,(=.R4.(10.R5.))P,(6<.Vsegs,(49.R7.R6.)R4.)(6<.Vsegs,(49.R9.R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model accs T Hh Hms; revert T;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros T Hout Hc; [exact Hc|].
  eapply rz_step_disjoint;
    [ exact Hh | exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ts_msteps_disjoint : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pms,$12.Pms',$12.Pmodel,$0.Paccs,(2.(3.(1.&40.)$;.))P,(6;.R4.R3.R1.)P,(=.R2.(10.R3.))P,(51.Vsegs,R5.R4.)(51.Vsegs,R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model accs Hms;
    induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
    intros Hout Hspin; [exact Hspin|].
  eapply ts_step_disjoint;
    [ exact Hsvc | exact Hstep
    | exact (accesses_outside_lazy_app_l ranges accs _ Hout)
    | apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hspin] ].
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
(* [comment removed for export] *)

End WithFP1.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma stepacc_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma stepacc_branch_tk_gen : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pregs,(6=.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(5.(1.&8.))Prom,P,(1.&40.)(5.(1.&8.))Pw,(1.&20.)Pc,$6>.Prs1,(1.&5.)Prs2,(1.&5.)Pimm,(1.&=.)P,(4.(5.(1.&20.))(6?.R:.R8.)(<.(1.&20.)R5.))P,(4.$1=.(70.R6.)$22.)P,(4.(5.(3.$71.$31.))(72.R7.)(<.(3.$71.$31.)(?.$71.$31.(73.R6.R5.R4.R3.)+4.)))P,(4.$1=.(74.R7.(75.R<.R6.)(75.R<.R5.))$1?.)(4.(66.(67.$12.))(68.R>.(76.Vfx,R=.R<.R;.R:.))(69.(67.$12.)(6:.$12.(76.Vfx,R=.(77.R<.(78.&=.R5.))R;.R:.)(9.$65.))))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_branch_ft_gen : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pregs,(6=.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(5.(1.&8.))Prom,P,(1.&40.)(5.(1.&8.))Pw,(1.&20.)Pc,$6>.Prs1,(1.&5.)Prs2,(1.&5.)Pimm,(1.&=.)P,(4.(5.(1.&20.))(6?.R:.R8.)(<.(1.&20.)R5.))P,(4.$1=.(70.R6.)$22.)P,(4.(5.(3.$71.$31.))(72.R7.)(<.(3.$71.$31.)(?.$71.$31.(73.R6.R5.R4.R3.)+4.)))P,(4.$1=.(74.R7.(75.R<.R6.)(75.R<.R5.))$22.)(4.(66.(67.$12.))(68.R>.(76.Vfx,R=.R<.R;.R:.))(69.(67.$12.)(6:.$12.(76.Vfx,R=.(79.R<.+4.)R;.R:.)(9.$65.))))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_lui : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs
           else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
          (v_addi pc 4) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_jal_x0 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pregs,(6=.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(5.(1.&8.))Prom,P,(1.&40.)(5.(1.&8.))Pw,(1.&20.)Pimm,(1.&15.)P,(4.(5.(1.&20.))(6?.R7.R5.)(<.(1.&20.)R2.))P,(4.$1=.(70.R3.)$22.)P,(4.(5.(3.$71.$31.))(72.R4.)(<.(3.$71.$31.)(?.$71.$31.(7:.(7;.&5.=$7<.)R3.)+4.)))(4.(66.(67.$12.))(68.R:.(76.Vfx,R9.R8.R7.R6.))(69.(67.$12.)(6:.$12.(76.Vfx,R9.(77.R8.(78.&15.R4.))R7.R6.)(9.$65.))))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  rewrite is_x0_0; cbv beta iota.
  rewrite b_addsext. reflexivity.
Qed.

#[using="Type"] Lemma stepacc_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
          (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) []).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma stepacc_ecall : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Psegs,(2.$37.)Pregs,(6=.&5.(1.&40.))Ppc,(1.&40.)Pmem,P,(1.&40.)(5.(1.&8.))Prom,P,(1.&40.)(5.(1.&8.))Pw,(1.&20.)P,(4.(5.(1.&20.))(6?.R6.R4.)(<.(1.&20.)R1.))P,(4.$1=.(70.R2.)$1?.)(4.(66.(67.$12.))(68.R8.(76.Vfx,R7.R6.R5.R4.))(69.(67.$12.)(6:.$12.(7=.R7.(7>.Vfx,)R6.(<.(1.&40.)(75.R7.(7;.&5.+11.$7<.)))(46.(1.&40.))(7?.Vfx,)R5.R4.)(9.$65.))))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma stepacc_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma stepacc_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite b_lb_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma stepacc_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma stepacc_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 16 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 16) with 65536%Z.
    change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma stepacc_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma stepacc_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 32 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 32) with 4294967296%Z.
    change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma stepacc_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
  MachineOk (@mkAccessReport machine_state
    (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
          (v_addi pc 4) mem rom)
    [(v_addi (getr regs rs) (bv_signed imm), 8%nat)]).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  stepacc_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AsanInitReal.
Variable segs : list Segment.

(* [comment removed for export] *)
Variables (ms1 : machine_state) (model : Model) (x8a : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc1 : ms_svc_pending ms1 = Some x8a.
Hypothesis Hno1 : bv_unsigned x8a = 222%Z.
Hypothesis Hargs1 : mmap_args_ok_noreserve ms1.

Let nZ1 : Z := page_round_up_Z (bv_unsigned (ms_gpr ms1 1)).
Let n1 : word := page_round_up (ms_gpr ms1 1).
Let model1 (a1 : word) : Model := mmap_model_noreserve a1 n1 model.
Let post1 (a1 : word) : machine_state :=
  advance_past_svc (apply_effect ms1 (mkEffect a1 [] [(a1, n1)])).

(* [comment removed for export] *)
Hypothesis Hrefuse1 : forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 ms1 (errno_ret e))) model.
Hypothesis Hex1 : exists a, grant_ok_nr (ms_gpr ms1 0) model a nZ1 = true.

(* [comment removed for export] *)
Variable ms2 : word -> machine_state.
Variable accs1 : word -> list (word * nat).
Hypothesis Hwalk1 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R1.VnZ1,)$1?.)(81.Vsegs,A1.Vpost1,R2.A1.Vms2,R2.A1.Vaccs1,R2.)")
(* [comment removed for export] *).
Hypothesis Hout1 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R1.VnZ1,)$1?.)(=.A1.Vaccs1,R2.(10.A1.Vmodel1,R2.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Variable x8b : word.
Hypothesis Hno2 : bv_unsigned x8b = 222%Z.
Hypothesis Hsvc2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  ms_svc_pending (ms2 a1) = Some x8b.
Hypothesis Hargs2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  mmap_args_ok (ms2 a1).

Let nZ2 (a1 : word) : Z := page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1)).
Let n2 (a1 : word) : word := page_round_up (ms_gpr (ms2 a1) 1).
Let model2 (a1 a2 : word) : Model := mmap_model a2 (n2 a1) (model1 a1).
Let post2 (a1 a2 : word) : machine_state :=
  advance_past_svc (apply_effect (ms2 a1) (mkEffect a2 [] [(a2, n2 a1)])).

(* [comment removed for export] *)
Hypothesis Hrefuse2 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R1.VnZ1,)$1?.)Pe,$31.P,(16.$31.R1.$36.)(51.Vsegs,(4;.(4<.A1.Vms2,R4.(3<.R2.)))A1.Vmodel1,R4.)")
(* [comment removed for export] *).
Hypothesis Hex2 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R1.VnZ1,)$1?.)(42.(1.&40.)La2,(1.&40.)(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R1.A1.VnZ2,R3.)$1?.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Variable ms3 : word -> word -> machine_state.
Variable accs2 : word -> word -> list (word * nat).
Hypothesis Hwalk2 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R2.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R2.A1.VnZ2,R3.)$1?.)(81.Vsegs,A2.Vpost2,R4.R3.A2.Vms3,R4.R3.A2.Vaccs2,R4.R3.)")
(* [comment removed for export] *).
Hypothesis Hout2 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R2.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R2.A1.VnZ2,R3.)$1?.)(=.A2.Vaccs2,R4.R3.(10.A2.Vmodel2,R4.R3.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Variable buf : list byte.
Hypothesis Hbufnb : (1 <= length buf)%nat.
Hypothesis Hbufmod : buf_modeled buf.
Variable x8c : word.
Hypothesis Hno3 : bv_unsigned x8c = 64%Z.
Hypothesis Hw_svc : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R2.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R2.A1.VnZ2,R3.)$1?.)(4.(5.(1.&40.))(47.A2.Vms3,R4.R3.)(<.(1.&40.)Vx8c,))")
(* [comment removed for export] *).
Hypothesis Hw_fd1 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R2.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R2.A1.VnZ2,R3.)$1?.)(4.(1.&40.)(1:.A2.Vms3,R4.R3.#0.)(1;.&40.+1.))")
(* [comment removed for export] *).
Hypothesis Hw_read : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R2.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R2.A1.VnZ2,R3.)$1?.)(4.(5.(2.(1.&8.)))(5<.A2.Vms3,R4.R3.(1:.A2.Vms3,R4.R3.#1.)(1:.A2.Vms3,R4.R3.#2.))(<.(2.(1.&8.))Vbuf,))")
(* [comment removed for export] *).
Hypothesis Hw_out : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R2.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R3.#0.)A1.Vmodel1,R3.R2.A1.VnZ2,R3.)$1?.)(=.(>.(3.(1.&40.)$;.)(?.(1.&40.)$;.(1:.A2.Vms3,R4.R3.#1.)(5:.(1.&8.)Vbuf,))(9.(3.(1.&40.)$;.)))(10.A2.Vmodel2,R4.R3.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Variable msE : word -> word -> nat -> machine_state.
Variable accs3 : word -> word -> nat -> list (word * nat).
Hypothesis Hwalk3 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)Pn,$;.P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R3.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R4.#0.)A1.Vmodel1,R4.R3.A1.VnZ2,R4.)$1?.)P,(14.#1.R3.)P,(14.R4.(5:.(1.&8.)Vbuf,))(81.Vsegs,(4;.(4<.A2.Vms3,R7.R6.(60.(1.&8.)(5?.(1.&8.)R5.Vbuf,))))A3.VmsE,R7.R6.R5.A3.Vaccs3,R7.R6.R5.)")
(* [comment removed for export] *).
Hypothesis Hout3 : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)Pn,$;.P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R3.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R4.#0.)A1.Vmodel1,R4.R3.A1.VnZ2,R4.)$1?.)P,(14.#1.R3.)P,(14.R4.(5:.(1.&8.)Vbuf,))(=.A3.Vaccs3,R7.R6.R5.(10.A2.Vmodel2,R7.R6.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Variables (x8d : word) (cs : word).
Hypothesis HE_no : is_exit_no x8d.
Hypothesis HE_svc : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)Pn,$;.P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R3.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R4.#0.)A1.Vmodel1,R4.R3.A1.VnZ2,R4.)$1?.)P,(14.#1.R3.)P,(14.R4.(5:.(1.&8.)Vbuf,))(4.(5.(1.&40.))(47.A3.VmsE,R7.R6.R5.)(<.(1.&40.)Vx8d,))")
(* [comment removed for export] *).
Hypothesis HE_code : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Pa1,(1.&40.)Pa2,(1.&40.)Pn,$;.P,(4.$1=.(80.(1:.Vms1,#0.)Vmodel,R3.VnZ1,)$1?.)P,(4.$1=.(53.(1:.A1.Vms2,R4.#0.)A1.Vmodel1,R4.R3.A1.VnZ2,R4.)$1?.)P,(14.#1.R3.)P,(14.R4.(5:.(1.&8.)Vbuf,))(4.(1.&40.)(82.&40.(1:.A3.VmsE,R7.R6.R5.#0.)(1;.&40.+??.))Vcs,)")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="x8a Hh Hfd Hsvc1 Hno1 Hargs1 nZ1 n1 model1 post1 Hrefuse1 Hex1 ms2 accs1 Hwalk1 Hout1 x8b Hno2 Hsvc2 Hargs2 nZ2 n2 model2 post2 Hrefuse2 Hex2 ms3 accs2 Hwalk2 Hout2 Hbufnb Hbufmod x8c Hno3 Hw_svc Hw_fd1 Hw_read Hw_out msE accs3 Hwalk3 Hout3 x8d HE_no HE_svc HE_code"] Theorem asan_init_srealizes :
  srealizes segs (mkCfg ms1 model)
    (t_write_ch (Z_to_bv 64 1) buf (t_exit cs (m_fs model))).
Proof.
  eapply srz_mmap_spin_noreserve;
    [ exact Hh | exact Hsvc1 | exact Hno1 | exact Hargs1 | exact Hrefuse1 |
    | exact Hex1 ].
  intros a1 Hg1.
  eapply srz_msteps_disjoint;
    [ exact Hh | exact (Hwalk1 a1 Hg1) | exact (Hout1 a1 Hg1) | ].
  eapply srz_mmap_spin_lazy;
    [ exact Hh | exact (Hsvc2 a1 Hg1) | exact Hno2 | exact (Hargs2 a1 Hg1)
    | exact (Hrefuse2 a1 Hg1) | | exact (Hex2 a1 Hg1) ].
  intros a2 Hg2.
  eapply srz_msteps_disjoint;
    [ exact Hh | exact (Hwalk2 a1 a2 Hg1 Hg2) | exact (Hout2 a1 a2 Hg1 Hg2) | ].
  eapply srz_write1_disjoint;
    [ exact Hh | exact (Hw_out a1 a2 Hg1 Hg2) | exact Hfd
    | exact (Hw_svc a1 a2 Hg1 Hg2) | exact Hno3 | exact (Hw_fd1 a1 a2 Hg1 Hg2)
    | exact (Hw_read a1 a2 Hg1 Hg2) | exact Hbufmod | exact Hbufnb | ].
  intros n Hn1 Hn2.
  eapply srz_msteps_disjoint;
    [ exact Hh | exact (Hwalk3 a1 a2 n Hg1 Hg2 Hn1 Hn2)
    | exact (Hout3 a1 a2 n Hg1 Hg2 Hn1 Hn2) | ].
  rewrite <- (HE_code a1 a2 n Hg1 Hg2 Hn1 Hn2).
  apply (srz_exit segs (msE a1 a2 n) (model2 a1 a2) x8d);
    [ exact Hh | exact (HE_svc a1 a2 n Hg1 Hg2 Hn1 Hn2) | exact HE_no ].
Qed.

(* [comment removed for export] *)
#[using="x8a Hh Hfd Hsvc1 Hno1 Hargs1 nZ1 n1 model1 post1 Hrefuse1 Hex1 ms2 accs1 Hwalk1 Hout1 x8b Hno2 Hsvc2 Hargs2 nZ2 n2 model2 post2 Hrefuse2 Hex2 ms3 accs2 Hwalk2 Hout2 Hbufnb Hbufmod x8c Hno3 Hw_svc Hw_fd1 Hw_read Hw_out msE accs3 Hwalk3 Hout3 x8d HE_no HE_svc HE_code"] Theorem asan_init_obs_iff : ltac2:(CDefT.buildp (gd_tbl_NoReserve ()) "Ptr,(2.$3=.)(83.(84.Vsegs,(49.Vms1,Vmodel,)R1.)(42.(2.$3=.)Lfull,(2.$3=.)(18.(85.(1;.&40.+1.)(>.(2.(1.&8.))Vbuf,(9.(2.(1.&8.))))R1.)(86.$3=.R2.(17.$3=.R1.(>.$3=.(87.Vcs,(88.Vmodel,))(9.$3=.)))))))")
(* [comment removed for export] *).
Proof.
  intro tr.
  rewrite (srealizes_obs_iff segs _ _ asan_init_srealizes tr).
  assert (Hall : Forall (fun b : list byte => (1 <= length b)%nat) [buf])
    by (constructor; [exact Hbufnb | constructor]).
  exact (t_writes_ch_pick_exit_iff (Z_to_bv 64 1) [buf] cs (m_fs model) tr Hall).
Qed.

#[using="x8a Hh Hfd Hsvc1 Hno1 Hargs1 nZ1 n1 model1 post1 Hrefuse1 Hex1 ms2 accs1 Hwalk1 Hout1 x8b Hno2 Hsvc2 Hargs2 nZ2 n2 model2 post2 Hrefuse2 Hex2 ms3 accs2 Hwalk2 Hout2 buf Hbufnb Hbufmod x8c Hno3 Hw_svc Hw_fd1 Hw_read Hw_out msE accs3 Hwalk3 Hout3 x8d cs HE_no HE_svc HE_code"] Theorem asan_init_no_error : ~ reaches_error segs (mkCfg ms1 model).
Proof.
  exact (srealizes_no_error segs _ _ asan_init_srealizes).
Qed.

End AsanInitReal.
End WithFP2.
