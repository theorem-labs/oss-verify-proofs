(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim PropExec CatSim CatExec WallSim.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AllocSim () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_add"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "WithFP1.zmem"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_zeros"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.Monad.outcome"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_spec"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_brk"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "LinuxProcessSemantics.LinuxProcessSem.State.eff_ret"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_zeros"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_unmaps"; "WithFP1.brk_resolution_ok"; "WithFP1.brk_model"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_page_range"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grants"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "WithFP1.brk_grow_ok"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backed_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "WithFP1.growable"; "LinuxProcessSemantics.LinuxProcessSem.State.reserved_top"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_model_next"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps"; "WithFP1.brk_r_ok"; "WithFP1.T1"; "LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size"; "WithFP1.T2"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.forget_vm_ranges"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "WithFP1.WithSegs.to_outcomes"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec"; "WithFP1.WithSegs.outcomes_post"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exits_with"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.cosafe"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "WithFP1.WithSegs.outcome_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "OSSVerify.KrLib.ABoot.CatSim.fd1chan"; "OSSVerify.KrLib.ABoot.WallSim.to_wallexit"; "OSSVerify.KrLib.ABoot.CatSim.bufs_modeled"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "WithFP1.to_outcomes"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "WithFP1.outcomes_post"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "WithFP1.outcome_trace"; "LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma u_add_small : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pa,(0.&40.)Pb,(0.&40.)P,(1.(2.(3.&40.R2.)(3.&40.R1.))(4.+2.+40.))(5.$6.(3.&40.(7.&40.R3.R2.))(2.(3.&40.R3.)(3.&40.R2.)))")
(* [comment removed for export] *).
Proof.
  intros a b H. rewrite bv_add_unsigned, bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). pose proof (u64_range b). lia.
Qed.

#[using="Type"] Lemma word_add_0_r : forall a : word, a + Z_to_bv 64 0 = a.
Proof.
  intro a. apply bv_eq.
  rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r, bv_wrap64_mod. apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_sub_cancel : forall r t : word, r + t - r = t.
Proof.
  intros r t. apply bv_eq.
  rewrite bv_sub_unsigned, bv_add_unsigned, !bv_wrap64_mod.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned r + bv_unsigned t - bv_unsigned r)%Z
    with (bv_unsigned t) by lia.
  apply Z.mod_small. apply u64_range.
Qed.

#[using="Type"] Lemma word_neq0_unsigned : forall r : word,
  r <> Z_to_bv 64 0 -> (bv_unsigned r <> 0)%Z.
Proof.
  intros r Hne Hu. apply Hne. apply bv_eq. rewrite Hu. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat_S : forall (a : word) k,
  (a + 1) + nat_to_word k = a + nat_to_word (S k).
Proof.
  intros a k. apply bv_eq. unfold nat_to_word.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
  fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
              && Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
           then Some (Z_to_bv 8 0) else mem a.

#[using="Type"] Lemma apply_zeros_nil : forall mem, apply_zeros mem [] = mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma apply_zeros_one : forall mem b l,
  apply_zeros mem [(b, l)] = zmem mem b l.
Proof.
  intros mem b l. apply functional_extensionality. intro a.
  unfold apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
  rewrite orb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma zmem_out : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pmem,P,(0.&40.)(8.(0.&8.))Pb,(0.&40.)Pl,(0.&40.)Pa,(0.&40.)P,(9.(1.(3.&40.R1.)(3.&40.R3.))(:.(2.(3.&40.R3.)(3.&40.R2.))(3.&40.R1.)))(5.(8.(0.&8.))(;.R5.R4.R3.R2.)A1.R5.R2.)")
(* [comment removed for export] *).
Proof.
  intros mem b l a Hd. unfold zmem.
  destruct Hd as [Hd | Hd].
  - assert (E : (bv_unsigned b <=? bv_unsigned a)%Z = false) by (apply Z.leb_gt; lia).
    rewrite E. reflexivity.
  - assert (E : (bv_unsigned a <? bv_unsigned b + bv_unsigned l)%Z = false)
      by (apply Z.ltb_ge; lia).
    rewrite E, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_zmem_out : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pmem,P,(0.&40.)(8.(0.&8.))Pb,(0.&40.)Pl,(0.&40.)Pa,(0.&40.)Pn,$>.P,(:.(2.(3.&40.R2.)(?.R1.))(4.+2.+40.))P,(9.(:.(2.(3.&40.R3.)(?.R2.))(3.&40.R5.))(:.(2.(3.&40.R5.)(3.&40.R4.))(3.&40.R3.)))(5.(8.(<.(0.&8.)))(10.R8.(;.R7.R6.R5.)R4.R3.)(10.R8.R7.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs mem b l a n Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply zmem_out. lia.
Qed.

#[using="Type"] Lemma rdn_zmem_in1 : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pmem,P,(0.&40.)(8.(0.&8.))Pb,(0.&40.)Pl,(0.&40.)Pa,(0.&40.)P,(11.(:.(3.&40.R3.)(3.&40.R1.))(1.(3.&40.R1.)(2.(3.&40.R3.)(3.&40.R2.))))(5.(8.(<.(0.&8.)))(10.R6.(;.R5.R4.R3.)R2.#1.)(12.(<.(0.&8.))(13.(0.&8.)(14.&8.=)(15.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros segs mem b l a [Hlo Hhi]. cbn [rdn]. unfold zmem.
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_app : forall {bs1 bs2 : list byte} m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word (length bs1)) bs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 m a.
  - cbn [app wbytes length].
    replace (a + nat_to_word 0) with a; [reflexivity|].
    symmetry. exact (word_add_0_r a).
  - cbn [app wbytes length].
    rewrite IH, word_add_nat_S. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma with_vmmaps_fds : forall h m, m_fds (with_vmmaps h m) = m_fds m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_fs : forall h m, m_fs (with_vmmaps h m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_vm : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_lazy : forall h m,
  m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma fd1chan_with_vmmaps : forall h m, fd1chan m -> fd1chan (with_vmmaps h m).
Proof. intros h m H. unfold fd1chan in *. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fd1chan_forget_vm_ranges : forall ranges m,
  fd1chan m -> fd1chan (forget_vm_ranges ranges m).
Proof.
  induction ranges as [|[a n] ranges IH]; intros m H; cbn [forget_vm_ranges].
  - exact H.
  - apply IH. unfold fd1chan, vm_forget_range, with_vm_backing in *.
    cbn [m_fds m_fd] in *. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_brk : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pregs,(16.&5.(0.&40.))Ppc,(0.&40.)Px8,(0.&40.)Pmem,P,(0.&40.)(8.(0.&8.))Prom,P,(0.&40.)(8.(0.&8.))Pr,(0.&40.)Pzs,(<.(17.(0.&40.)(0.&40.)))(5.$18.(19.(1:.(1;.R7.(1<.Vfx,)R6.(12.(0.&40.)R5.)(1=.(0.&40.))(1>.Vfx,)R4.R3.)(1?.R2.(15.(17.(0.&40.)(<.(0.&8.))))R1.(15.(17.(0.&40.)(0.&40.)))(15.$20.)(15.(17.(0.&40.)$>.)))))(21.Vfx,(22.R7.(23.&5.+:.$24.)R2.)(25.R6.+4.)(26.R4.R1.)R3.))")
(* [comment removed for export] *).
Proof.
  intros regs pc x8 mem rom r zs.
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma in_sysno_sys_input214 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

#[using="Type"] Lemma in_arg0_sys_input214 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma syscall_spec_brk : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pms,$18.Px8,(0.&40.)Pmodel,$27.Po,(28.$29.)P,(5.$6.(3.&40.R3.)+=6.)(2:.(2;.(2<.R6.R5.R4.)R3.R2.)(2=.(2>.R5.#0.)(2<.R6.R5.R4.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input214, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Definition vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] None None None.

Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
  Mmap.brk_grow_ok (vm_model h) req r.

(* [comment removed for export] *)
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Mmap.brk_r_ok (vm_model h) req r = true.

(* [comment removed for export] *)
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
  Mmap.brk_r_ok m req r = true.

(* [comment removed for export] *)
Definition brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r.

(* [comment removed for export] *)
#[using="Type"] Lemma fd1chan_brk_model : forall req r m,
  fd1chan m -> fd1chan (brk_model req r m).
Proof.
  intros req r m H. unfold brk_model, with_brk_next. cbv zeta.
  apply fd1chan_forget_vm_ranges, fd1chan_with_vmmaps, H.
Qed.

#[using="Type"] Lemma check_brk_ok_inv : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preq,(0.&40.)Peff,$29.Pm,$27.Pm',$27.Pevs,(<.$2?.)P,(5.$30.(31.R5.R4.R3.)(32.R2.R1.))(11.(5.$29.R5.(1?.(33.R5.)(15.(17.(0.&40.)(<.(0.&8.))))(34.R6.(33.R5.)(35.(36.R4.)))(37.(33.R5.)(35.(36.R4.)))(15.$20.)(15.(17.(0.&40.)$>.))))(11.(5.(<.$2?.)R2.(15.$2?.))(11.(38.R4.R6.(33.R5.))(5.$27.R3.(39.R6.(33.R5.)R4.)))))")
(* [comment removed for export] *).
Proof.
  intros req [r ws zs us cs copyins] m m' evs H.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (Mmap.brk_r_ok m req r) eqn:HR; [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZ;
    [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HU;
    [|cbn [andb] in H; discriminate].
  cbn [andb] in H.
  apply listNN_eqb_eq in HZ. subst zs.
  apply listNN_eqb_eq in HU. subst us.
  inversion H; clear H; subst.
  cbn [eff_ret]. unfold brk_resolution_ok, brk_model.
  repeat split; try reflexivity. exact HR.
Qed.

#[using="Type"] Lemma check_brk_ok_intro : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preq,(0.&40.)Pr,(0.&40.)Pm,$27.P,(38.R1.R3.R2.)(5.$30.(31.R4.(1?.R3.(15.(17.(0.&40.)(<.(0.&8.))))(34.R4.R3.(35.(36.R2.)))(37.R3.(35.(36.R2.)))(15.$20.)(15.(17.(0.&40.)$>.)))R2.)(32.(39.R4.R3.R2.)(15.$2?.)))")
(* [comment removed for export] *).
Proof.
  intros req r m HR. unfold brk_resolution_ok in HR.
  unfold check_brk. rewrite HR.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  unfold brk_model. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_ok_iff : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pms,$18.Px8,(0.&40.)Pmodel,$27.Peff,$29.Pmodel',$27.Pevs,(<.$2?.)P,(5.$6.(3.&40.R5.)+=6.)(2:.(2;.(2<.R8.R7.R6.)R5.(3:.$29.R4.R3.R2.))(11.(5.$29.R4.(1?.(33.R4.)(15.(17.(0.&40.)(<.(0.&8.))))(34.(2>.R7.#0.)(33.R4.)(35.(36.R5.)))(37.(33.R4.)(35.(36.R5.)))(15.$20.)(15.(17.(0.&40.)$>.))))(11.(5.(<.$2?.)R2.(15.$2?.))(11.(38.R5.(2>.R7.#0.)(33.R4.))(5.$27.R3.(39.(2>.R7.#0.)(33.R4.)R5.))))))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model eff model' evs Hno. split.
  - intro H. apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
    apply check_brk_complete_ok in H.
    apply check_brk_ok_inv in H. exact H.
  - intros (Heff & -> & Hok & ->).
    apply (proj2 (syscall_spec_brk _ _ _ _ _ Hno)). apply check_brk_sound_ok.
    rewrite Heff at 1. cbn [eff_ret].
    apply check_brk_ok_intro. exact Hok.
Qed.

#[using="Type"] Lemma brk_ok_intro : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pms,$18.Px8,(0.&40.)Pmodel,$27.Pr,(0.&40.)P,(5.$6.(3.&40.R3.)+=6.)P,(38.R3.(2>.R5.#0.)R2.)(2;.(2<.R7.R6.R5.)R4.(3:.$29.(1?.R3.(15.(17.(0.&40.)(<.(0.&8.))))(34.(2>.R6.#0.)R3.(35.(36.R4.)))(37.R3.(35.(36.R4.)))(15.$20.)(15.(17.(0.&40.)$>.)))(39.(2>.R6.#0.)R3.R4.)(15.$2?.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model r Hno Hok.
  apply (brk_ok_iff segs ms x8 model _ _ _ Hno). cbn [eff_ret]. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pms,$18.Px8,(0.&40.)Pmodel,$27.P,(5.$6.(3.&40.R2.)+=6.)(3;.(2;.(2<.R5.R4.R3.)R2.(3<.$29.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno H.
  apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
  apply (check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in H.
  unfold check_brk in H.
  destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (Z_to_bv 64 0)
            && listNN_eqb []
                 (brk_zeros (ms_gpr ms 0) (Z_to_bv 64 0) (vm_brk (m_vmmaps model)))
            && listNN_eqb []
                 (brk_unmaps (Z_to_bv 64 0) (vm_brk (m_vmmaps model))));
    discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_receptive : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Pms,$18.Px8,(0.&40.)Pmodel,$27.P,(5.$6.(3.&40.R2.)+=6.)(3=.$29.Leff,$29.(3=.$27.Lmodel',$27.(2;.(2<.R7.R6.R5.)R4.(3:.$29.R2.R1.(15.$2?.)))))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model Hno.
  pose (r := vm_brk (m_vmmaps model)).
  exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
         (brk_model (ms_gpr ms 0) r model).
  apply brk_ok_intro; [exact Hno|].
  unfold brk_resolution_ok, Mmap.brk_r_ok, r. cbv zeta.
  destruct (w_is0 (ms_gpr ms 0)
            || Z.ltb (bv_unsigned (ms_gpr ms 0))
                     (bv_unsigned (min_brk (m_vmmaps model)))).
  - apply bv_eqb_refl.
  - destruct (Z.ltb (bv_unsigned (ms_gpr ms 0))
                    (bv_unsigned (vm_brk (m_vmmaps model)))).
    + rewrite bv_eqb_refl, orb_true_r. reflexivity.
    + rewrite bv_eqb_refl, orb_true_r, andb_true_l.
      unfold brk_grow_ok, Mmap.brk_grow_ok.
      now rewrite Z.ltb_irrefl, andb_false_r.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_zeros_grow : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preq,(0.&40.)Pr,(0.&40.)Pold,(0.&40.)P,(3;.(5.(0.&40.)R3.(14.&40.=)))P,(1.=(3.&40.R2.))P,(1.(3.&40.R3.)(3.&40.R4.))(5.(<.(17.(0.&40.)(0.&40.)))(34.R6.R5.R4.)(3>.(3?.(3.&40.R4.))(3?.(3.&40.R5.))))")
(* [comment removed for export] *).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grants_grow : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preq,(0.&40.)Pr,(0.&40.)Pold,(0.&40.)P,(3;.(5.(0.&40.)R3.(14.&40.=)))P,(1.=(3.&40.R2.))P,(1.(3.&40.R3.)(3.&40.R4.))(5.(<.(17.(0.&40.)(0.&40.)))(40.R6.R5.R4.)(13.(17.(0.&40.)(0.&40.))(41.(0.&40.)(0.&40.)R4.(42.&40.R5.R4.))(15.(17.(0.&40.)(0.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

#[using="Type"] Lemma brk_zeros_query : forall r old, brk_zeros (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_zeros, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma brk_grants_query : forall r old, brk_grants (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_grants, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma brk_zeros_keep : forall req old, brk_zeros req old old = [].
Proof.
  intros req old. unfold brk_zeros, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma brk_grants_keep : forall req old, brk_grants req old old = [].
Proof.
  intros req old. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof.
  intros old. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
  unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_query : forall h r,
  r = vm_brk h -> brk_unmaps r (vm_brk h) = [].
Proof. intros h r ->. apply brk_unmaps_keep. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_grow : forall r old,
  (bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof.
  intros r old H. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
  assert (E : (page_round_up_Z (bv_unsigned r)
               <? page_round_up_Z (bv_unsigned old))%Z = false)
    by (apply Z.ltb_ge, page_round_up_Z_mono, H).
  unfold brk_page_range. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grow_ok_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  brk_grow_ok h req r
  = ((if (page_round_up_Z (bv_unsigned (vm_brk h))
          <? page_round_up_Z (bv_unsigned r))%Z
      then (page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
           && region_free (vm_reserved h ++ vm_maps h)
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (vm_brk h))))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                             - page_round_up_Z (bv_unsigned (vm_brk h))))
      else true)
     && (vm_backed_bytes h + bv_unsigned (r - vm_brk h) <=? vm_limit h)%Z)%bool.
Proof.
  intros h req r Hreq H0 Hlt.
  assert (Hmaps : m_vmmaps (vm_model h) = h) by reflexivity.
  assert (Hbacked : vm_backing_used (vm_model h) = vm_backed_bytes h).
  { unfold vm_backing_used, vm_model.
    cbv [mkModel m_vmmaps m_vm m_vm_lazy m_vm_materialized
         vmst_lazy vmst_materialized].
    change ((live_bytes (vm_backed_maps h) + 0)%Z =
            live_bytes (vm_backed_maps h)).
    apply Z.add_0_r. }
  unfold brk_grow_ok, Mmap.brk_grow_ok, Mmap.brk_budget_ok.
  rewrite Hmaps, Hbacked.
  assert (E2 : (0 <? bv_unsigned (vm_brk h))%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned (vm_brk h) <? bv_unsigned r)%Z = true)
    by (apply Z.ltb_lt; lia).
  rewrite E2, E3. reflexivity.
Qed.

#[using="Type"] Lemma brk_grow_ok_keep : forall h req,
  brk_grow_ok h req (vm_brk h) = true.
Proof.
  intros h req. unfold brk_grow_ok, Mmap.brk_grow_ok.
  cbv [vm_model mkModel m_vmmaps m_vm vm_backing_used m_vm_lazy
       m_vm_materialized vmst_lazy vmst_materialized].
  cbn [vmst_maps vm_backed_bytes maps_subtract_all].
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma page_round_up_Z_aligned : forall z,
  (0 <= z)%Z -> (z mod page_size = 0)%Z -> page_round_up_Z z = z.
Proof.
  intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
  replace (z + 4096 - 1)%Z with
    (4095 + (z / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma page_round_up_Z_bounds : forall z,
  (0 <= z)%Z ->
  (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma round8_le_page_round : forall z,
  (0 <= z)%Z ->
  ((((z + 7) / 8) * 8) <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z.
  pose proof (Z.div_mod (z + 7) 8 ltac:(lia)) as H8.
  pose proof (Z.mod_pos_bound (z + 7) 8 ltac:(lia)) as H8mod.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hp.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hpmod.
  assert (H8ceil :
    (z <= ((z + 7) / 8) * 8 <= z + 7)%Z) by lia.
  assert (Hpceil :
    (z <= ((z + 4096 - 1) / 4096) * 4096)%Z) by lia.
  set (q8 := ((z + 7) / 8)%Z) in *.
  set (qp := ((z + 4096 - 1) / 4096)%Z) in *.
  assert (Hq : (q8 <= 512 * qp)%Z) by lia.
  change (q8 * 8 <= qp * 4096)%Z.
  lia.
Qed.

#[using="Type"] Lemma round8_le_page_grant : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pold,$6.Pn,$6.P,(:.=R2.)P,(:.=R2.)P,(5.$6.(43.R4.$44.)=)(:.(45.(46.(2.R4.+7.)+8.)+8.)(47.(3?.(2.R5.R4.))R5.))")
(* [comment removed for export] *).
Proof.
  intros old n Hold Hn Hmod.
  unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod old 4096 ltac:(lia)) as Holddiv.
  replace (old + n + 4096 - 1)%Z with
    ((n + 4096 - 1) + (old / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  pose proof (round8_le_page_round n Hn).
  unfold page_round_up_Z in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_prefix : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pmaps,(<.(17.(0.&40.)(0.&40.)))Pb,(0.&40.)Psmall,(0.&40.)Pbig,(0.&40.)P,(:.(3.&40.R2.)(3.&40.R1.))P,(5.$48.(49.R5.R4.R2.)$4:.)(5.$48.(49.R6.R5.R4.)$4:.)")
(* [comment removed for export] *).
Proof.
  induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree;
    [reflexivity|].
  cbn [region_free] in Hfree |- *.
  apply andb_true_iff in Hfree as [Hhead Htail].
  apply andb_true_iff. split; [|eapply IH; eassumption].
  apply negb_true_iff in Hhead. apply negb_true_iff.
  unfold iv_overlap in Hhead |- *.
  apply andb_false_iff in Hhead. apply andb_false_iff.
  destruct Hhead as [Hhead|Hhead]; [left|right];
    apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grow_ok_aligned_grow : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Ph,$4;.Preq,(0.&40.)Pr,(0.&40.)P,(3;.(5.(0.&40.)R2.(14.&40.=)))P,(1.=(3.&40.(35.R4.)))P,(1.(3.&40.(35.R5.))(3.&40.R3.))P,(5.$6.(43.(3.&40.(35.R6.))$44.)=)(5.$48.(4<.R7.R6.R5.)(4=.(4=.(4>.(3?.(3.&40.R5.))(4?.R7.))(49.(50.(17.(0.&40.)(0.&40.))(51.R7.)(52.R7.))(35.R7.)(14.&40.(47.(2.(3?.(3.&40.R5.))$44.)(3.&40.(35.R7.))))))(4>.(2.(53.R7.)(3.&40.(42.&40.R5.(35.R7.))))(54.R7.))))")
(* [comment removed for export] *).
Proof.
  intros h req r Hreq Hpos Hlt Halign.
  rewrite brk_grow_ok_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk h))) by lia.
  assert (Hround : (bv_unsigned (vm_brk h)
                    < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  replace (Z_to_bv 64 (bv_unsigned (vm_brk h))) with (vm_brk h).
  - reflexivity.
  - symmetry. apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma brk_zeros_aligned_grow : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preq,(0.&40.)Pr,(0.&40.)Pold,(0.&40.)P,(3;.(5.(0.&40.)R3.(14.&40.=)))P,(1.=(3.&40.R2.))P,(1.(3.&40.R3.)(3.&40.R4.))P,(5.$6.(43.(3.&40.R4.)$44.)=)(5.(<.(17.(0.&40.)(0.&40.)))(34.R7.R6.R5.)(13.(17.(0.&40.)(0.&40.))(41.(0.&40.)(0.&40.)R5.(14.&40.(47.(3?.(3.&40.R6.))(3.&40.R5.))))(15.(17.(0.&40.)(0.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros req r old Hreq Hpos Hlt Halign.
  rewrite brk_zeros_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
  unfold brk_page_range.
  assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_aligned_grant_ok : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pres,(<.(17.(0.&40.)(0.&40.)))Pr,(0.&40.)Pw,(0.&40.)Pg,(0.&40.)Ptop,$6.Pceil,$6.P,(5.$6.(3.&40.(7.&40.R5.R4.))(2.(3.&40.R5.)(3.&40.R4.)))P,(5.$6.(3.&40.(7.&40.R6.R5.))R3.)P,(5.(0.&40.)R5.(14.&40.(47.(3?.(3.&40.(7.&40.R7.R6.)))(3.&40.R7.))))P,(1.(2.R4.$44.)(4.+2.+40.))P,(:.(3?.(3.&40.(7.&40.R9.R8.)))R5.)P,(5.$48.(49.R;.R:.(14.&40.(47.(2.(3?.(3.&40.(7.&40.R:.R9.)))$44.)(3.&40.R:.))))$4:.)(11.(5.$6.(3.&40.R9.)(47.(3?.(3.&40.(7.&40.R;.R:.)))(3.&40.R;.)))(11.(:.(3.&40.R:.)(3.&40.R9.))(11.(:.(2.(3.&40.R;.)(3.&40.R9.))R7.)(11.(:.R8.R7.)(11.(5.$48.(49.R<.R;.R:.)$4:.)(5.$48.(49.R<.R;.R9.)$4:.))))))")
(* [comment removed for export] *).
Proof.
  intros res r w g top ceil Hnowrap Htop Hg Hacp Hceil Hfree.
  pose proof (u64_range r). pose proof (u64_range w).
  pose proof (page_round_up_Z_bounds (bv_unsigned (r + w))
                (proj1 (u64_range (r + w)))).
  assert (Hps : (0 < page_size)%Z) by (vm_compute; reflexivity).
  (* [comment removed for export] *)
  assert (Hu : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
                 bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. apply Z.mod_small.
    split; [exact Hlo | exact Hhi]. }
  assert (HgU : bv_unsigned g
                = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z)
    by (subst g; apply Hu; lia).
  repeat split; rewrite ?HgU; try lia.
  (* [comment removed for export] *)
  - apply (region_free_prefix res r w
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite Hu by lia; lia | exact Hfree].
  - apply (region_free_prefix res r g
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite HgU, Hu by lia; lia | exact Hfree].
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
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
    : Prop :=
  r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
  (t = Z_to_bv 64 0 \/
   (((if (page_round_up_Z (bv_unsigned r)
          <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
      then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            <=? top)%Z
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z
                               (bv_unsigned r + bv_unsigned t)
                              + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (bv_unsigned t <=? lim)%Z)%bool = true)).

(* [comment removed for export] *)
Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
    (bufs : list (list byte))
    (r : word) : (list (list byte) * word) -> Prop := ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Lo,(17.(<.(<.(0.&8.)))(0.&40.))(9.(11.(5.(17.(<.(<.(0.&8.)))(0.&40.))R1.(41.(<.(<.(0.&8.)))(0.&40.)(15.(<.(0.&8.)))(14.&40.+4.)))(9.(5.(0.&40.)O1.(14.&40.=))(9.(:.(4.+2.+40.)(2.(3.&40.O1.)(3.&40.O3.)))(3;.(5.(0.&40.)O3.(14.&40.=))))))(11.(55.O6.O5.O4.O3.O1.)(5.(17.(<.(<.(0.&8.)))(0.&40.))R1.(41.(<.(<.(0.&8.)))(0.&40.)O2.(14.&40.=)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
    : (list (list byte) * word) -> Prop := ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Lo,(17.(<.(<.(0.&8.)))(0.&40.))(9.(11.(5.(0.&40.)O1.O3.)(5.(17.(<.(<.(0.&8.)))(0.&40.))R1.(41.(<.(<.(0.&8.)))(0.&40.)O2.(14.&40.=))))(11.(3;.(5.(0.&40.)O1.O3.))(5.(17.(<.(<.(0.&8.)))(0.&40.))R1.(41.(<.(<.(0.&8.)))(0.&40.)(15.(<.(0.&8.)))(14.&40.+4.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma brk_r_ok_query_iff : forall h r,
  brk_r_ok h (Z_to_bv 64 0) r <-> r = vm_brk h.
Proof.
  intros h r. unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  unfold w_is0. rewrite bv_eqb_refl. cbn [orb].
  apply bv_eqb_eq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reserved_top_above : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preserved,(<.(17.(0.&40.)(0.&40.)))Pr,$6.P,(:.(56.R2.)R1.)(57.(17.(0.&40.)(0.&40.))Lp,(17.(0.&40.)(0.&40.))(:.(2.(3.&40.(58.(0.&40.)(0.&40.)R1.))(3.&40.(59.(0.&40.)(0.&40.)R1.)))R3.)R3.)")
(* [comment removed for export] *).
Proof.
  induction reserved as [|[a sz] l IH]; intros r Hr; cbn [reserved_top] in *.
  - constructor.
  - constructor; [cbn [fst snd]; lia | apply IH; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_above_top : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preserved,(<.(17.(0.&40.)(0.&40.)))Plo,(0.&40.)Pn,(0.&40.)P,(:.(56.R3.)(3.&40.R2.))(5.$48.(49.R4.R3.R2.)$4:.)")
(* [comment removed for export] *).
Proof.
  induction reserved as [|[a sz] l IH]; intros lo n Hr;
    cbn [reserved_top] in *; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_above : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pl,(<.(17.(0.&40.)(0.&40.)))Plo,(0.&40.)Pn,(0.&40.)P,(57.(17.(0.&40.)(0.&40.))Lp,(17.(0.&40.)(0.&40.))(:.(2.(3.&40.(58.(0.&40.)(0.&40.)R1.))(3.&40.(59.(0.&40.)(0.&40.)R1.)))(3.&40.R3.))R3.)(5.$48.(49.R4.R3.R2.)$4:.)")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_below : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pl,(<.(17.(0.&40.)(0.&40.)))Plo,(0.&40.)Pn,(0.&40.)P,(57.(17.(0.&40.)(0.&40.))Lp,(17.(0.&40.)(0.&40.))(:.(2.(3.&40.R3.)(3.&40.R2.))(3.&40.(58.(0.&40.)(0.&40.)R1.)))R3.)(5.$48.(49.R4.R3.R2.)$4:.)")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned a <? bv_unsigned lo + bv_unsigned n)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E, andb_false_r. cbn [negb andb]. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma growable_aligned_grow : forall reserved lim top (t r : word),
  (bv_unsigned r mod page_size = 0)%Z ->
  (reserved_top reserved <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (bv_unsigned t <= lim)%Z ->
  ((if (page_round_up_Z (bv_unsigned r)
        <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
    then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
          <=? top)%Z
         && region_free reserved
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z
                             (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
    else true)
   && (bv_unsigned t <=? lim)%Z)%bool = true.
Proof.
  intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
  pose proof (proj1 (u64_range r)) as Hr0.
  rewrite (page_round_up_Z_aligned (bv_unsigned r)); [|lia|exact Halign].
  assert (Hru := page_round_up_Z_bounds
    (bv_unsigned r + bv_unsigned t) ltac:(lia)).
  assert (Hltpage :
    (bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z)
    by lia.
  rewrite (proj2 (Z.ltb_lt _ _) Hltpage).
  apply andb_true_iff. split; [apply andb_true_iff; split|].
  - apply Z.leb_le. lia.
  - rewrite Z_to_bv_bv_unsigned. apply region_free_above_top. exact Htop.
  - apply Z.leb_le. exact Hlim.
Qed.

#[using="Type"] Lemma brk_aslr_max_val : brk_aslr_max = 1073741824%Z. (* [comment removed for export] *)
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_next_query : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Ph,$4;.Pr,(0.&40.)P,(5.(0.&40.)R1.(35.R2.))(5.$4;.(5:.R3.(14.&40.=)R2.)(5;.(51.R3.)(52.R3.)(5<.R3.)(5=.R3.)R2.(54.R3.)(5>.R3.)(5?.R3.)))")
(* [comment removed for export] *).
Proof.
  intros h r ->. unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r.
  rewrite brk_grants_query, brk_unmaps_keep. reflexivity.
Qed.

#[using="Type"] Lemma brk_model_query : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pr,(0.&40.)Pm,$27.P,(5.(0.&40.)R2.(35.(36.R1.)))(5.$27.(39.(14.&40.=)R3.R2.)(60.(5;.(51.(36.R2.))(52.(36.R2.))(5<.(36.R2.))(5=.(36.R2.))R3.(54.(36.R2.))(5>.(36.R2.))(5?.(36.R2.)))R2.))")
(* [comment removed for export] *).
Proof.
  intros r m ->. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  rewrite brk_model_next_query by reflexivity. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_r_ok_grow_iff : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preserved,(<.(17.(0.&40.)(0.&40.)))Plim,$6.Ps,(0.&40.)Pr,(0.&40.)Pmaps,(<.(17.(0.&40.)(0.&40.)))Pnoaccess,(<.(17.(0.&40.)(0.&40.)))Pmb,(0.&40.)Psp,(0.&40.)Preq,(0.&40.)Pr2,(0.&40.)P,(1.=(3.&40.R2.))P,(:.(3.&40.R9.)(3.&40.R3.))P,(:.(3.&40.R9.)(3.&40.R4.))(2:.(61.(5;.R=.R9.R8.R;.R:.R<.R7.R6.)R5.R4.)(11.(9.(5.(0.&40.)R4.R5.)(5.(0.&40.)R4.R:.))(5.$48.(4<.(5;.R=.R9.R8.R;.R:.R<.R7.R6.)R5.R4.)$4:.)))")
(* [comment removed for export] *).
Proof.
  intros reserved lim s r maps noaccess mb sp req r2 Hpos Hs Hreq.
  unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    apply Z.eqb_neq. lia. }
  rewrite E0.
  assert (Hmin : (bv_unsigned req <?
                   bv_unsigned (min_brk (mkVmMapsFull reserved maps noaccess s r lim mb sp)))%Z
                 = false).
  { apply Z.ltb_ge. unfold min_brk. cbn [vm_start_brk]. lia. }
  cbn [vmst_maps]. rewrite Hmin. cbn [orb vm_brk].
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned r)) ltac:(lia)).
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma T1_iff_T2 : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Preserved,(<.(17.(0.&40.)(0.&40.)))Plim,$6.Ps,(0.&40.)Pmb,(0.&40.)Psp,(0.&40.)Pt,(0.&40.)Pbufs,(<.(<.(0.&8.)))Pr,(0.&40.)P,(3;.(5.(0.&40.)R1.(14.&40.=)))P,(:.(3.&40.R7.)(3.&40.R2.))P,(1.(2.(3.&40.R3.)(3.&40.R5.))(4.+2.+40.))Po,(17.(<.(<.(0.&8.)))(0.&40.))(2:.(62.R<.R;.(47.(3.&40.R8.)$63.)R7.R6.R5.R1.)(3=.(0.&40.)Lr2,(0.&40.)(11.(61.(5;.R=.(15.(17.(0.&40.)(0.&40.)))(15.(17.(0.&40.)(0.&40.)))R;.R6.R<.R:.R9.)(7.&40.R6.R8.)R1.)(64.(7.&40.R6.R8.)R7.R1.R2.))))")
(* [comment removed for export] *).
Proof.
  intros reserved lim s mb sp t bufs r Hr0 Hs Hnw o.
  pose proof (u64_range r) as Hur. pose proof (u64_range t) as Hut.
  pose proof (word_neq0_unsigned r Hr0) as Hur0.
  assert (Huadd : bv_unsigned (r + t) = (bv_unsigned r + bv_unsigned t)%Z)
    by (apply u_add_small; exact Hnw).
  assert (Hwant0 : r + t <> Z_to_bv 64 0).
  { intro He. apply (f_equal bv_unsigned) in He.
    rewrite Huadd in He.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
  assert (Bridge : forall r2,
             brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 <->
             (r2 = r + t \/ r2 = r)
             /\ brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                = true)
    by (intro r2; apply brk_r_ok_grow_iff with (maps := []) (noaccess := []); lia).
  split.
  - intros [[-> Hcase] | [Hg ->]].
    + (* [comment removed for export] *)
      assert (Ht0 : t <> Z_to_bv 64 0)
        by (destruct Hcase as [Hc | [Hc | Hc]]; [congruence | lia | exact Hc]).
      pose proof (word_neq0_unsigned t Ht0) as Hut0.
      exists r. split.
      * apply Bridge. split; [right; reflexivity|].
        exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)).
      * right. split; [| reflexivity].
        intro He. apply (f_equal bv_unsigned) in He.
        rewrite Huadd in He. lia.
    + (* [comment removed for export] *)
      destruct Hg as (_ & _ & Hb).
      exists (r + t). split.
      * apply Bridge. split; [left; reflexivity|].
        destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz].
        { assert (Ht0 : t = Z_to_bv 64 0)
            by (apply bv_eq; rewrite Hz; reflexivity).
          rewrite Ht0, word_add_0_r.
          exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) r). }
        destruct Hb as [Hb | Hb];
          [exfalso; apply Hz; rewrite Hb; reflexivity |].
        rewrite brk_grow_ok_grow;
          cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes];
          [| exact Hwant0 | lia | lia].
        rewrite app_nil_r, word_add_sub_cancel, Huadd, Z.add_0_l.
        exact Hb.
      * left. split; reflexivity.
  - intros (r2 & Hrok & Hb).
    apply Bridge in Hrok. destruct Hrok as (Hcase & Hgrow).
    destruct Hb as [[-> ->] | [Hne ->]].
    + (* [comment removed for export] *)
      right. split; [| reflexivity].
      split; [exact Hr0 | split; [exact Hnw |]].
      destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz];
        [left; apply bv_eq; rewrite Hz; reflexivity | right].
      rewrite brk_grow_ok_grow in Hgrow;
        cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes] in *;
        [| exact Hwant0 | lia | lia].
      rewrite app_nil_r, word_add_sub_cancel, Huadd, Z.add_0_l in Hgrow.
      exact Hgrow.
    + (* [comment removed for export] *)
      left. split; [reflexivity |].
      right. right.
      intro Ht0. subst t.
      rewrite word_add_0_r in Hne, Hcase.
      destruct Hcase as [Hc | Hc]; exact (Hne Hc).
Qed.

#[using="Type"] Lemma T2_fail_iff : forall want bufs r2,
  r2 <> want -> forall o, T2 want bufs r2 o <-> o = ([], Z_to_bv 64 4).
Proof.
  intros want bufs r2 Hne o. unfold T2. tauto.
Qed.

#[using="Type"] Lemma T2_succ_iff : forall want bufs o,
  T2 want bufs want o <-> o = (bufs, Z_to_bv 64 0).
Proof.
  intros want bufs o. unfold T2. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

(* [comment removed for export] *)
#[using="Type"] Lemma tou_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_outcomes ms' model U -> to_outcomes ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tou_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma forget_vm_ranges_frame : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pranges,(<.(17.(0.&40.)(0.&40.)))Pmodel,$27.(11.(5.(8.(0.&40.))(65.(66.R2.R1.))(65.R1.))(11.(5.$67.(68.(66.R2.R1.))(68.R1.))(11.(5.(<.(17.(0.&40.)$69.))(6:.(66.R2.R1.))(6:.R1.))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R1.)(15.(17.(0.&40.)(0.&40.))))(5.(<.(17.(0.&40.)(0.&40.)))(6;.(66.R3.R2.))(15.(17.(0.&40.)(0.&40.)))))))")
(* [comment removed for export] *).
Proof.
  induction ranges as [|[a n] ranges IH]; intros model; cbn [forget_vm_ranges].
  - auto.
  - specialize (IH (vm_forget_range (bv_unsigned a)
      (bv_unsigned a + bv_unsigned n) model)).
    destruct IH as (Hhalt & Hfs & Hfds & Hlazy).
    unfold vm_forget_range, with_vm_backing in Hhalt, Hfs, Hfds, Hlazy.
    cbn [m_halted m_fs m_fds m_vm_lazy] in Hhalt, Hfs, Hfds, Hlazy.
    repeat split; try assumption.
    intro Hempty. apply Hlazy. rewrite Hempty. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_step_shape : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Px8,(0.&40.)Pmodel,$27.Peff,$29.Pmodel',$27.Pevs,(<.$2?.)P,(5.(8.(0.&40.))(65.R4.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R5.)(15.(17.(0.&40.)(0.&40.))))P,(5.$6.(3.&40.R7.)+=6.)P,(2;.(2<.Vsegs,R9.R8.)R7.(3:.$29.R6.R5.R4.))(11.(5.(<.$2?.)R5.(15.$2?.))(11.(5.(8.(0.&40.))(65.R6.)(1=.(0.&40.)))(11.(5.$67.(68.R6.)(68.R8.))(11.(5.(<.(17.(0.&40.)$69.))(6:.R6.)(6:.R8.))(5.(<.(17.(0.&40.)(0.&40.)))(6;.R6.)(6;.R8.))))))")
(* [comment removed for export] *).
Proof.
  intros ms x8 model eff model' evs Hh Hlazy Hno Hs.
  apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs.
  destruct Hs as (_ & -> & _ & ->).
  unfold brk_model, with_brk_next. cbv zeta.
  destruct (forget_vm_ranges_frame
    (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model)))
    (with_vmmaps
      (brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff_ret eff)) model))
    as (Hhalt & Hfs & Hfds & Hlazy').
  repeat split.
  - rewrite Hhalt. unfold with_vmmaps. cbn [m_halted]. exact Hh.
  - rewrite Hfs. unfold with_vmmaps. reflexivity.
  - rewrite Hfds. unfold with_vmmaps. reflexivity.
  - rewrite Hlazy. apply Hlazy'.
    unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlazy.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_brk_inv : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.Px8,(0.&40.)Pevs,(<.$2?.)Pst,$6<.P,(5.(8.(0.&40.))(65.R4.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R5.)(15.(17.(0.&40.)(0.&40.))))P,(5.(8.(0.&40.))(6=.R7.)(12.(0.&40.)R5.))P,(5.$6.(3.&40.R6.)+=6.)P,(6>.Vsegs,(6?.R9.R8.)R6.R5.)(3=.$29.Leff,$29.(3=.$27.Lmodel',$27.(11.(2;.(2<.Vsegs,R<.R:.)R;.(3:.$29.R2.R1.(15.$2?.)))(11.(5.(<.$2?.)R9.(15.$2?.))(5.$6<.R8.(70.(6?.(19.(1:.R<.R2.))R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    assert (Hx : x0 = x8) by congruence; subst x0.
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno H3)
      as (He & _ & _ & _ & Hlazy').
    subst evs.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)) in H7.
    inversion H7; subst model''.
    exists eff, model'; auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
        as (He & _ & _ & _ & Hlazy'); subst evs0;
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hhalt : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      congruence
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hkill : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
  wevents (fst o) ++ [ExitEv (snd o) fs].

(* [comment removed for export] *)
Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
  fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.

#[using="Type"] Lemma to_outcomes_exec : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R3.R2.R1.)P,(5.(8.(0.&40.))(65.R3.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R4.)(15.(17.(0.&40.)(0.&40.))))(72.Vsegs,(6?.R6.R5.)(73.(68.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - (* [comment removed for export] *)
    eapply exec_conseq;
      [exact (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
                Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) |].
    intros tr o (Heq & Hx). exists (bufs, code).
    split; [apply HU; reflexivity |].
    split; [unfold outcome_trace; cbn [fst snd]; rewrite <- wevents_ch_fd1; exact Heq |].
    cbn [snd]. exact Hx.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - (* [comment removed for export] *)
    apply exec_step; [exact Hh | | |].
    + destruct (brk_receptive segs ms x8 model Hno) as (eff & model' & Hspec).
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & _ & _ & Hlazy').
      eexists; eexists.
      apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)). reflexivity.
    + intros evs Hss.
      destruct (sstep_brk_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_brk_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy)) |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [| exact Hx].
      cbn [app]. unfold outcome_trace in Heq |- *. rewrite Hfs in Heq. exact Heq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_outcomes_no_other_exit : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R3.R2.R1.)P,(5.(8.(0.&40.))(65.R3.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R4.)(15.(17.(0.&40.)(0.&40.))))Pcode',(0.&40.)P,Po,(17.(<.(<.(0.&8.)))(0.&40.))P,A1.R6.R1.(3;.(5.(0.&40.)(59.(<.(<.(0.&8.)))(0.&40.)R2.)R3.))(3;.(72.Vsegs,(6?.R8.R7.)(74.R2.)))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & Hout & _ & Hx)); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne out Hout Hx').
Qed.

#[using="Type"] Lemma to_outcomes_not_silent : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R3.R2.R1.)P,(5.(8.(0.&40.))(65.R3.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R4.)(15.(17.(0.&40.)(0.&40.))))(3;.(75.Vsegs,(6?.R6.R5.)Ltr,(<.$2?.)(5.(<.$2?.)R1.(15.$2?.))))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy Hc.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & _ & Heq & Hx)); [| destruct Hx].
  destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  subst tr. unfold outcome_trace in Hnil.
  destruct (wevents (fst out)); discriminate Hnil.
Qed.

#[using="Type"] Lemma to_outcomes_star_only : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R3.R2.R1.)P,(5.(8.(0.&40.))(65.R3.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R4.)(15.(17.(0.&40.)(0.&40.))))Ptr,(<.$2?.)Pc,$76.P,(77.Vsegs,(6?.R8.R7.)R2.R1.)(3=.(17.(<.(<.(0.&8.)))(0.&40.))Lo,(17.(<.(<.(0.&8.)))(0.&40.))(11.A1.R8.R1.(78.$2?.R4.(79.(68.R9.)R1.))))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy) Hstar))
    as (tr' & o & _ & (out & Hout & Heq & _)).
  exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma to_outcomes_star_admits : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R3.R2.R1.)P,(5.(8.(0.&40.))(65.R3.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R4.)(15.(17.(0.&40.)(0.&40.))))Po,(17.(<.(<.(0.&8.)))(0.&40.))P,A1.R5.R1.(3=.$76.Lc,$76.(77.Vsegs,(6?.R9.R8.)(79.(68.R8.)R3.)R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - (* [comment removed for export] *)
    apply HU in Ho. subst o.
    unfold outcome_trace; cbn [fst snd].
    rewrite <- wevents_ch_fd1.
    eapply (to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1);
      [exact Hh | exact Hlazy | exact (fd1chan_fdchan model Hfd)
      | exact Hbm | exact Hte].
  - (* [comment removed for export] *)
    destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model) o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - (* [comment removed for export] *)
    apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno Hspec)
      as (Hevs & Hh' & Hfs & _ & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) o Ht)
      as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model') o)
      by (unfold outcome_trace; rewrite Hfs; reflexivity).
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []);
      try assumption.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_outcomes_no_error : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R3.R2.R1.)P,(5.(8.(0.&40.))(65.R3.)(1=.(0.&40.)))P,(5.(<.(17.(0.&40.)(0.&40.)))(6;.R4.)(15.(17.(0.&40.)(0.&40.))))(3;.(7:.Vsegs,(6?.R6.R5.)))")
(* [comment removed for export] *).
Proof.
  intros ms model U Hto Hh Hlazy. apply exec_no_error.
  eapply exec_conseq; [exact (to_outcomes_exec ms model U Hto Hh Hlazy) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma tou_brk_r : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.Px8,(0.&40.)PT',P,(0.&40.)P,(17.(<.(<.(0.&8.)))(0.&40.))SpPU,Px,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(5.(8.(0.&40.))(6=.R5.)(12.(0.&40.)R3.))P,(5.$6.(3.&40.R4.)+=6.)P,Pr,(0.&40.)P,(38.R7.(2>.R8.#0.)R1.)(71.(19.(1:.R9.(1?.R2.(15.(17.(0.&40.)(<.(0.&8.))))(34.(2>.R9.#0.)R2.(35.(36.R8.)))(37.R2.(35.(36.R8.)))(15.$20.)(15.(17.(0.&40.)$>.)))))(39.(2>.R9.#0.)R2.R8.)A1.R6.R2.)P,Po,(17.(<.(<.(0.&8.)))(0.&40.))(2:.A1.R5.R1.(3=.(0.&40.)Lr,(0.&40.)(11.(38.R9.(2>.R:.#0.)R1.)A2.R7.R1.R2.)))(71.R9.R8.R5.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 T' U Hsvc Hno Hcont HU.
  apply (tou_brk ms model x8 (fun eff _ => T' (eff_ret eff)) U);
    [exact Hsvc | exact Hno | |].
  - intros eff model' evs Hspec.
    apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    pose proof (Hcont (eff_ret eff) Hok) as H.
    rewrite <- Heff in H. exact H.
  - intro o. rewrite HU. split.
    + intros (r & Hok & Ht).
      exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                            (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
             (brk_model (ms_gpr ms 0) r model), [].
      split; [apply brk_ok_intro; [exact Hno | exact Hok] | exact Ht].
    + intros (eff & model' & evs & Hspec & Ht).
      apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
      destruct Hspec as (_ & _ & Hok & _).
      exists (eff_ret eff). auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tou_wexit_eq : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.Pbufs,(<.(<.(0.&8.)))Pcode,(0.&40.)P,(7;.R3.)P,(7<.Vsegs,(14.&40.+1.)R3.R2.R5.)P,(7=.R4.)(71.R7.R6.Lo,(17.(<.(<.(0.&8.)))(0.&40.))(5.(17.(<.(<.(0.&8.)))(0.&40.))R1.(41.(<.(<.(0.&8.)))(0.&40.)R6.R5.)))")
(* [comment removed for export] *).
Proof.
  intros ms model bufs code Hfd Hte Hbm.
  apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm | tauto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tou_equiv : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Pms,$18.Pmodel,$27.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpPV,Px,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(71.R4.R3.R2.)P,Po,(17.(<.(<.(0.&8.)))(0.&40.))(2:.A1.R3.R1.A1.R4.R1.)(71.R6.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros V HV.
  - apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm |].
    intro o. rewrite (HV o). apply HU.
  - eapply tou_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tou_brk ms model x8 T V); [exact Hsvc | exact Hno | |].
    + intros eff model' evs Hspec. exact (Hcont eff model' evs Hspec).
    + intro o. rewrite (HV o). apply HU.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_omni_run : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Ppc,$7>.Pph,$7?.Psp,(0.&40.)Pbrk0,(0.&40.)Pmb,(0.&40.)Prnd,$80.Plim,$6.Pinp,$81.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(82.R:.(83.R:.R9.R8.R7.R4.(84.R2.)(85.R2.)(86.R2.)(87.R2.))(88.(89.R:.)R6.R5.R7.R3.R2.)R1.)(8:.(8;.R;.R:.R9.)R4.(8<.R8.R7.R6.R5.)R3.(8=.(8>.R3.)R2.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  cbn [omni_run]. unfold init_config.
  exact (to_outcomes_exec segs _ _ U Hto eq_refl eq_refl).
Qed.

#[using="Type"] Lemma alloc_obs_iff : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Ppc,$7>.Pph,$7?.Psp,(0.&40.)Pbrk0,(0.&40.)Pmb,(0.&40.)Prnd,$80.Plim,$6.Pinp,$81.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(82.R:.(83.R:.R9.R8.R7.R4.(84.R2.)(85.R2.)(86.R2.)(87.R2.))(88.(89.R:.)R6.R5.R7.R3.R2.)R1.)Ptr,(<.$2?.)(2:.(8?.R<.(90.R<.R;.R:.R9.R8.R7.R6.R5.R4.)R1.)(3=.(17.(<.(<.(0.&8.)))(0.&40.))Lo,(17.(<.(<.(0.&8.)))(0.&40.))(11.A1.R4.R1.(78.$2?.R2.(91.(8>.R5.)R1.)))))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
    by reflexivity.
  assert (Hlazy : m_vm_lazy
      (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
  assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp)
    by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_outcomes_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
      as (o & Ho & Hp').
    exists o. split; [exact Ho|].
    rewrite Hfs in Hp'. eapply is_prefix_trans; eauto.
  - intros (o & Ho & Hp).
    destruct (to_outcomes_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    rewrite Hfs in Hstar.
    exists (outcome_trace (in_fs inp) o), c. split; assumption.
Qed.

#[using="Type"] Lemma alloc_no_error_run : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psegs,(<.$=.)Ppc,$7>.Pph,$7?.Psp,(0.&40.)Pbrk0,(0.&40.)Pmb,(0.&40.)Prnd,$80.Plim,$6.Pinp,$81.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpP,(82.R:.(83.R:.R9.R8.R7.R4.(84.R2.)(85.R2.)(86.R2.)(87.R2.))(88.(89.R:.)R6.R5.R7.R3.R2.)R1.)(3;.(7:.R;.(90.R;.R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
  eapply exec_conseq; [exact (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psource_segs,(<.$=.)Prpc,$7>.Prph,$7?.Prsp,(0.&40.)Prbrk,(0.&40.)Prmb,(0.&40.)Prrnd,$80.Ptarget_segs,(<.$=.)Papc,$7>.Paph,$7?.Pasp,(0.&40.)Pabrk,(0.&40.)Pamb,(0.&40.)Parnd,$80.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpPinp,$81.P,(82.R10.(83.R10.R?.R>.R=.R:.(84.R1.)(85.R1.)(86.R1.)(87.R1.))(88.(89.R10.)R<.R;.R=.$92.R1.)R2.)P,(82.R:.(83.R:.R9.R8.R7.R4.(84.R2.)(85.R2.)(86.R2.)(87.R2.))(88.(89.R:.)R6.R5.R7.$93.R2.)R3.)(94.(8;.R12.R11.R10.)(8;.R;.R:.R9.)(8<.R?.R>.R=.R<.)(8<.R8.R7.R6.R5.)R3.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_AllocSim ()) "Psource_segs,(<.$=.)Prpc,$7>.Prph,$7?.Prsp,(0.&40.)Prbrk,(0.&40.)Prmb,(0.&40.)Prrnd,$80.Prlim,$6.Ptarget_segs,(<.$=.)Papc,$7>.Paph,$7?.Pasp,(0.&40.)Pabrk,(0.&40.)Pamb,(0.&40.)Parnd,$80.Palim,$6.PU,P,(17.(<.(<.(0.&8.)))(0.&40.))SpPinp,$81.P,(82.R12.(83.R12.R11.R10.R?.R<.(84.R1.)(85.R1.)(86.R1.)(87.R1.))(88.(89.R12.)R>.R=.R?.R;.R1.)R2.)P,(82.R;.(83.R;.R:.R9.R8.R5.(84.R2.)(85.R2.)(86.R2.)(87.R2.))(88.(89.R;.)R7.R6.R8.R4.R2.)R3.)(11.(95.(96.(8;.R14.R13.R12.)R=.(8<.R11.R10.R?.R>.)R3.))(97.(96.(8;.R14.R13.R12.)R=.(8<.R11.R10.R?.R>.)R3.)(96.(8;.R<.R;.R:.)R5.(8<.R9.R8.R7.R6.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
    reflexivity.
  - cbn. apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
End WithFP1.
