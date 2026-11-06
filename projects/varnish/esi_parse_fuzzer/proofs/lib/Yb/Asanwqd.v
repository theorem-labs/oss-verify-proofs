(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Ltac acfg_if_split H :=
  repeat (match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end).

Module Agenxn8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require ShapeAlg Nodes StoreOk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Stredvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;  (* [comment removed for export] *)
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_set. Qed.

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
End Agenxn8.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.

Module Speco6o.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End Speco6o.

Module RefNodes.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.  (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Stredvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Agenxn8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Speco6o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Lemma acfg_iff_guard : forall i m (ERRS : list Z) (G : SyscallEffect -> check_result),
  injected_family_off ACFG i = true ->
  (forall eff, refusal_b i m (eff_ret eff) = errno_ret_in ERRS (eff_ret eff)) ->
  (forall eff, errno_ret_in ERRS (eff_ret eff) = false -> check_syscall i eff m = G eff) ->
  (forall eff m' evs, errno_ret_in ERRS (eff_ret eff) = true ->
     check_syscall i eff m = CheckOk m' evs -> m_halted m' = None) ->
  (forall eff m' evs, G eff = CheckOk m' evs -> errno_ret_in ERRS (eff_ret eff) = false) ->
  (exists eff m' evs, G eff = CheckOk m' evs) ->
  forall eff m' evs, syscall_spec_acfg i m (Ok eff m' evs) <-> G eff = CheckOk m' evs.
Proof.
  intros i m ERRS G Hoff Href Hchk Hrh Hge Hex eff m' evs. split.
  - intros [Hs Hok]. cbn [spec_step_ok] in Hok. apply check_syscall_ok_iff in Hs.
    destruct (errno_ret_in ERRS (eff_ret eff)) eqn:Er.
    + exfalso. destruct Hex as (eff' & m'' & evs' & Hg).
      apply (Hok (Hrh _ _ _ Er Hs)). split; [exact Hoff|]. split; [rewrite Href; exact Er|].
      exists eff', m'', evs'. split.
      * apply check_syscall_ok_iff. rewrite (Hchk _ (Hge _ _ _ Hg)). exact Hg.
      * rewrite Href. exact (Hge _ _ _ Hg).
    + rewrite <- (Hchk _ Er). exact Hs.
  - intros Hg. apply syscall_spec_acfg_nonrefusal.
    + apply check_syscall_ok_iff. rewrite (Hchk _ (Hge _ _ _ Hg)). exact Hg.
    + rewrite Href. exact (Hge _ _ _ Hg).
Qed.

Lemma acfg_off_214 : forall segs ms x8, bv_unsigned x8 = 214%Z ->
  injected_family_off ACFG (sys_input segs ms x8) = true.
Proof.
  intros segs ms x8 Hno. apply (acfg_family_off_no (sys_input segs ms x8) 214%Z Hno).
  cbn [alloc_mark_sysnos In]. left; reflexivity.
Qed.

Lemma acfg_off_222 : forall segs ms x8, bv_unsigned x8 = 222%Z ->
  injected_family_off ACFG (sys_input segs ms x8) = true.
Proof.
  intros segs ms x8 Hno. apply (acfg_family_off_no (sys_input segs ms x8) 222%Z Hno).
  cbn [alloc_mark_sysnos In]. right; right; left; reflexivity.
Qed.

Lemma acfg_off_226 : forall segs ms x8, bv_unsigned x8 = 226%Z ->
  injected_family_off ACFG (sys_input segs ms x8) = true.
Proof.
  intros segs ms x8 Hno. apply (acfg_family_off_no (sys_input segs ms x8) 226%Z Hno).
  cbn [alloc_mark_sysnos In]. right; right; right; left; reflexivity.
Qed.

Lemma errno_mm_aligned : forall r, (bv_unsigned r mod page_size = 0)%Z -> errno_ret_in [ENOMEM] r = false.
Proof. intros r H. exact (ret_in_errnos_ENOMEM_aligned r H). Qed.

Section WithSegs.
Variable segs : list Segment.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)

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
  cbn [app maps_subtract_ranges fold_left].
  replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
  apply bv_eq. rewrite bv_sub_unsigned, Hureq.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

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
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_ceiling)%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && hint_placement_ok_b hint (m_vmmaps m) (bv_unsigned a) n.

(* [comment removed for export] *)
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grant_ok_na_pin_of_gate : forall hint m a n,
  init_sp_ok (m_vmmaps m) -> grant_ok_na hint m a n = true -> grant_ok_na_pin m a n = true.
Proof.
  intros hint m a n Hisp H. unfold grant_ok_na in H. unfold grant_ok_na_pin.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Hce].
  apply andb_true_iff in H as [Hal Hpos].
  assert (Htop : (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z)
    by (apply (alloc_top_ge_of_ceiling _ _ Hisp); apply Z.leb_le; exact Hce).
  rewrite Hal, Hpos, Hrf, (proj2 (Z.leb_le _ _) Htop). reflexivity.
Qed.

(* [comment removed for export] *)

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)

Lemma check_syscall_226 : forall ms x8 eff m,
  bv_unsigned x8 = 226%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma mprotect_check_rel : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
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
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
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
  cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end); reflexivity].
  destruct cs; [| try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end); reflexivity].
  destruct ci; [| try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end); reflexivity].
  reflexivity.
Qed.

Lemma mprotect_check : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  m_halted model = None ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall eff m' evs,
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)
  <-> match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in (mprotect_errnos_when (mprotect_refusable model addr n)) r   (* [comment removed for export] *)
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end = CheckOk m' evs.
Proof.
  intros ms x8 model addr len Hno Hh H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  pose proof (fun eff => mprotect_check_rel ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hrel.
  cbv zeta in Hrel. fold n in Hrel.
  destruct (mprotect_refusable model addr n) eqn:Ef.
  - intros eff m' evs. split.
    + intros [Hs _]. apply check_syscall_ok_iff in Hs. rewrite Hrel in Hs. exact Hs.
    + intros Hf. apply syscall_spec_acfg_forced.
      * apply check_syscall_ok_iff. rewrite Hrel. exact Hf.
      * intros eff' m'' evs' Hs'. apply check_syscall_ok_iff in Hs'. rewrite Hrel in Hs'.
        rewrite (refusal_b_226 (sys_input segs ms x8) model _ Hno).
        unfold mprotect_refusable in Ef. apply negb_true_iff in Ef.
        destruct eff' as [r ws zs us cs ci]. cbn [eff_ret] in Hs' |- *.
        destruct ws; [|discriminate Hs']. destruct us; [|discriminate Hs'].
        destruct cs; [|discriminate Hs']. destruct ci; [|discriminate Hs'].
        destruct (errno_ret_in mprotect_errnos r) eqn:Er; [exact Er|].
        rewrite Ef in Hs'. discriminate Hs'.
  - apply (acfg_iff_guard (sys_input segs ms x8) model mprotect_errnos
             (fun eff => match eff with
                | mkEffectU r [] zs [] [] [] =>
                    if errno_ret_in (mprotect_errnos_when false) r
                    then match zs with [] => CheckOk model [] | _ => CheckReject end
                    else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
                         then CheckOk (mprotect_model addr n model) []
                         else CheckReject
                | _ => CheckReject
                end)).
    + exact (acfg_off_226 segs ms x8 Hno).
    + intros eff. rewrite (refusal_b_226 (sys_input segs ms x8) model _ Hno). reflexivity.
    + intros [r ws zs us cs ci] Er. rewrite Hrel. cbn [eff_ret] in Er |- *.
      destruct ws, us, cs, ci; cbv beta iota; try reflexivity. rewrite Er. reflexivity.
    + intros eff m' evs Er Hc. rewrite Hrel in Hc. destruct eff as [r ws zs us cs ci].
      cbn [eff_ret] in Er, Hc.
      destruct ws, us, cs, ci; cbv beta iota in Hc; try discriminate Hc.
      rewrite Er in Hc. cbv beta iota in Hc.
      destruct zs; [|discriminate Hc]. injection Hc as <- <-. exact Hh.
    + intros eff m' evs Hg. destruct eff as [r ws zs us cs ci]. cbn [eff_ret]. cbv beta iota in Hg.
      destruct ws, us, cs, ci; cbv beta iota in Hg; try discriminate Hg.
      cbn [mprotect_errnos_when errno_ret_in existsb] in Hg.
      destruct (w_is0 r) eqn:Ez; [|destruct (mprotect_budget_ok model addr n); discriminate Hg].
      unfold w_is0 in Ez. apply bv_eqb_eq in Ez. subst r. vm_compute. reflexivity.
    + unfold mprotect_refusable in Ef. apply negb_false_iff in Ef.
      exists (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []), (mprotect_model addr n model), [].
      cbv beta iota. unfold w_is0. rewrite Ef, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

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
End RefNodes.


Module NoRey4t.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec CatSim MmapSim ShapeAlg Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SpinAlg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.SymTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

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

Section WithSegs.
Variable segs : list Segment.

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
Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

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
Hypothesis Hwalk1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  msteps_acc segs (post1 a1) (ms2 a1) (accs1 a1).
Hypothesis Hout1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  accesses_outside_lazy (accs1 a1) (m_vm_lazy (model1 a1)).

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
Hypothesis Hrefuse2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 (ms2 a1) (errno_ret e))) (model1 a1).
Hypothesis Hex2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  exists a2, grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true.

(* [comment removed for export] *)
Variable ms3 : word -> word -> machine_state.
Variable accs2 : word -> word -> list (word * nat).
Hypothesis Hwalk2 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  msteps_acc segs (post2 a1 a2) (ms3 a1 a2) (accs2 a1 a2).
Hypothesis Hout2 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  accesses_outside_lazy (accs2 a1 a2) (m_vm_lazy (model2 a1 a2)).

(* [comment removed for export] *)
Variable buf : list byte.
Hypothesis Hbufnb : (1 <= length buf)%nat.
Hypothesis Hbufmod : buf_modeled buf.
Variable x8c : word.
Hypothesis Hno3 : bv_unsigned x8c = 64%Z.
Hypothesis Hw_svc : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_svc_pending (ms3 a1 a2) = Some x8c.
Hypothesis Hw_fd1 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_gpr (ms3 a1 a2) 0 = Z_to_bv 64 1.
Hypothesis Hw_read : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_read_bytes (ms3 a1 a2) (ms_gpr (ms3 a1 a2) 1) (ms_gpr (ms3 a1 a2) 2) = Some buf.
Hypothesis Hw_out : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  accesses_outside_lazy [(ms_gpr (ms3 a1 a2) 1, length buf)]
    (m_vm_lazy (model2 a1 a2)).

(* [comment removed for export] *)
Variable msE : word -> word -> nat -> machine_state.
Variable accs3 : word -> word -> nat -> list (word * nat).
Hypothesis Hwalk3 : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  msteps_acc segs
    (advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (firstn n buf))))
    (msE a1 a2 n) (accs3 a1 a2 n).
Hypothesis Hout3 : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  accesses_outside_lazy (accs3 a1 a2 n) (m_vm_lazy (model2 a1 a2)).

(* [comment removed for export] *)
Variables (x8d : word) (cs : word).
Hypothesis HE_no : is_exit_no x8d.
Hypothesis HE_svc : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  ms_svc_pending (msE a1 a2 n) = Some x8d.
Hypothesis HE_code : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  bv_and (ms_gpr (msE a1 a2 n) 0) (Z_to_bv 64 255) = cs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End AsanInitReal.
End WithFP2.
End NoRey4t.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Agenxn8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asancq9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Back4sr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.NoRey4t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanz3l AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.

Module Asanrb8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require ShapeAlg SpinAlg Nodes StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Stredvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Agenxn8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asancq9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Back4sr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanz3l AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs) ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep_cfg segs ACFG (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hacc.
  apply (sstep_cfg_syscall_acfg segs ms model x8 eff m' m' evs Hh Hsvc Hc Hh').
  rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec_acfg (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall eff m' ev, syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc. split.
  - intros i. apply (sstep_of_check_noacc ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + (first [ pose proof ((Hinv _ _ _ Hc)) as dR_1; dex1 dR_1 as i; dand3 dR_1 as -> -> -> | pose proof ((Hinv _ _ _ Hc)) as dR_1; dand4 dR_1 as i -> -> -> | destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->) ]).
      rewrite (Hacc i), materialize_model_accesses_nil in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + (first [ pose proof ((Hinv _ _ _ Hc)) as dR_2; dex1 dR_2 as i; dand3 dR_2 as -> -> -> | pose proof ((Hinv _ _ _ Hc)) as dR_2; dand4 dR_2 as i -> -> -> | destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->) ]).
      rewrite (Hacc i), materialize_model_accesses_nil in Hmat. discriminate.
    + (first [ pose proof ((Hinv _ _ _ Hc)) as dR_3; dex1 dR_3 as i; dand3 dR_3 as -> -> -> | pose proof ((Hinv _ _ _ Hc)) as dR_3; dand4 dR_3 as i -> -> -> | destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->) ]). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec_acfg (sys_input segs ms x8) model (Ok (effs i) (ms' i) [])) ->
  (forall eff m' evs, syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hacc.
  assert (Hdet : forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0).
  { intros [eff m' evs|]; split.
    - intros Hs. apply check_syscall_ok_iff in Hs. apply Hchk in Hs as (-> & -> & ->). reflexivity.
    - intros He. injection He as -> -> ->. apply check_syscall_ok_iff. apply Hchk. auto.
    - intros Hs. exfalso. apply (Hnu eff0). apply check_syscall_err_iff. exact Hs.
    - intros He. discriminate He. }
  pose proof (syscall_spec_acfg_det _ _ _ _ _ Hdet) as Hacfg.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply Hacfg. reflexivity.
  - intros eff m' ev Hc. apply Hacfg in Hc. injection Hc as -> -> ->. exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hacc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) (T i)) ->
  srealizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
  intros. unfold brk_model, with_brk_next. cbv zeta.
  rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_cfg_instr segs ACFG ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->  (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
  rewrite H0, Hpr in Hchk.
  eapply (srz_det_noacc ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
    [exact Hh | reflexivity | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + ((first [ intro dR_6; dand3 dR_6 as -> -> -> | intros (-> & -> & ->) ])). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - rewrite munmap_model_halted. exact Hh.
  - unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

Definition brk_res_acfg (m : Model) (req r : word) : Prop :=
  brk_resolution_ok m req r
  /\ (brk_refusal_b m req r = true ->
      forall r', brk_resolution_ok m req r' -> brk_refusal_b m req r' = true).

Lemma refusal_b_brk : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_214 (sys_input segs ms x8) model r Hno). reflexivity. Qed.

Lemma brk_acfg_iff : forall ms x8 model eff model' evs,
  m_halted model = None ->
  bv_unsigned x8 = 214%Z ->
  (syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs) <->
   (eff = mkEffectU (eff_ret eff) []
            (brk_zeros (ms_gpr ms 0) (eff_ret eff) (vm_brk (m_vmmaps model)))
            (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model))) [] []
    /\ evs = []
    /\ brk_res_acfg model (ms_gpr ms 0) (eff_ret eff)
    /\ model' = brk_model (ms_gpr ms 0) (eff_ret eff) model)).
Proof.
  intros ms x8 model eff model' evs Hh Hno. split.
  - intros [Hs Hok]. cbn [spec_step_ok] in Hok.
    apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs. destruct Hs as (He & -> & Hr & ->).
    assert (Hh' : m_halted (brk_model (ms_gpr ms 0) (eff_ret eff) model) = None)
      by (rewrite brk_model_halted; exact Hh).
    split; [exact He|]. split; [reflexivity|]. split; [| reflexivity]. split; [exact Hr|].
    intros Hrb r' Hr'. destruct (brk_refusal_b model (ms_gpr ms 0) r') eqn:E; [reflexivity|]. exfalso.
    apply (Hok Hh'). split; [exact (acfg_off_214 segs ms x8 Hno)|].
    split; [rewrite (refusal_b_brk ms x8 model _ Hno); exact Hrb|].
    exists (mkEffectU r' [] (brk_zeros (ms_gpr ms 0) r' (vm_brk (m_vmmaps model)))
                         (brk_unmaps r' (vm_brk (m_vmmaps model))) [] []),
           (brk_model (ms_gpr ms 0) r' model), [].
    split; [exact (brk_ok_intro segs ms x8 model r' Hno Hr')|].
    rewrite (refusal_b_brk ms x8 model _ Hno). cbn [eff_ret]. exact E.
  - intros (He & -> & [Hr Hf] & ->). split.
    + apply (brk_ok_iff segs ms x8 model eff _ [] Hno). auto.
    + cbn [spec_step_ok]. intros _. destruct (brk_refusal_b model (ms_gpr ms 0) (eff_ret eff)) eqn:E.
      * intros (_ & _ & (eff' & m' & evs' & Hs' & Hnr)). rewrite (refusal_b_brk ms x8 model _ Hno) in Hnr.
        apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hs'. destruct Hs' as (_ & _ & Hr' & _).
        rewrite (Hf eq_refl _ Hr') in Hnr. discriminate Hnr.
      * apply spurious_refusal_not_refusal. rewrite (refusal_b_brk ms x8 model _ Hno). exact E.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_res_acfg model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_noacc ms model x8 {r : word | brk_res_acfg model (ms_gpr ms 0) r}
           (fun i => mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros [r Hr]. cbn [proj1_sig]. apply (brk_acfg_iff ms x8 model _ _ _ Hh Hno). cbn [eff_ret]. auto.
  - intros eff m' evs Hc.
    apply (brk_acfg_iff ms x8 model eff m' evs Hh Hno) in Hc as (Heff & -> & Hok & ->).
    exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros [r Hr]. cbn [proj1_sig]. rewrite brk_model_halted. exact Hh.
  - intros [r Hr]. reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases0 : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hnr : forall r, brk_refusal_b model (ms_gpr ms 0) r = false).
  { intros r. unfold brk_refusal_b. rewrite H0. unfold w_is0. rewrite bv_eqb_refl. reflexivity. }
  assert (Hcases : forall r, brk_res_acfg model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. split.
    - intros [Hr _]. apply Hcases0. exact Hr.
    - intros ->. split; [apply Hcases0; reflexivity|]. intros Hrb. rewrite Hnr in Hrb. discriminate Hrb. }
  assert (Hq : brk_res_acfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hq) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  (forall tr, KA tr -> KB tr) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB).
Proof.
  intros regs pc mem rom model w d KA KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB Hsub.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  assert (Hrb_req : brk_refusal_b model (ms_gpr ms 0) req = false).
  { unfold brk_refusal_b. rewrite H0. cbv zeta. fold h. fold b.
    rewrite (bv_eqb_neq _ _ Hneq). rewrite andb_false_r. reflexivity. }
  assert (Hrb_b : brk_refusal_b model (ms_gpr ms 0) b = true).
  { unfold brk_refusal_b. rewrite H0. cbv zeta. unfold Mmap.min_brk. fold h. fold b.
    assert (E0 : w_is0 req = false) by (unfold w_is0; apply bv_eqb_neq; exact Hreq0).
    rewrite E0. rewrite (proj2 (Z.ltb_ge _ _)) by (rewrite Hureq; lia).
    rewrite (bv_eqb_neq _ _ Hneq), bv_eqb_refl. reflexivity. }
  assert (Hcases' : forall r, brk_res_acfg model (ms_gpr ms 0) r <-> r = req).
  { intros r. split.
    - intros [Hr Hf]. destruct (proj1 (Hcases r) Hr) as [-> | [-> _]]; [|reflexivity]. exfalso.
      pose proof (Hf Hrb_b req Hgrow) as X. rewrite Hrb_req in X. discriminate X.
    - intros ->. split; [exact Hgrow|]. intros X. rewrite Hrb_req in X. discriminate X. }
  assert (Hg' : brk_res_acfg model (ms_gpr ms 0) req) by (apply Hcases'; reflexivity).
  apply (srz_conseq segs _ KB).
  2:{ intros tr. unfold t_alt2. split; [intros Ht; right; exact Ht | intros [Ht | Ht]; [exact (Hsub tr Ht) | exact Ht]]. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => KB)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hg'); exact Ht]].
  eapply srz_cases; [exact (exist _ req Hg') | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases' r) Hr) as Er. subst r.
  - assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases0 : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hcases : forall r, brk_res_acfg model (ms_gpr ms 0) r <-> r = b).
  { intros r. split.
    - intros [Hr _]. apply Hcases0. exact Hr.
    - intros ->. split; [apply Hcases0; reflexivity|].
      intros Hrb r' Hr'. rewrite (proj1 (Hcases0 r') Hr'). exact Hrb. }
  assert (Hkeep : brk_res_acfg model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_acfg model (ms_gpr ms 0) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  assert (Hna : alloc_no_b (bv_unsigned x8) = false) by (rewrite Hno; reflexivity).
  apply (node_chk_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
  - intros [t [Ht1 Ht2]]. cbn [proj1_sig].
    apply (acfg_si_nonalloc segs ms x8 model _ Hna). apply check_syscall_ok_iff. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - intros [ret ws zs us cs ci] m' ev Hc. apply (acfg_si_nonalloc segs ms x8 model _ Hna) in Hc.
    apply check_syscall_ok_iff in Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
  - intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
  - intros [t Ht]. reflexivity.
Qed.

Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_alt2b : forall c (nx : bool -> config) (A B : TSet),
  node_ok segs c bool (fun _ => []) nx ->
  srealizes segs (nx true) A -> srealizes segs (nx false) B ->
  srealizes segs c (t_alt2 A B).
Proof.
  intros c nx A B Hnode HA HB.
  apply (srz_conseq segs c (t_alt (fun i : bool => if i then A else B))).
  - apply (srz_cases c bool nx _ true Hnode). intros [|]; assumption.
  - intros tr. unfold t_alt2, t_alt. split.
    + intros [[|] H]; tauto.
    + intros [H | H]; [exists true | exists false]; exact H.
Qed.

(* [comment removed for export] *)
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
(* [comment removed for export] *)

Lemma mmap_fixedin_check_rel : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with
             | [] => match us with
                     | [] => CheckOk model []
                     | _ => if listNN_eqb us [(addr, n)]
                            then CheckOk (with_mmap_destroyed addr n
                                            (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []
                            else CheckReject
                     end
             | _ => CheckReject
             end
        else if (Z.eqb prot 0)
        then match zs with
             | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                     then CheckOk (fixedin_ok_model prot flags addr n model) []
                     else CheckReject
             | _ => CheckReject
             end
        else match us with
             | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                     then CheckOk (fixedin_ok_model prot flags addr n model) []
                     else CheckReject
             | _ => CheckReject
             end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold two_pow_64, stack_max_size in Hcv.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [destruct zs; reflexivity|].
    destruct zs; [|reflexivity].
    cbn [andb].
    reflexivity.
  - (* [comment removed for export] *)
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [destruct zs; reflexivity|].
    cbn [andb].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixedin_check : forall ms x8 model (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  m_halted model = None ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  forall eff m' evs,
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)
  <-> match eff with
    | mkEffectU r [] zs us [] [] =>
        if (Z.eqb prot 0)
        then match zs with
             | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                     then CheckOk (fixedin_ok_model prot flags addr n model) []
                     else CheckReject
             | _ => CheckReject
             end
        else match us with
             | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                     then CheckOk (fixedin_ok_model prot flags addr n model) []
                     else CheckReject
             | _ => CheckReject
             end
    | _ => CheckReject
    end = CheckOk m' evs.
Proof.
  intros ms x8 model prot flags addr len Hno Hh Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
  pose proof (fun eff => mmap_fixedin_check_rel ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos
                           H1 Hlen H2 H3 H4 H5 Hce Hrf Hmc Hbud) as Hrel.
  cbv zeta in Hrel. fold n in Hrel.
  apply (acfg_iff_guard (sys_input segs ms x8) model mmap_errnos
           (fun eff => match eff with
              | mkEffectU r [] zs us [] [] =>
                  if (Z.eqb prot 0)
                  then match zs with
                       | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                               then CheckOk (fixedin_ok_model prot flags addr n model) []
                               else CheckReject
                       | _ => CheckReject
                       end
                  else match us with
                       | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                               then CheckOk (fixedin_ok_model prot flags addr n model) []
                               else CheckReject
                       | _ => CheckReject
                       end
              | _ => CheckReject
              end)).
  - exact (acfg_off_222 segs ms x8 Hno).
  - intros eff. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity.
  - intros [r ws zs us cs ci] Er. rewrite Hrel. cbn [eff_ret] in Er |- *.
    destruct ws, zs, us, cs, ci; cbv beta iota; try reflexivity; rewrite Er; reflexivity.
  - intros eff m' evs Er Hc. rewrite Hrel in Hc. destruct eff as [r ws zs us cs ci].
    cbn [eff_ret] in Er, Hc.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hc; try discriminate Hc;
      rewrite Er in Hc; cbv beta iota in Hc; acfg_if_split Hc; try discriminate Hc;
      injection Hc as <- <-;
      first [exact Hh | unfold with_mmap_destroyed; rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh].
  - intros eff m' evs Hg. destruct eff as [r ws zs us cs ci]. cbn [eff_ret]. cbv beta iota in Hg.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hg; try discriminate Hg;
      destruct (bv_eqb r addr) eqn:Eb; try (destruct (Z.eqb prot 0); discriminate Hg);
      apply bv_eqb_eq in Eb; subst r; exact (errno_mm_aligned addr Hal).
  - exists (fixedin_ok_eff prot addr n), (fixedin_ok_model prot flags addr n model), [].
    unfold fixedin_ok_eff. destruct Hprot as [-> | ->]; cbn [Z.eqb]; cbv beta iota;
      rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) (KB : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Har.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  assert (R0 : ms_gpr ms 0 = addr) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (R1 : ms_gpr ms 1 = Z_to_bv 64 len) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (R2 : ms_gpr ms 2 = Z_to_bv 64 prot) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  assert (R3 : ms_gpr ms 3 = flags) by (unfold ms; rewrite ms_gpr_epend3; exact H13).
  assert (R4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by (unfold ms; rewrite ms_gpr_epend4; exact H14).
  assert (R5 : ms_gpr ms 5 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend5; exact H15).
  pose proof (mmap_fixedin_check ms (getr regs 17) model prot flags addr len Hno Hh Hprot Hcore
                R0 Hal Hpos R1 Hlen R2 R3 R4 R5 Hce Hrf Hmc Hbud) as Hchk.
  pose proof (fun eff => mmap_fixedin_check_rel ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                R0 Hal Hpos R1 Hlen R2 R3 R4 R5 Hce Hrf Hmc Hbud) as Hrel.
  cbv zeta in Hchk. fold n in Hchk. cbv zeta in Hrel. fold n in Hrel.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n))) (fixedin_ok_model prot flags addr n model))).
  - apply (node_chk_noacc ms model (getr regs 17) unit (fun _ => fixedin_ok_eff prot addr n)
             (fun _ => fixedin_ok_model prot flags addr n model) Hh eq_refl).
    + intros []. cbv beta. apply Hchk.
      unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; cbv beta iota;
        rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. apply Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (Z.eqb prot 0) eqn:Ep.
      * destruct zs; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
        exists tt. unfold fixedin_ok_eff. rewrite Ep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
      * destruct us; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
        exists tt. unfold fixedin_ok_eff. rewrite Ep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros [r [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]] Hc; rewrite Hrel in Hc; cbv beta iota in Hc;
        acfg_if_split Hc; discriminate Hc.
    + intros []. unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
    + intros []. unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity.
  - unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2 AX2S AP APS.

(* [comment removed for export] *)
Lemma is_ecall_at_sound : forall SEGS cs,
  is_ecall_at SEGS cs = true ->
  0 <= pc cs /\ pc cs + 4 < two64 /\
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
  v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End CsOk.
End Asanrb8.

  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac chkp_cleanup :=
  repeat
    (repeat match goal with
       | [ H : (0 <= ?x < _)%Z |- _ ] =>
          destruct H;
          try (lazymatch type of H with (* [comment removed for export] *)
            | (0 <= x < _)%Z => clear H (* [comment removed for export] *)
          end)
          (* [comment removed for export] *)
       end;
     repeat match goal with
       | [ H : (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
       | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
       | [ H : ?A -> (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
       | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       end;
     repeat match goal with
       | [ H : ?x = ?x -> ?Q |- _ ] => specialize (H eq_refl)
       | [ H : ?T -> ?Q, H' : ?T |- _ ] => specialize (H H')
       | [ H : ?A -> ?x = ?x -> ?Q |- _ ] => specialize (fun a => H a eq_refl)
       | [ H : ?A -> ?B -> ?Q, H' : ?B |- _ ] => specialize (fun a => H a H')
       | [ H : (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : ?A -> (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
       | [ H : ?A -> (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
       end).
Local Ltac nia := Zify.zify; chkp_cleanup; xnia zchecker.
Local Ltac liac := Zify.zify; chkp_cleanup; xlia zchecker.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RES_hull_def (SEGS : list Segment) (A : AP.atable) : Prop :=
  Forall (fun iv : word * word => img_lo A <= bv_unsigned (fst iv)
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
         (segments_reserved SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_covered : forall z l, in_ivs z l = covered l z.
Proof.
  intros z l. unfold in_ivs, covered, in_iv, in_rng, B, S. reflexivity.
Qed.

Lemma in_ivs_cons : forall z iv l,
  in_ivs z (iv :: l) = (((bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv))) || in_ivs z l)%bool.
Proof. reflexivity. Qed.

Lemma in_ivs_app : forall z l1 l2, in_ivs z (l1 ++ l2) = (in_ivs z l1 || in_ivs z l2)%bool.
Proof. intros. unfold in_ivs. apply existsb_app. Qed.

Lemma in_ivs_true' : forall z l, in_ivs z l = true <-> exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_ivs_false : forall z l,
  in_ivs z l = false <-> forall iv, In iv l -> ~ (bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Proof.
  intros z l. split.
  - intros H iv Hin Hz. assert (T : in_ivs z l = true) by (apply (proj2 (in_ivs_true' z l)); eauto). congruence.
  - intros H. destruct (in_ivs z l) eqn:E; [|reflexivity]. exfalso.
    apply in_ivs_true' in E as [iv [Hin Hz]]. exact (H iv Hin Hz).
Qed.

Lemma sum_sizes_live : forall l, sum_sizes l = live_bytes l.
Proof. induction l as [|[a s] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof. intros. rewrite !sum_sizes_live. apply live_bytes_app. Qed.

(* [comment removed for export] *)
Lemma region_free_sem : forall l (lo n : word) z,
  region_free l lo n = true -> 0 < bv_unsigned n ->
  bv_unsigned lo <= z < bv_unsigned lo + bv_unsigned n -> in_ivs z l = false.
Proof.
  intros l lo n z Hrf Hn Hz. apply (proj2 (in_ivs_false z l)). intros [b s] Hin Hin2. cbn [fst snd] in Hin2.
  pose proof (region_free_In l lo n b s Hrf Hin) as Hov. lia.
Qed.

Lemma region_free_app : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n)%bool.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_contains_intro : forall l (lo n : word) b s,
  In (b, s) l -> bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s ->
  map_contains l lo n = true.
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_intro : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_used_sem : forall m,
  model_ivs_wf m ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Lemma mat_pages_le_A_bytes : forall A m,
  MInv A m -> A_wf A -> Z.of_nat (length (m_vm_materialized m)) * page_size <= A_bytes A.
Proof.
  intros A m [N1 N2 N3 N4 N5] Hwf. apply allowed_pages_bound; assumption.
Qed.

Lemma vm_backing_used_le : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= eager_used m + A_bytes A.
Proof.
  intros A m HM Hwf. rewrite vm_backing_used_split. pose proof (mat_pages_le_A_bytes A m HM Hwf). lia.
Qed.

Lemma vm_backing_used_limit : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros A m HM Hwf. pose proof (vm_backing_used_le A m HM Hwf). pose proof (minv_budget _ _ HM). lia.
Qed.

(* [comment removed for export] *)
Lemma sum_count_negb_covered_mono : forall C C' l,
  (forall x, covered C x = true -> covered C' x = true) ->
  sum_count (fun x => negb (covered C' x)) l <= sum_count (fun x => negb (covered C x)) l.
Proof.
  intros C C' l H. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  destruct (covered C x) eqn:E; [|reflexivity]. rewrite (H x E) in Hx. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_pieces : forall a sz lo hi q,
  iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) ->
  bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz
  /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma maps_subtract_pieces : forall l lo hi q,
  ivs_wf l -> In q (maps_subtract l lo hi) ->
  exists r, In r l /\ bv_unsigned (fst r) <= bv_unsigned (fst q)
            /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst r) + bv_unsigned (snd r)
            /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
  - (first [ pose proof ((IH lo hi q Hl Hin)) as dR_1; dex1 dR_1 as r; destruct dR_1 as [Hr H] | pose proof ((IH lo hi q Hl Hin)) as dR_1; dand3 dR_1 as r Hr H | destruct (IH lo hi q Hl Hin) as (r & Hr & H) ]). exists r. split; [right; exact Hr | exact H].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) lo hi,
  lo < hi -> 0 < bv_unsigned sz -> (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keeps : forall l (b s : word) lo hi,
  lo < hi -> 0 < bv_unsigned s -> In (b, s) l ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b) ->
  In (b, s) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi Hlh Hs Hin Hd; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. rewrite (iv_subtract_disjoint b s lo hi Hlh Hs Hd). left. reflexivity.
  - right. apply IH; assumption.
Qed.

(* [comment removed for export] *)

Lemma page_in_ranges_cons : forall p iv l,
  page_in_ranges p (iv :: l)
  = (((bv_unsigned (fst iv) <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned (fst iv) + bv_unsigned (snd iv)))
     || page_in_ranges p l)%bool.
Proof. reflexivity. Qed.

Lemma page_in_ranges_app : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_in_ranges_true : forall p l,
  page_in_ranges p l = true <->
  exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - ((first [ intro dR_72; dex1 dR_72 as iv; dand3 dR_72 as Hin H1 H2 | intro dR_72; dand4 dR_72 as iv Hin H1 H2 | intros (iv & Hin & H1 & H2) ])). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_in_ranges_covers : forall p l z,
  page_in_ranges p l = true -> bv_unsigned p <= z < bv_unsigned p + page_size -> in_ivs z l = true.
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_out : forall (p : word) l lo hi,
  ivs_wf l -> lo <= hi ->
  (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l.
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_in : forall (p : word) l lo hi,
  ivs_wf l -> lo <= bv_unsigned p < hi ->
  page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
  rewrite in_ivs_covered in C.
  (first [ pose proof ((maps_subtract_sem l lo hi Hwf ltac:(lia))) as dR_2; dand3 dR_2 as _ _ Cv | destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv) ]). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_cons_in : forall (p a n : word) l,
  bv_unsigned a <= bv_unsigned p -> bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = true.
Proof.
  intros p a n l H1 H2. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. left.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_cons_out : forall (p a n : word) l,
  (bv_unsigned p + page_size <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned p) ->
  0 < bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = page_in_ranges p l.
Proof.
  intros p a n l H Hn. rewrite page_in_ranges_cons. cbn [fst snd]. unfold page_size in *.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_facts : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
  /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_in_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned x < hi ->
  lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= hi.
Proof.
  intros x lo hi Hlo Hhi Hx. (first [ pose proof ((page_base_facts x)) as dR_3; dand3 dR_3 as P1 P2 P3 | pose proof (page_base_facts x) as (P1 & P2 & P3) ]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_out_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  bv_unsigned (page_base x) + 4096 <= lo \/ hi <= bv_unsigned (page_base x).
Proof.
  intros x lo hi Hlo Hhi Hx. (first [ pose proof ((page_base_facts x)) as dR_4; dand3 dR_4 as P1 P2 P3 | pose proof (page_base_facts x) as (P1 & P2 & P3) ]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma unfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> unfill a n m x = None.
Proof.
  intros a n m x Hx. unfold unfill.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof. intros p H0 H4. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

Lemma is_ecall_at_sound : forall SEGS cs, is_ecall_at SEGS cs = true ->
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true /\ 0 <= pc cs /\ pc cs + 4 < 2 ^ 64.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  exists w. unfold two64 in H4. auto.
Qed.

Lemma page_up_eq : forall len, page_up len = page_round_up_Z len.
Proof. intros. unfold page_up, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma env_agree_le' : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.

Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)

Lemma ext1_agree'' : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma elenZ_lit'' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aluop_eqb_refl : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl, ?mulop_eqb_refl, ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma amap_eqb_refl : forall m, amap_eqb m m = true.
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl. destruct k; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l H. induction H as [|p l Hf Hl IH]; cbn; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.

Lemma sum_sizes_filter_le : forall f l, sum_sizes (List.filter f l) <= sum_sizes l.
Proof.
  intros f l. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (u64_range s). destruct (f (b, s)); cbn; lia.
Qed.

Lemma A_bytes_app' : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.

Lemma A_bytes_flat_map_split : forall {T} (f : T -> list (Z * Z)) (g : T -> bool) l r,
  A_bytes (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) = A_bytes (flat_map f (l ++ r)).
Proof.
  intros T f g l r. rewrite !flat_map_app, !A_bytes_app'. induction l as [|x l IH]; cbn; [lia|].
  destruct (g x); cbn; rewrite !A_bytes_app'; lia.
Qed.

Lemma in_flat_map_split : forall {T U} (f : T -> list U) (g : T -> bool) l r y,
  In y (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) <-> In y (flat_map f (l ++ r)).
Proof.
  intros T U f g l r y. rewrite !in_flat_map. split.
  - ((first [ intro dR_73; dex1 dR_73 as x; destruct dR_73 as [Hx Hy] | intro dR_73; dand3 dR_73 as x Hx Hy | intros (x & Hx & Hy) ])). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|].
    apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|]. apply in_app_iff; right; exact Hx.
  - ((first [ intro dR_74; dex1 dR_74 as x; destruct dR_74 as [Hx Hy] | intro dR_74; dand3 dR_74 as x Hx Hy | intros (x & Hx & Hy) ])). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx].
    + destruct (g x) eqn:E; [apply in_app_iff; left; apply filter_In; auto|].
      apply in_app_iff; right. apply in_app_iff; left. apply filter_In. rewrite E. auto.
    + apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.

Lemma sum_count_filter_le : forall (P P' : Z -> bool) (f : word * word -> bool) l,
  (forall q, In q l -> f q = true -> forall x, B q <= x < B q + S q -> P' x = P x) ->
  sum_count P' (List.filter f l) <= sum_count P l.
Proof.
  intros P P' f l H. induction l as [|q l IH]; cbn; [lia|].
  assert (IH' := IH ltac:(intros q' Hq'; apply H; right; exact Hq')).
  destruct (f q) eqn:E; cbn; [|unfold iv_count in *; pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))); lia].
  unfold iv_count in *. rewrite (zcount_ext P' P); [lia|].
  intros x Hx. apply (H q (or_introl eq_refl) E). pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. lia.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true. Proof. vm_compute. reflexivity. Qed.

Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_lazy : forall flags a n m,
  mmap_noreserve_b flags = true -> with_mmap_backing flags a n m = vm_add_lazy a n m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_gates_core34 : forall flags,
  mmap_flags_core flags = 34%Z ->
  mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_modeled_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags Hc. unfold mmap_modeled_b, mmap_noaccess_b. rewrite Hc.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; vm_compute; reflexivity.
Qed.

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_flags_core_104022 : mmap_flags_core (Z_to_bv 64 1064994) = 1048610%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_gates_core100022 : forall flags prot,
  mmap_flags_core flags = 1048610%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b,
    mmap_noreplace_noaccess_b, mmap_noreplace_rw_b, mmap_noreplace_flags_b.
  rewrite Hc. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_contains : forall l (lo n : word),
  (0 < bv_unsigned n)%Z ->
  region_free l lo n = true -> map_contains l lo n = false.
Proof.
  intros l lo n Hn Hfree. unfold map_contains.
  apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
  cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

(* [comment removed for export] *)
Definition iv_pos (iv : word * word) : Prop := 0 < bv_unsigned (snd iv).
Lemma iv_subtract_pos : forall (a sz : word) lo hi,
  0 < bv_unsigned sz -> Forall iv_pos (State.iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hsz. unfold State.iv_subtract.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs.
  change (bv_modulus 64) with (2 ^ 64) in Ra, Rs.
  apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E1; [|constructor]. apply Z.ltb_lt in E1.
    constructor; [|constructor]. unfold iv_pos. cbn [snd]. rewrite Z_to_bv_unsigned.
    rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; [|constructor]. apply Z.ltb_lt in E2.
    constructor; [|constructor]. unfold iv_pos. cbn [snd]. rewrite Z_to_bv_unsigned.
    rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma maps_subtract_pos : forall l lo hi, Forall iv_pos l -> Forall iv_pos (State.maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] r IH]; intros lo hi H; cbn [State.maps_subtract]; [constructor|].
  inversion H as [|x y Hx Hy]; subst. apply Forall_app. split; [apply iv_subtract_pos; exact Hx | apply IH; exact Hy].
Qed.
(* [comment removed for export] *)

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.
Lemma mprotect_errnos_ENOMEM : forall e, In e mprotect_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (two64 - 12).
Proof. apply bv_eq. reflexivity. Qed.

Section OurSpecNodes.
Variable segs : list Segment.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_cfg_instr segs ACFG ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec_acfg (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall eff m' ev, syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc. split.
  - intros i. apply (sstep_cfg_syscall_acfg segs ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc (Hok i) (Hh' i)).
    rewrite (Hacc i). apply materialize_model_accesses_nil.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + (first [ pose proof ((Hinv _ _ _ Hc)) as dR_5; dex1 dR_5 as i; dand3 dR_5 as -> -> -> | pose proof ((Hinv _ _ _ Hc)) as dR_5; dand4 dR_5 as i -> -> -> | destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->) ]).
      rewrite (Hacc i), materialize_model_accesses_nil in Hm. injection Hm as <-. exists i. split; reflexivity.
    + (first [ pose proof ((Hinv _ _ _ Hc)) as dR_6; dex1 dR_6 as i; dand3 dR_6 as -> -> -> | pose proof ((Hinv _ _ _ Hc)) as dR_6; dand4 dR_6 as i -> -> -> | destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->) ]). rewrite (Hacc i), materialize_model_accesses_nil in Hm. discriminate.
    + (first [ pose proof ((Hinv _ _ _ Hc)) as dR_7; dex1 dR_7 as i; dand3 dR_7 as -> -> -> | pose proof ((Hinv _ _ _ Hc)) as dR_7; dand4 dR_7 as i -> -> -> | destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->) ]). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_grant_not_refusable_of_base : forall flags (m : Model) nZ (a : word),
  (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a H1 H2 H3 H4 H5. unfold mmap_grant_refusable. rewrite H5.
  rewrite (proj2 (vm_gap_available_iff (m_vmmaps m) nZ)); [reflexivity|]. exists a. auto.
Qed.

Lemma mmap_reserve_not_refusable_of_base : forall (m : Model) nZ (a : word),
  (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a H1 H2 H3 H4. unfold mmap_reserve_refusable.
  rewrite (proj2 (vm_gap_available_iff (m_vmmaps m) nZ)); [reflexivity|]. exists a. auto.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_alt1 : forall c (IB : Type) (nx : IB -> config) (B : TSet) (b0 : IB),
  node_ok segs c IB (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) B) ->
  srealizes segs c B.
Proof.
  intros c IB nx B b0 Hnode HB.
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq segs c (t_alt (fun i : IB => t_emit [] B))).
  - apply (srz_node segs c IB (fun _ => []) nx (fun _ => B) b0 Hnode). intros i. apply HB.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
    + intros H. exists b0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

Lemma grant_ok_na_pin_unpack : forall m a n, grant_ok_na_pin m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\ (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros m a n H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. tauto.
Qed.

Lemma grant_ok_na_pin_pack : forall m a n,
  (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z -> (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true ->
  grant_ok_na_pin m a n = true.
Proof.
  intros m a n Hal Hpos Htop Hrf. unfold grant_ok_na_pin.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Htop), Hrf.
  reflexivity.
Qed.

Lemma mmap_grant_of_not_refusable : forall flags m nZ,
  mmap_grant_refusable flags m nZ = false ->
  mmap_noreserve_backed_ok flags m nZ = true /\ exists a, grant_ok_na_pin m a nZ = true.
Proof.
  intros flags m nZ H. unfold mmap_grant_refusable in H. apply orb_false_iff in H as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg. split; [exact Hb|].
  apply vm_gap_available_iff in Hg as (a & Hal & Hpos & Htop & Hrf). exists a.
  apply grant_ok_na_pin_pack; assumption.
Qed.

Lemma mmap_reserve_grant_of_not_refusable : forall m nZ,
  mmap_reserve_refusable m nZ = false -> exists a, grant_ok_na_pin m a nZ = true.
Proof.
  intros m nZ H. unfold mmap_reserve_refusable in H. apply negb_false_iff in H.
  apply vm_gap_available_iff in H as (a & Hal & Hpos & Htop & Hrf). exists a.
  apply grant_ok_na_pin_pack; assumption.
Qed.

Lemma mmap_rw_check_rel : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                && listNN_eqb zs [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (Gm & _ & _).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, mmap_model.
  destruct (mmap_noreserve_backed_ok flags model nZ); rewrite ?andb_true_r, ?andb_false_r; [reflexivity|].
  cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma mmap_rw_check : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z ->
  m_halted model = None ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  mmap_grant_refusable flags model nZ = false ->
  forall eff m' evs,
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)
  <-> match eff with
    | mkEffectU r [] zs [] [] [] =>
        if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                && listNN_eqb zs [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end = CheckOk m' evs.
Proof.
  intros ms x8 model flags Hno Hh H1 H2 H3 Hcore H4 H5 nZ Hnf.
  pose proof (fun eff => mmap_rw_check_rel ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5) as Hrel.
  cbv zeta in Hrel. fold nZ in Hrel.
  apply (acfg_iff_guard (sys_input segs ms x8) model mmap_errnos
           (fun eff => match eff with
              | mkEffectU r [] zs [] [] [] =>
                  if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                          && listNN_eqb zs [(r, Z_to_bv 64 nZ)]
                  then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
                  else CheckReject
              | _ => CheckReject
              end)).
  - exact (acfg_off_222 segs ms x8 Hno).
  - intros eff. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity.
  - intros [r ws zs us cs ci] Er. rewrite Hrel. cbn [eff_ret] in Er |- *.
    destruct ws, zs, us, cs, ci; cbv beta iota; try reflexivity; rewrite Er; reflexivity.
  - intros eff m' evs Er Hc. rewrite Hrel in Hc. destruct eff as [r ws zs us cs ci].
    cbn [eff_ret] in Er, Hc.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hc; try discriminate Hc;
      rewrite Er in Hc; cbv beta iota in Hc; try discriminate Hc; injection Hc as <- <-; exact Hh.
  - intros eff m' evs Hg. destruct eff as [r ws zs us cs ci]. cbn [eff_ret]. cbv beta iota in Hg.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hg; try discriminate Hg;
      destruct (grant_ok_na_pin model r nZ) eqn:Hga; try discriminate Hg;
      destruct (grant_ok_na_pin_unpack _ _ _ Hga) as (Hal & _); exact (errno_mm_aligned r Hal).
  - destruct (mmap_grant_of_not_refusable flags model nZ Hnf) as [Hb [a Ha]].
    exists (mkEffectU a [] [(a, Z_to_bv 64 nZ)] [] [] []),
           (with_mmap_backing flags a (Z_to_bv 64 nZ) (mmap_model a (Z_to_bv 64 nZ) model)), [].
    cbv beta iota. rewrite Ha, Hb, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_rw1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> init_sp_ok (m_vmmaps model) ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true /\ mmap_noreserve_backed_ok flags model nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true -> mmap_noreserve_backed_ok flags model nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh Hisp H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0 & Hb0) HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_aligned').
  assert (Hnf : mmap_grant_refusable flags model nZ = false).
  { destruct (grant_ok_na_pin_unpack _ _ _ Ha0) as (P1 & P2 & P3 & P4).
    exact (mmap_grant_not_refusable_of_base flags model nZ a0 P1 P2 P3 P4 Hb0). }
  pose proof (mmap_rw_check ms (getr regs 17) model flags Hno Hh Hne1
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  pose proof (Hchk Hnf) as Hck. clear Hchk.
  rewrite Hb0 in Hck.
  pose proof (fun eff => mmap_rw_check_rel ms (getr regs 17) model eff flags Hno Hne1
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hrel.
  cbv zeta in Hrel. rewrite Hl1 in Hrel. fold nZ n in Hrel.
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (EFF := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (MS := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n model) end).
  apply (srz_alt1 (mkCfg ms model) IB
           (fun i => mkCfg (advance_past_svc (apply_effect ms (EFF i))) (MS i)) KB
           (exist _ a0 Ha0)).
  - apply (node_chk_ev_mat ms model (getr regs 17) IB EFF MS (fun _ => []) Hh eq_refl).
    + intros [a Ha]. unfold EFF, MS. cbv beta iota. apply Hck. cbv beta iota.
      rewrite Ha. cbn [andb].
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. apply Hck in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
      cbn [andb] in Hc.
      destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      exists (exist _ r Hg). unfold EFF, MS. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros [r [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]] Hc; rewrite Hrel in Hc; cbv beta iota in Hc;
        acfg_if_split Hc; discriminate Hc.
    + intros [a Ha]. unfold MS. cbv beta iota. rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. unfold EFF, MS. cbv beta iota. unfold ms. rewrite adv_zeros1_epend. apply HB; [exact Ha | exact Hb0].
Qed.


Lemma mmap_none_check_rel : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma mmap_none_check : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z ->
  m_halted model = None ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  mmap_reserve_refusable model nZ = false ->
  forall eff m' evs,
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)
  <-> match eff with
    | mkEffectU r [] [] us [] [] =>
        if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end = CheckOk m' evs.
Proof.
  intros ms x8 model flags Hno Hh H1 H2 H3 Hcore H4 H5 nZ Hnf.
  pose proof (fun eff => mmap_none_check_rel ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5) as Hrel.
  cbv zeta in Hrel. fold nZ in Hrel.
  apply (acfg_iff_guard (sys_input segs ms x8) model mmap_errnos
           (fun eff => match eff with
              | mkEffectU r [] [] us [] [] =>
                  if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
                  then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
                  else CheckReject
              | _ => CheckReject
              end)).
  - exact (acfg_off_222 segs ms x8 Hno).
  - intros eff. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity.
  - intros [r ws zs us cs ci] Er. rewrite Hrel. cbn [eff_ret] in Er |- *.
    destruct ws, zs, us, cs, ci; cbv beta iota; try reflexivity; rewrite Er; reflexivity.
  - intros eff m' evs Er Hc. rewrite Hrel in Hc. destruct eff as [r ws zs us cs ci].
    cbn [eff_ret] in Er, Hc.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hc; try discriminate Hc;
      rewrite Er in Hc; cbv beta iota in Hc; try discriminate Hc; injection Hc as <- <-; exact Hh.
  - intros eff m' evs Hg. destruct eff as [r ws zs us cs ci]. cbn [eff_ret]. cbv beta iota in Hg.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hg; try discriminate Hg;
      destruct (grant_ok_na_pin model r nZ) eqn:Hga; try discriminate Hg;
      destruct (grant_ok_na_pin_unpack _ _ _ Hga) as (Hal & _); exact (errno_mm_aligned r Hal).
  - destruct (mmap_reserve_grant_of_not_refusable model nZ Hnf) as [a Ha].
    exists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []),
           (with_mmap_backing flags a (Z_to_bv 64 nZ) (noaccess_model a (Z_to_bv 64 nZ) model)), [].
    cbv beta iota. rewrite Ha, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma srz_mmap_none1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> init_sp_ok (m_vmmaps model) ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh Hisp H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_aligned').
  assert (Hnf : mmap_reserve_refusable model nZ = false).
  { destruct (grant_ok_na_pin_unpack _ _ _ Ha0) as (P1 & P2 & P3 & P4).
    exact (mmap_reserve_not_refusable_of_base model nZ a0 P1 P2 P3 P4). }
  pose proof (mmap_none_check ms (getr regs 17) model flags Hno Hh Hne1
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  pose proof (Hchk Hnf) as Hck. clear Hchk.
  pose proof (fun eff => mmap_none_check_rel ms (getr regs 17) model eff flags Hno Hne1
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hrel.
  cbv zeta in Hrel. rewrite Hl1 in Hrel. fold nZ n in Hrel.
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (EFF := fun i : IB => match i with exist _ a _ => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (MS := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (noaccess_model a n model) end).
  apply (srz_alt1 (mkCfg ms model) IB
           (fun i => mkCfg (advance_past_svc (apply_effect ms (EFF i))) (MS i)) KB
           (exist _ a0 Ha0)).
  - apply (node_chk_ev_mat ms model (getr regs 17) IB EFF MS (fun _ => []) Hh eq_refl).
    + intros [a Ha]. unfold EFF, MS. cbv beta iota. apply Hck. cbv beta iota.
      rewrite Ha. cbn [andb].
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. apply Hck in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
      destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
      exists (exist _ r Hg). unfold EFF, MS. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros [r [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]] Hc; rewrite Hrel in Hc; cbv beta iota in Hc;
        acfg_if_split Hc; discriminate Hc.
    + intros [a Ha]. unfold MS. cbv beta iota. rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. unfold EFF, MS. cbv beta iota. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.



End OurSpecNodes.


Section OurSpecNodes2.
Variable segs : list Segment.

Lemma mmap_fixed_gate_open : forall (h : VmMaps) (addr : word) (len : Z),
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok h ->
  (two_pow_64 <=? bv_unsigned addr + page_round_up_Z len)%Z = false
  /\ negb (bv_unsigned addr + page_round_up_Z len <=? alloc_top h)%Z = false
  /\ negb (bv_unsigned addr mod page_size =? 0)%Z = false
  /\ negb (0 <? bv_unsigned addr)%Z = false
  /\ (len < 2 ^ 64)%Z /\ (0 < page_round_up_Z len < 2 ^ 64)%Z.
Proof.
  intros h addr len Hal Hpos Hlen Hce Hisp. pose proof alloc_ceiling_val.
  pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
  - apply Z.leb_gt. unfold two_pow_64. lia.
  - rewrite (proj2 (Z.leb_le _ _) (alloc_top_ge_of_ceiling _ _ Hisp Hce)). reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _) Hal). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) Hpos). reflexivity.
  - lia. - lia. - lia.
Qed.

Lemma mmap_fixed_rw_free_check_rel : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> (mmap_flags_core flags = 50%Z \/ mmap_flags_core flags = 1048610%Z) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf Hbk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  destruct Hcore as [Hcore|Hcore].
  - destruct (mmap_gates_core50 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & _ & Gfn & Gfr).
    rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. cbn [negb]. cbv beta iota zeta.
    rewrite G1, G2, G3, G4. fold nZ. fold n.
    assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
    { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
      rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
    rewrite Hmc, andb_false_r, Hrf. rewrite Hbk.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct us; [|reflexivity].
    destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    rewrite andb_true_r. unfold mmap_model. reflexivity.
  - (* [comment removed for export] *)
    destruct (mmap_gates_core100022 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & Gfn & Gfr & _ & Gnn & Gnr).
    rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr, Gnn, Gnr. cbn [negb]. cbv beta iota zeta.
    rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf. rewrite Hbk.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct us; [|reflexivity].
    destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    rewrite andb_true_r. unfold mmap_model. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_rw_free_check : forall ms x8 model flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  m_halted model = None ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> (mmap_flags_core flags = 50%Z \/ mmap_flags_core flags = 1048610%Z) ->   (* [comment removed for export] *)
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->   (* [comment removed for export] *)
  forall eff m' evs,
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)
  <-> match eff with
    | mkEffectU r [] zs [] [] [] =>
        if bv_eqb r addr && listNN_eqb zs [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end = CheckOk m' evs.
Proof.
  intros ms x8 model flags addr len Hno Hh H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf Hbk.
  pose proof (fun eff => mmap_fixed_rw_free_check_rel ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp
                           H2 H3 Hcore H4 H5 Hrf Hbk) as Hrel.
  cbv zeta in Hrel. fold nZ n in Hrel.
  apply (acfg_iff_guard (sys_input segs ms x8) model mmap_errnos
           (fun eff => match eff with
              | mkEffectU r [] zs [] [] [] =>
                  if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                  then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
                  else CheckReject
              | _ => CheckReject
              end)).
  - exact (acfg_off_222 segs ms x8 Hno).
  - intros eff. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity.
  - intros [r ws zs us cs ci] Er. rewrite Hrel. cbn [eff_ret] in Er |- *.
    destruct ws, zs, us, cs, ci; cbv beta iota; try reflexivity; rewrite Er; reflexivity.
  - intros eff m' evs Er Hc. rewrite Hrel in Hc. destruct eff as [r ws zs us cs ci].
    cbn [eff_ret] in Er, Hc.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hc; try discriminate Hc;
      rewrite Er in Hc; cbv beta iota in Hc; try discriminate Hc; injection Hc as <- <-; exact Hh.
  - intros eff m' evs Hg. destruct eff as [r ws zs us cs ci]. cbn [eff_ret]. cbv beta iota in Hg.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hg; try discriminate Hg;
      destruct (bv_eqb r addr) eqn:Eb; try discriminate Hg;
      apply bv_eqb_eq in Eb; subst r; exact (errno_mm_aligned addr Hal).
  - exists (mkEffectU addr [] [(addr, n)] [] [] []), (with_mmap_backing flags addr n (mmap_model addr n model)), [].
    cbv beta iota. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_rw_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> (mmap_flags_core flags = 50%Z \/ mmap_flags_core flags = 1048610%Z) ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (R0 : ms_gpr ms 0 = addr) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (R1 : ms_gpr ms 1 = Z_to_bv 64 len) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (R2 : ms_gpr ms 2 = Z_to_bv 64 3) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  assert (R3 : ms_gpr ms 3 = flags) by (unfold ms; rewrite ms_gpr_epend3; exact H13).
  assert (R4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by (unfold ms; rewrite ms_gpr_epend4; exact H14).
  assert (R5 : ms_gpr ms 5 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend5; exact H15).
  pose proof (mmap_fixed_rw_free_check ms (getr regs 17) model flags addr len Hno Hh
                R0 Hal Hpos R1 Hlen Hce Hisp R2 R3 Hcore R4 R5 Hrf Hbk) as Hchk.
  pose proof (fun eff => mmap_fixed_rw_free_check_rel ms (getr regs 17) model eff flags addr len Hno
                R0 Hal Hpos R1 Hlen Hce Hisp R2 R3 Hcore R4 R5 Hrf Hbk) as Hrel.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  cbv zeta in Hrel. fold nZ in Hrel. fold n in Hrel.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [(addr, n)] [] [] [])))
                  (with_mmap_backing flags addr n (mmap_model addr n model)))).
  - apply (node_chk_ev_mat segs ms model (getr regs 17) unit (fun _ => mkEffectU addr [] [(addr, n)] [] [] [])
             (fun _ => with_mmap_backing flags addr n (mmap_model addr n model)) (fun _ => []) Hh eq_refl).
    + intros []. cbv beta. apply Hchk. cbv beta iota. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. apply Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros [r [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]] Hc; rewrite Hrel in Hc; cbv beta iota in Hc;
        acfg_if_split Hc; discriminate Hc.
    + intros []. rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.


Lemma mmap_fixed_none_free_check_rel : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> (mmap_flags_core flags = 50%Z \/ mmap_flags_core flags = 1048610%Z) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  destruct Hcore as [Hcore|Hcore].
  - destruct (mmap_gates_core50 flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & _ & _).
    rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn. cbn [negb]. cbv beta iota zeta.
    rewrite G1, G2, G3, G4. fold nZ. fold n.
    assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
    { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
      rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
    rewrite Hmc, andb_false_r, Hrf.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct zs; [|reflexivity].
    destruct cs; [|reflexivity].
    destruct ci; [|reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    unfold noaccess_model. reflexivity.
  - (* [comment removed for export] *)
    destruct (mmap_gates_core100022 flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & Gfr & Gnn & _ & _).
    rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr, Gnn. cbn [negb]. cbv beta iota zeta.
    rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct zs; [|reflexivity].
    destruct cs; [|reflexivity].
    destruct ci; [|reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    unfold noaccess_model. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_none_free_check : forall ms x8 model flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  m_halted model = None ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> (mmap_flags_core flags = 50%Z \/ mmap_flags_core flags = 1048610%Z) ->   (* [comment removed for export] *)
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  forall eff m' evs,
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)
  <-> match eff with
    | mkEffectU r [] [] us [] [] =>   (* [comment removed for export] *)
        if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end = CheckOk m' evs.
Proof.
  intros ms x8 model flags addr len Hno Hh H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  pose proof (fun eff => mmap_fixed_none_free_check_rel ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp
                           H2 H3 Hcore H4 H5 Hrf) as Hrel.
  cbv zeta in Hrel. fold nZ n in Hrel.
  apply (acfg_iff_guard (sys_input segs ms x8) model mmap_errnos
           (fun eff => match eff with
              | mkEffectU r [] [] us [] [] =>
                  if bv_eqb r addr && listNN_eqb us [(addr, n)]
                  then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
                  else CheckReject
              | _ => CheckReject
              end)).
  - exact (acfg_off_222 segs ms x8 Hno).
  - intros eff. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity.
  - intros [r ws zs us cs ci] Er. rewrite Hrel. cbn [eff_ret] in Er |- *.
    destruct ws, zs, us, cs, ci; cbv beta iota; try reflexivity; rewrite Er; reflexivity.
  - intros eff m' evs Er Hc. rewrite Hrel in Hc. destruct eff as [r ws zs us cs ci].
    cbn [eff_ret] in Er, Hc.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hc; try discriminate Hc;
      rewrite Er in Hc; cbv beta iota in Hc; try discriminate Hc; injection Hc as <- <-; exact Hh.
  - intros eff m' evs Hg. destruct eff as [r ws zs us cs ci]. cbn [eff_ret]. cbv beta iota in Hg.
    destruct ws, zs, us, cs, ci; cbv beta iota in Hg; try discriminate Hg;
      destruct (bv_eqb r addr) eqn:Eb; try discriminate Hg;
      apply bv_eqb_eq in Eb; subst r; exact (errno_mm_aligned addr Hal).
  - exists (mkEffectU addr [] [] [(addr, n)] [] []), (with_mmap_backing flags addr n (noaccess_model addr n model)), [].
    cbv beta iota. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma srz_mmap_fixed_none_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> (mmap_flags_core flags = 50%Z \/ mmap_flags_core flags = 1048610%Z) ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (R0 : ms_gpr ms 0 = addr) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (R1 : ms_gpr ms 1 = Z_to_bv 64 len) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (R2 : ms_gpr ms 2 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  assert (R3 : ms_gpr ms 3 = flags) by (unfold ms; rewrite ms_gpr_epend3; exact H13).
  assert (R4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by (unfold ms; rewrite ms_gpr_epend4; exact H14).
  assert (R5 : ms_gpr ms 5 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend5; exact H15).
  pose proof (mmap_fixed_none_free_check ms (getr regs 17) model flags addr len Hno Hh
                R0 Hal Hpos R1 Hlen Hce Hisp R2 R3 Hcore R4 R5 Hrf) as Hchk.
  pose proof (fun eff => mmap_fixed_none_free_check_rel ms (getr regs 17) model eff flags addr len Hno
                R0 Hal Hpos R1 Hlen Hce Hisp R2 R3 Hcore R4 R5 Hrf) as Hrel.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  cbv zeta in Hrel. fold nZ in Hrel. fold n in Hrel.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                  (with_mmap_backing flags addr n (noaccess_model addr n model)))).
  - apply (node_chk_ev_mat segs ms model (getr regs 17) unit (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
             (fun _ => with_mmap_backing flags addr n (noaccess_model addr n model)) (fun _ => []) Hh eq_refl).
    + intros []. cbv beta. apply Hchk. cbv beta iota. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. apply Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
      exists tt. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros [r [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]] Hc; rewrite Hrel in Hc; cbv beta iota in Hc;
        acfg_if_split Hc; discriminate Hc.
    + intros []. rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.


(* [comment removed for export] *)

Lemma srz_mprotect1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (mprotect_check segs ms (getr regs 17) model addr len Hno Hh
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  pose proof (fun eff => mprotect_check_rel segs ms (getr regs 17) model eff addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hrel.
  cbv zeta in Hchk. fold n in Hchk. cbv zeta in Hrel. fold n in Hrel.
  (* [comment removed for export] *)
  assert (Hnf : mprotect_refusable model addr n = false) by (unfold mprotect_refusable; rewrite Hbud; reflexivity).
  rewrite Hnf, Hbud in Hchk. cbn [mprotect_errnos_when errno_ret_in existsb] in Hchk.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                  (mprotect_model addr n model))).
  - apply (node_chk_ev_mat segs ms model (getr regs 17) unit (fun _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])
             (fun _ => mprotect_model addr n model) (fun _ => []) Hh eq_refl).
    + intros []. cbv beta. apply Hchk. cbv beta iota.
      unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. apply Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
      exists tt. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros [r [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]] Hc; rewrite Hrel in Hc; cbv beta iota in Hc;
        acfg_if_split Hc; discriminate Hc.
    + intros []. unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.


End OurSpecNodes2.


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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis RES_cover : APS.res_cover_ok SEGS A.
Hypothesis SHADOW_val : APS.shadow_val_ok A.
Hypothesis NX0_ok : APS.nx0_ok nx0.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT NX0_ok SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB HULL_ok SHADOW_ok SHADOW_val SINV argH argH_top FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="reg_lit_sound' reg_sound' HULL_ok' RES_len' HULL_ok RES_len"] Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
  CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  getr R (Z_to_bv 5 11) = Z_to_bv 64 len
  /\ 0 < len < 2 ^ 64
  /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
  /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
  /\ page_round_up_Z len mod 4096 = 0
  /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> edenot E' ne = edenot E ne).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML. (* [comment removed for export] *) unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection HML as <- <- <-.
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
    apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
    destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
    assert (Hmod : len mod 4096 = 0).
    { unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
      replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
        by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    assert (Hpr : page_round_up_Z len = len).
    { unfold page_round_up_Z, page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hpr.
    split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
    split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
    intros E' HE'. exact HE'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_14 : (14%bv : bv 5) = Z_to_bv 5 (Z.of_nat 14). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_15 : (15%bv : bv 5) = Z_to_bv 5 (Z.of_nat 15). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17). Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)

Lemma CEIL_eq : alloc_ceiling = CEIL.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma FLOOR_eq : bottomup_floor = FLOOR.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

Lemma Z_to_bv64_m1 : forall m1, m1 = two64 - 1 -> Z_to_bv 64 m1 = Z_to_bv 64 (-1).
Proof. intros m1 ->. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
#[using="RES_hullH HULL_ok' RES_len' HULL_ok RES_hull RES_len"] Lemma reserved_free_above : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  img_hi A <= bv_unsigned lo ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
Qed.
(* [comment removed for export] *)
#[using="RES_hullH HULL_ok' RES_len' HULL_ok RES_hull RES_len"] Lemma reserved_free_apart : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_add_inv : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  exists nhi, xhi (kn cs) n = Some nhi /\
  cs2 = ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts A (kn cs) (a_maps cs) b n ++ k) (nxt cs))
            (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
            ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs).
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts. rewrite Hsh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_allow_ext : forall E cs cs', a_vis cs' = a_vis cs -> in_allow A E cs' = in_allow A E cs.
Proof. intros E cs cs' H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kind_none (k : mkind) : bool := match k with KNONE | KNONELAZY => true | _ => false end.
Definition kind_lazy (k : mkind) : bool := match k with KRWLAZY | KNONELAZY => true | _ => false end.

Record grant_post (kd : mkind) (a n : word) (model model' : Model) : Prop := GP {
  gp_maps : vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model);
  gp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  gp_noacc : vm_noaccess (m_vmmaps model') = (if kind_none kd then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model));
  gp_lazy : m_vm_lazy model' = (if kind_lazy kd then (a, n) :: m_vm_lazy model else m_vm_lazy model);
  gp_mat : m_vm_materialized model' = m_vm_materialized model;
  gp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  gp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  gp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  gp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  gp_halted : m_halted model' = m_halted model;
  gp_fds : m_fds model' = m_fds model;
  gp_fs : m_fs model' = m_fs model;
  gp_tid : m_tid model' = m_tid model;
  gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)  (* [comment removed for export] *) }.

Definition grant_mem (kd : mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
        FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
#[using="RES_len' RES_len SEGS"] Lemma vis_grant_out : forall kd (a n : word) model model' E cs cs1 (x : word),
  grant_post kd a n model model' ->
  a_vis cs1 = a_vis cs ->
  0 < bv_unsigned n -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  VIS E cs1 model' x = VIS E cs model x.
Proof.
  intros kd a n model model' E cs cs1 x GPo Hvis Hn Hal Hnl Hx.
  unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  replace (alloc_top (m_vmmaps model')) with (alloc_top (m_vmmaps model)) by (unfold alloc_top; rewrite (gp_isp _ _ _ _ _ GPo); reflexivity).   (* [comment removed for export] *)
  rewrite (in_allow_ext E cs cs1 Hvis).
  rewrite in_ivs_cons. cbn [fst snd].
  assert (T : ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool = false).
  { apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  rewrite T. cbn [orb].
  assert (P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model) = page_in_ranges (page_base x) (m_vm_lazy model)).
  { apply page_in_ranges_cons_out; [|exact Hn].
    pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal ltac:(rewrite Z.add_mod, Hal, Hnl by lia; reflexivity) Hx).
    unfold page_size. lia. }
  destruct (kind_none kd); destruct (kind_lazy kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T, ?P; cbn [orb]; reflexivity.
Qed.

#[using="RES_len' RES_len A SEGS"] Lemma grant_wf : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> model_ivs_wf model'.
Proof.
  (intros kd a n model model' GPo; (first [ intro dR_76; dand4 dR_76 as W1 W2 W3 Wsp | intros (W1 & W2 & W3 & Wsp) ]); intros Hb). unfold model_ivs_wf.
  rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  assert (iv_wf (a, n)) by (unfold iv_wf, B, S; cbn; lia).
  split; [apply ivs_wf_cons; assumption|].
  split; [destruct (kind_none kd); try apply ivs_wf_cons; assumption|].
  split; [destruct (kind_lazy kd); try apply ivs_wf_cons; assumption|].
  unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GPo). exact Wsp.
Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma grant_eager_le : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  eager_used model' <= eager_used model + (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n).
Proof.
  intros kd a n model model' GPo Hwf Hb.
  pose proof (grant_wf kd a n model model' GPo Hwf Hb) as Hwf'.
  rewrite (eager_used_sem model' Hwf'), (eager_used_sem model Hwf).
  rewrite (gp_maps _ _ _ _ _ GPo).
  set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
  set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
  cbn [sum_count].
  assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                 <= sum_count (fun x => negb (covered C x)) (vm_maps (m_vmmaps model))).
  { apply sum_count_negb_covered_mono. intros x Hx. subst C C'.
    rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app in Hx. rewrite covered_app.
    apply orb_true_iff in Hx. apply orb_true_iff.
    destruct Hx as [Hx|Hx]; [left|right]; [destruct (kind_none kd) | destruct (kind_lazy kd)]; try exact Hx;
      unfold covered in *; cbn [existsb]; rewrite Hx; apply orb_true_r. }
  assert (HEAD : iv_count (fun x => negb (covered C' x)) (a, n) <= (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n)).
  { destruct (kind_none kd || kind_lazy kd)%bool eqn:Hk.
    - unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_false; [lia|]. intros x Hx.
      pose proof (u64_range n). rewrite Z2Nat.id in Hx by lia. apply negb_false_iff.
      subst C'. rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app.
      assert (IN : in_iv (a, n) x = true).
      { unfold in_iv, in_rng, B, S. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      apply orb_prop in Hk as [Hk|Hk]; rewrite Hk; unfold covered; cbn [existsb]; rewrite IN; cbn [orb];
        [reflexivity | apply orb_true_r].
    - unfold iv_count, S. cbn [snd]. pose proof (u64_range n).
      pose proof (zcount_le_len (fun x => negb (covered C' x)) (B (a, n)) (Z.to_nat (bv_unsigned n))). lia. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition maps_apart (E : env) (ms : list amap) (lo n : Z) : Prop :=
  forall m, In m ms -> is_fog m = false ->
    lo + n <= bv_unsigned (edenot E (am_base m)) \/
    bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= lo.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma lit_cover_point : forall E ms fuel lo hi z,
  lit_cover fuel ms lo hi = true -> lo <= z < hi ->
  exists m, In m ms /\ is_fog m = false /\
    bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
  intros E ms fuel. induction fuel as [|f IH]; intros lo hi z Hc Hz; cbn [lit_cover] in Hc.
  - apply Z.leb_le in Hc. lia.
  - destruct (Z.leb hi lo) eqn:Hhl; [apply Z.leb_le in Hhl; lia|].
    apply existsb_exists in Hc as [m [Hm Hb]]. destruct (is_fog m) eqn:Hnf; [discriminate|].
    destruct (am_base m) as [b| | | | | | |] eqn:Hbm; try discriminate.
    destruct (am_len m) as [l| | | | | | |] eqn:Hlm; try discriminate.
    match type of Hb with (if ?c then _ else _) = true => destruct c eqn:Hg; [|discriminate] end. rename Hb into Hrec. rename Hg into Hb.
    apply andb_prop in Hb as [Hb H64]. apply andb_prop in Hb as [Hb Hlob]. apply andb_prop in Hb as [H0b Hblo].
    apply Z.leb_le in H0b. apply Z.leb_le in Hblo. apply Z.ltb_lt in Hlob. apply Z.ltb_lt in H64. unfold two64 in H64.
    destruct (Z_lt_ge_dec z (b + l)) as [Hzl|Hzl].
    + exists m. split; [exact Hm|]. split; [exact Hnf|]. rewrite Hbm, Hlm. cbn [edenot]. rewrite !u64_lit by lia. lia.
    + exact (IH (b + l) hi z Hrec ltac:(lia)).
Qed.
(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma lit_cover_apart : forall E ms fuel lo hi a nZ,
  lit_cover fuel ms lo hi = true -> lo < hi -> maps_apart E ms a nZ -> 0 < nZ ->
  lo + (hi - lo) <= a \/ a + nZ <= lo.
Proof.
  intros E ms fuel lo hi a nZ Hc Hlh Hap HnZ.
  destruct (Z_le_gt_dec hi a); [left; lia|]. destruct (Z_le_gt_dec (a + nZ) lo); [right; lia|]. exfalso.
  destruct (lit_cover_point E ms fuel lo hi (Z.max a lo) Hc ltac:(lia)) as [m (Hm & Hnf & Hz)].
  pose proof (Hap m Hm Hnf). lia.
Qed.

Lemma maps_apart_of_region_free : forall E ms model (a n : word),
  maps_match E ms (vm_maps (m_vmmaps model)) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  maps_apart E ms (bv_unsigned a) (bv_unsigned n).
Proof.
  intros E ms model a n Hmaps Hrf m Hin Hnf.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
  exact (RefNodes.region_free_In _ a n (edenot E (am_base m)) (edenot E (am_len m)) Hrf (maps_match_In E ms _ m Hmaps Hin Hnf)).
Qed.

#[using="HULL_ok' RES_len' HULL_ok RES_len A"] Lemma inside_maps_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  inside_maps k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap. induction ms as [|m ms IH]; intros H; [discriminate|].
  cbn [inside_maps] in H. apply orb_prop in H as [H|H].
  - apply andb_prop in H as [Hnf H]. apply negb_true_iff in Hnf.
    pose proof (APS.xinsideX_sound SEGS E M k b o l (am_base m) 0 (am_len m) HK H) as [I1 I2].   (* [comment removed for export] *)
    unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *.
    destruct (Hap m (or_introl eq_refl) Hnf); lia.
  - apply IH; [|exact H]. intros m' Hm'. apply Hap. right. exact Hm'.
Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' SHADOW_val HULL_ok RES_len"] Lemma safe_range_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n + 8388608 <= uE E e_sp0 -> 0 < n ->
  safe_range A k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hlo Hhi Hn H. unfold safe_range in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
    pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
    unfold estart, elenZ. cbn [a_base a_off].
    apply orb_prop in H as [H|H].
    + apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2. lia.
    + (* [comment removed for export] *)
      apply andb_prop in H as [H H2]. apply andb_prop in H as [Hc H1]. apply Z.leb_le in H1; apply Z.leb_le in H2.
      pose proof SHADOW_val as SV. unfold APS.shadow_val_ok in SV.
      pose proof (lit_cover_apart E ms (length ms) (LOWSH A) KHI lo n Hc ltac:(unfold LOWSH, KHI; rewrite SV; lia) Hap Hn) as HB.
      unfold LOWSH in *. lia.
  - (* [comment removed for export] *)
    pose proof (xinside_sound SEGS E M k b o l e_sp0 (-8388608) (ELit BANDLEN) HK H) as [I1 I2].
    unfold estart in I1 |- *. cbn [a_base a_off] in I1 |- *. unfold uE in Hhi. lia.
  - eapply inside_maps_apart; eassumption.
Qed.

#[using="HULL_ok' RES_len' SHADOW_val HULL_ok RES_len"] Lemma grant_keep_apart : forall E M k ms K lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n + 8388608 <= uE E e_sp0 -> 0 < n ->
  grant_keep_b A k ms K = true ->
  match K with KImg _ _ => False | _ => True end ->
  kfoot_apart E K lo n.
Proof.
  intros E M k ms K lo n HK Hap Hlo Hhi Hn H HnI. unfold kfoot_apart, kfoot.
  destruct K as [[b o] w v|[b o] l|[b o] l kb|ilo ihi|e m|e rlo rhi|[b o] l|a1 n1 a2 n2|[b o] l fc|[b o] l]; cbn [grant_keep_b] in H;
    try exact I; [apply andb_prop in H as [Hw H]; apply Nat.leb_le in Hw| | | destruct HnI | | |];
    pose proof (safe_range_apart E M k ms b o _ lo n HK Hap Hlo Hhi Hn H) as D; try lia.
  rewrite elenZ_lit'' in D by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="kimg_clip_in_hull' kentry_keep_sem' HULL_ok' RES_len' SHADOW_val HULL_ok RES_len"] Lemma kn_grant_filter_ok : forall E M M' k ms lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n + 8388608 <= uE E e_sp0 -> 0 < n ->
  (forall x : word, bv_unsigned x < lo \/ lo + n <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kn_grant_filter A k ms).
Proof.
  intros E M M' k ms lo n HK Hap Hlo Hhi Hn Hout. unfold kn_grant_filter.
  pose proof (kimg_clip_in_hull' (List.filter (grant_keep_b A k ms) k)) as Hhull.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hhull K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  destruct K as [| | |ilo ihi| | | | | |];
    try (eapply grant_keep_apart; [exact HK | exact Hap | exact Hlo | exact Hhi | exact Hn | exact Hkeep | exact I]).
  (* [comment removed for export] *)
  unfold kfoot_apart, kfoot. cbn in HKh. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="RES_len' RES_len A SEGS"] Lemma regs_ok_regupd_same : forall E sr R n (v : word),
  regs_ok E sr R -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = v ->
  regs_ok E sr (regupd R (Z_to_bv 5 (Z.of_nat n)) v).
Proof.
  intros E sr R n v HR Hn Hv r.
  assert (Hne : Z_to_bv 5 (Z.of_nat n) <> 0%bv).
  { intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
    change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
  destruct (bv_eqb r (Z_to_bv 5 (Z.of_nat n))) eqn:Hr.
  - apply (proj1 (bv_eqb_eq _ _)) in Hr. subst r. rewrite getr_same by exact Hne. rewrite <- Hv. apply HR.
  - assert (Hr' : r <> Z_to_bv 5 (Z.of_nat n)) by (intros ->; rewrite bv_eqb_refl in Hr; discriminate).
    rewrite getr_other by exact Hr'. apply HR.
Qed.

(* [comment removed for export] *)
Lemma cs_top : forall E cs R FULL model, CSOK E cs R FULL model ->
  alloc_top (m_vmmaps model) + 8388608 = uE E e_sp0.
Proof. intros E cs R FULL model HC. exact (APS.co_top _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
#[using="argH_top"] Lemma cs_argH_top : forall E cs R FULL model (x : word), CSOK E cs R FULL model -> argH E x = true ->
  alloc_top (m_vmmaps model) + 8388608 <= bv_unsigned x.
Proof.
  intros E cs R FULL model x HC Hx. rewrite (cs_top E cs R FULL model HC).
  exact (argH_top _ _ _ (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Hx).
Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' RES_cover HULL_ok RES_len"] Lemma free_apart_hull : forall model (a n : word) nZ,
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ ->
  bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a.
Proof.
  intros model a n nZ Hres Hrf Un HnZ.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3). pose proof (u64_range a) as Ra.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _]. rewrite Hres in Hrf.
  destruct (Z_le_gt_dec (bv_unsigned a + nZ) (img_lo A)) as [|G1]; [left; assumption|].
  destruct (Z_le_gt_dec (img_hi A) (bv_unsigned a)) as [|G2]; [right; assumption|]. exfalso.
  destruct RES_cover as [HLH RC].
  set (z := Z.max (bv_unsigned a) (img_lo A)).
  assert (Hz : img_lo A <= z < img_hi A /\ bv_unsigned a <= z < bv_unsigned a + nZ) by (unfold z; lia).
  pose proof (RC z (proj1 Hz)) as Hin. unfold in_ivs in Hin. apply existsb_exists in Hin as [iv [Hiv Hb]].
  apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  pose proof (RefNodes.region_free_In _ a n (fst iv) (snd iv) Hrf ltac:(destruct iv; exact Hiv)) as D. rewrite Un in D. lia.
Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' argH_top HULL_ok RES_len"] Lemma grant_new_facts : forall E cs R FULL model (a n : word) nZ,
  CSOK E cs R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) -> bv_unsigned a + nZ <= alloc_top (m_vmmaps model) ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
    in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = false
    /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
    /\ argH E x = false /\ in_hull A (bv_unsigned x) = false /\ (alloc_top (m_vmmaps model) <=? bv_unsigned x) = false
    /\ VIS E cs model x = false.
Proof.
  intros E cs R FULL model a n nZ HC Hrf Un HnZ Himg HaC x Hx.
  pose proof Hrf as Hrf0.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
  pose proof (region_free_sem _ a n (bv_unsigned x) Hrf2 ltac:(rewrite Un; lia) ltac:(rewrite Un; lia)) as M0.
  assert (N0 : in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false).
  { destruct (in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model))) eqn:En; [|reflexivity]. exfalso.
    apply (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC) in En. congruence. }
  assert (Hh : in_hull A (bv_unsigned x) = false).
  { unfold in_hull. apply andb_false_iff. destruct Himg as [Himg|Himg]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
  assert (Hc : (alloc_top (m_vmmaps model) <=? bv_unsigned x) = false) by (apply Z.leb_gt; lia).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption.
  - destruct (argH E x) eqn:Ea; [|reflexivity]. pose proof (cs_argH_top E cs R FULL model x HC Ea). lia.
  - unfold vis. rewrite Hh, Hc, M0. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="kimg_clip_in_hull' kentry_keep_sem' HULL_ok' RES_len' argH_top SHADOW_val SINV_frame HULL_ok RES_len"] Lemma grant_cs1_ok : forall E cs R FULL model kd (a n : word) nZ model' FULL' sr' R' knew be ne nhi (eager : bool) ylo' nx',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> 0 < nZ -> nZ mod 4096 = 0 -> bv_unsigned a mod 4096 = 0 ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) -> bv_unsigned a + nZ <= alloc_top (m_vmmaps model) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  regs_ok E sr' R' ->
  edenot E be = a -> edenot E ne = n ->
  know_ok SEGS E (MR E cs model' FULL') knew ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false -> nZ <= nhi ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  ylo' <= a_ylo cs ->      (* [comment removed for export] *)
  (forall m, In m (a_maps cs) -> is_hole m = true ->      (* [comment removed for export] *)
     bv_unsigned a + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned a) ->
  let cs1 := add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (a_maps cs)) nx' (AM be ne kd) nhi eager ylo' in
  CSOK E cs1 R' FULL' model'
  /\ (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
        MR E cs1 model' FULL' x = MR E cs model FULL x)
  /\ MR E cs1 model' FULL' = MR E cs model' FULL'.
Proof.
  intros E cs R FULL model kd a n nZ model' FULL' sr' R' knew be ne nhi eager ylo' nx'
         HC Un HnZpos HnZal Hal Himg_a HaC Hrf GPo [GM1 GM2] Hregs Hbase HneE Hknew Hkind Hkfog Hnhi Hbudget Hylo Hholes cs1.
  pose proof (u64_range a) as Ra. pose proof (alloc_top_room (m_vmmaps model)) as HaC'. unfold two_pow_64, stack_max_size in HaC'.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as Hmaps.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (cs_top E cs R FULL model HC) as HTOP.
  pose proof (grant_new_facts E cs R FULL model a n nZ HC Hrf Un HnZpos Himg_a HaC) as NEW.
  (* [comment removed for export] *)
  assert (VISOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    VIS E cs1 model' x = VIS E cs model x).
  { intros x Hx. eapply vis_grant_out; [exact GPo | reflexivity | rewrite Un; lia | exact Hal | rewrite Un; exact HnZal | rewrite Un; exact Hx]. }
  assert (HIDOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    HID E cs1 model' x = HID E cs model x).
  { intros x Hx. unfold hid. rewrite (VISOUT x Hx). reflexivity. }
  assert (MROUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                   MR E cs1 model' FULL' x = MR E cs model FULL x).
  { intros x Hx. unfold Mr, mrestrict. rewrite (HIDOUT x Hx). rewrite (GM1 x) by (rewrite Un; exact Hx). reflexivity. }
  assert (MRSAME : MR E cs1 model' FULL' = MR E cs model' FULL').
  { unfold Mr. rewrite (hid_ext A argH E cs cs1 model') by reflexivity. reflexivity. }
  split; [| split; [exact MROUT | exact MRSAME]].
  (* [comment removed for export] *)
  pose proof (grant_wf kd a n model model' GPo Hwf ltac:(rewrite Un; lia)) as Hwf'.
  assert (HTOPeq : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (unfold alloc_top; rewrite (gp_isp _ _ _ _ _ GPo); reflexivity).
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xsplit Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xtop Xptop Xlzsub Xtophi Xnapos].
  constructor.
  all: unfold cs1, add_entry; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss].
  all: try change (ALLOW E (ACS ?s ?m ?t ?y ?e (a_vis cs) (a_ghost cs) ?ab ?br ?fd ?ti)) with (ALLOW E cs).
  all: rewrite ?HTOPeq.
  - (* [comment removed for export] *) exact Hregs.
  - (* [comment removed for export] *) reflexivity.
  - (* [comment removed for export] *) apply Forall_app. split.
    + unfold cs1, add_entry in MRSAME. cbn [kn a_ss s_know mk_ss] in MRSAME. rewrite MRSAME. exact Hknew.
    + eapply kn_grant_filter_ok; [exact Xknow | exact Hapart | exact Himg_a | lia | exact HnZpos | exact MROUT].
  - (* [comment removed for export] *) rewrite (gp_halted _ _ _ _ _ GPo). exact Xhalt.
  - (* [comment removed for export] *) unfold fds_ok in *. rewrite (gp_fds _ _ _ _ _ GPo), (gp_fs _ _ _ _ _ GPo). exact Xfds.
  - (* [comment removed for export] *) rewrite (gp_fs _ _ _ _ _ GPo). exact Xfs.
  - (* [comment removed for export] *) rewrite (gp_tid _ _ _ _ _ GPo). exact Xtid.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo). exact Xres.
  - (* [comment removed for export] *) rewrite (gp_limit _ _ _ _ _ GPo). exact Xlimit.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). rewrite <- Hbase, <- HneE. apply maps_match_cons; [exact Hkfog | exact Xmaps].
  - (* [comment removed for export] *)
    rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons.
    + intros Hh. exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. destruct kd; cbn in Hkfog, Hh; discriminate.
    + apply Forall_forall. intros m Hm Hk. destruct (proj1 (Forall_forall _ _) Xholes m Hm Hk) as [F1 F2]. split; [|lia].
      intros iv Hiv. apply in_app_iff in Hiv as [Hiv|[<-|Hiv]].
      * apply F1. apply in_app_iff. left. exact Hiv.
      * cbn [fst snd]. rewrite Un. pose proof (Hholes m Hm Hk). lia.
      * apply F1. apply in_app_iff. right. exact Hiv.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). constructor; [|exact Xseps].
    apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
    rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
    pose proof (RefNodes.region_free_In _ a n b s Hrf2 Hin). rewrite Un in *. lia.
  - (* [comment removed for export] *) exact Hwf'.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). apply Forall_cons; [|exact Xbounds]. cbn [fst snd]. rewrite Un. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  - (* [comment removed for export] *) rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [apply Forall_cons; [cbn [fst snd]; rewrite Un; lia|]|]; exact Xlazyb.
  - (* [comment removed for export] *) intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_noacc _ _ _ _ _ GPo) in Hz.
    destruct (kind_none kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
      rewrite (Xnasub z Hz); apply orb_true_r.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind amap_den am_base am_len]. intros Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      replace (kind_none kd) with true by (destruct Hk as [-> | ->]; reflexivity). left. unfold amap_den. cbn [am_base am_len]. rewrite Hbase, HneE. reflexivity.
    + apply Forall_forall. intros m Hm Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk) as X. destruct (kind_none kd); [right|]; exact X.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind am_base am_len]. intros Hk x Hx. subst kd. rewrite Hbase, HneE, Un in Hx. cbn in Hkind.
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). cbn [kind_none kind_lazy]. split.
      * exact (proj1 (proj2 (NEW x Hx))).
      * destruct (page_of_byte_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) Hx) as [P1 P2].
        apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    + apply Forall_forall. intros m Hm Hk x Hx.
      destruct (proj1 (Forall_forall _ _) Xkinds m Hm Hk x Hx) as [K1 K2].
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). split.
      * destruct (kind_none kd); [|exact K1]. rewrite in_ivs_cons. cbn [fst snd]. rewrite K1, Un.
        pose proof (Hapart m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as D.
        replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct D; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * destruct (kind_lazy kd); [|exact K2]. rewrite page_in_ranges_cons, K2. apply orb_true_r.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo).
    rewrite sum_sizes_app in *. cbn [sum_sizes snd]. rewrite Un. cbn [sum_sizes] in Xtotsz. lia.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo). exact Xbrk.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo), (gp_sbrk _ _ _ _ _ GPo). exact Xsbrk.
  - (* [comment removed for export] *) pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
    destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. lia.
  - (* [comment removed for export] *) exact Xabytes.
  - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?(gp_mat _ _ _ _ _ GPo), ?(gp_limit _ _ _ _ _ GPo); try assumption.
    + intros p Hp. rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [rewrite page_in_ranges_cons, (N4 p Hp); apply orb_true_r | exact (N4 p Hp)].
    + pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
      destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. rewrite Xlimit. specialize (Hbudget eq_refl). lia.
  - (* [comment removed for export] *) intros x Hh Hm Hna Hlz Hgh.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [Hlt2|Hge2]].
    + rewrite (GM1 x) by lia. apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [Hm _]. apply Z.leb_le in Hm. cbn [fst] in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
    + (* [comment removed for export] *) rewrite (GM2 x) by (rewrite Un; lia).
      rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [|reflexivity].
      rewrite in_ivs_cons in Hna. cbn [fst snd] in Hna. apply orb_false_iff in Hna as [Hna _].
      apply andb_false_iff in Hna as [Hna|Hna]; [apply Z.leb_gt in Hna | apply Z.ltb_ge in Hna; rewrite Un in Hna]; lia.
    + rewrite (GM1 x) by (rewrite Un; lia). apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [_ Hm]. apply Z.ltb_lt in Hm. cbn [fst snd] in Hm. rewrite Un in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
  - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply GM1.
    pose proof (argH_top _ _ _ Xsinv Hx). rewrite Un. lia.
  - (* [comment removed for export] *) exact Xtop.
  - (* [comment removed for export] *) exact Xptop.
  - (* [comment removed for export] *) intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_lazy _ _ _ _ _ GPo) in Hz.
    destruct (kind_lazy kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
      rewrite (Xlzsub z Hz); apply orb_true_r.
  - (* [comment removed for export] *) exact Xtophi.
  - (* [comment removed for export] *) rewrite (gp_noacc _ _ _ _ _ GPo). destruct (kind_none kd); [|exact Xnapos].
    constructor; [cbn [snd]; rewrite Un; exact HnZpos | exact Xnapos].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma pgup_le : forall x a, x <= a -> a mod 4096 = 0 -> pgup x <= a.
Proof.
  intros x a Hx Ha. unfold pgup.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma fit_lo_sound : forall fuel ivs cur n a nZ,
  (forall iv, In iv ivs -> a + nZ <= fst iv \/ fst iv + snd iv <= a) ->
  n <= nZ -> cur <= a -> a mod 4096 = 0 ->
  fit_lo fuel ivs cur n <= a.
Proof.
  induction fuel as [|f IH]; intros ivs cur n a nZ Hap Hn Hcur Hal; cbn [fit_lo]; [exact Hcur|].
  destruct (List.find _ ivs) as [iv|] eqn:Hf; [|exact Hcur].
  apply find_some in Hf as [Hin Hov]. apply andb_prop in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  apply (IH ivs _ n a nZ Hap Hn); [|exact Hal].
  apply pgup_le; [|exact Hal]. destruct (Hap iv Hin) as [D|D]; lia.
Qed.
#[using="HULL_ok' RES_len' HULL_ok RES_len SEGS"] Lemma lit_ivs_apart : forall E ms (a : word) nZ,
  maps_apart E ms (bv_unsigned a) nZ ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) ->
  forall iv, In iv (lit_ivs A ms) -> bv_unsigned a + nZ <= fst iv \/ fst iv + snd iv <= bv_unsigned a.
Proof.
  intros E ms a nZ Hap Hh iv Hin. unfold lit_ivs in Hin. destruct Hin as [<-|Hin]; [cbn [fst snd]; lia|].
  apply in_flat_map in Hin as [m [Hm Hiv]]. destruct (is_fog m) eqn:Hf; [destruct Hiv|].
  destruct (am_base m) as [b| | | | | | |] eqn:Hb; try (destruct Hiv; fail); try contradiction.
  all: try solve [destruct Hiv].
  destruct (am_len m) as [l| | | | | | |] eqn:Hl; try solve [destruct Hiv].
  match type of Hiv with In iv (if ?c then _ else _) => destruct c eqn:Hg; [|destruct Hiv] end.
  destruct Hiv as [<-|[]]. cbn [fst snd].
  apply andb_prop in Hg as [Hg G3]. apply andb_prop in Hg as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3. unfold two64 in G3.
  pose proof (Hap m Hm Hf) as D. rewrite Hb, Hl in D. cbn [edenot] in D. rewrite !u64_lit in D by lia. exact D.
Qed.
#[using="HULL_ok' RES_len' HULL_ok RES_len SEGS"] Lemma null_vlo_sound : forall E ms (a : word) nZ nlo,
  maps_apart E ms (bv_unsigned a) nZ ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) ->
  nlo <= nZ -> 4096 <= bv_unsigned a -> bv_unsigned a mod 4096 = 0 ->
  null_vlo A ms nlo <= bv_unsigned a / 4096.
Proof.
  intros E ms a nZ nlo Hap Hh Hn Ha Hal. unfold null_vlo.
  apply Z.div_le_mono; [lia|]. eapply fit_lo_sound; [exact (lit_ivs_apart E ms a nZ Hap Hh) | exact Hn | exact Ha | exact Hal].
Qed.

Definition null_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nlo nhi : Z) : acs :=
  let v := nxt cs in
  let base := escale 4096 (EVar v) in
  add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base)
    ((KRange (EVar v) (null_vlo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend base ne nlo
      ++ kdisj_new A (KRange (EVar v) (null_vlo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: kn cs) (a_maps cs) base ne)   (* [comment removed for export] *)
       ++ kn_grant_filter A (kn cs) (a_maps cs))
    (Datatypes.S v) (AM base ne kd) nhi eager (a_ylo cs - 2 * nhi).

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A"] Lemma null_kend_ok : forall E M base ne nlo (a n : word),
  edenot E base = a -> edenot E ne = n ->
  4096 <= bv_unsigned a -> nlo <= bv_unsigned n -> bv_unsigned a + bv_unsigned n <= TOPMAX ->
  know_ok SEGS E M (null_kend base ne nlo).
Proof.
  intros E M base ne nlo a n Hb Hn Hlo Hnlo HaC. unfold null_kend.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn. unfold two64 in *.
  destruct ne; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil;
    cbn [kentry_ok]; unfold eadd; rewrite AX2S.mkAlu_denot; cbn [alu64 alu]; rewrite bv_add_unsigned, Hb, Hn;
    unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64)%Z;
    unfold TOPMAX in *; rewrite Z.mod_small by lia; lia.
Qed.
Lemma null_kend_pure : forall base ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kend base ne nlo).
Proof. intros. unfold null_kend. destruct ne; repeat constructor. Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' SHADOW_val RES_cover SHADOW_ok HULL_ok RES_len"] Lemma kdisj_new_ok : forall E cs R FULL model M Mk k nb ne (a n : word) nZ,
  CSOK E cs R FULL model -> know_ok SEGS E Mk k ->
  edenot E nb = a -> edenot E ne = n -> bv_unsigned n = nZ -> 0 < nZ ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps model) ->
  bv_unsigned a mod 4096 = 0 -> nZ mod 4096 = 0 ->     (* [comment removed for export] *)
  know_ok SEGS E M (kdisj_new A k (a_maps cs) nb ne).
Proof.
  intros E cs R FULL model M Mk k nb ne a n nZ HC HKk Hb Hn Un HnZ Hrf HaC Hal HnZal.
  pose proof (APS.co_ptop _ _ _ _ _ _ _ _ _ _ _ HC) as HPT.
  assert (HaP : bv_unsigned a + nZ <= pagedown (alloc_top (m_vmmaps model))).
  { apply APS.le_pagedown; [rewrite Z.add_mod, Hal, HnZal by lia; reflexivity | exact HaC]. }
  pose proof (pagedown_le (alloc_top (m_vmmaps model))) as HPle.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3). pose proof (u64_range a) as Ra.
  pose proof (free_apart_hull model a n nZ (APS.co_res _ _ _ _ _ _ _ _ _ _ _ HC) Hrf Un HnZ) as HH.
  pose proof (cs_top E cs R FULL model HC) as HTOP.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a n (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (proj1 RES_cover) as HLH.
  pose proof SHADOW_val as SV. unfold APS.shadow_val_ok in SV.
  (first [ pose proof ((APS.co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_27; dand4 dR_27 as _ _ _ Hisp | pose proof (APS.co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Hisp) ]).
  pose proof (alloc_top_ge_of_ceiling _ _ Hisp (Z.le_refl _)) as HCT. rewrite CEIL_eq in HCT. unfold CEIL in HCT.
  pose proof (APS.co_tophi _ _ _ _ _ _ _ _ _ _ _ HC) as HTH. unfold TOPMAX in HTH.
  unfold kdisj_new. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply (proj2 (Forall_app _ _ _)); split; [|apply (proj2 (Forall_app _ _ _)); split]]]].
  - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia). rewrite Hb, Hn, Un. lia.
  - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite !edenot_lit, u64_lit by (unfold BANDLEN; lia). rewrite Hb, Hn, Un.
    unfold uE in HTOP. right. lia.
  - (* [comment removed for export] *)
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite !edenot_lit, u64_lit by (unfold BANDLEN; lia). rewrite Hb, Hn, Un.
    unfold uE in HPT. right. lia.
  - (* [comment removed for export] *)
    destruct (lit_cover (length (a_maps cs)) (a_maps cs) (LOWSH A) KHI) eqn:HLC; [|apply Forall_nil].
    apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off].
    rewrite !edenot_lit, !u64_lit by (unfold LOWSH, KHI; rewrite SV; lia). rewrite Hb, Hn, Un, !Z.add_0_r.
    apply (lit_cover_apart E (a_maps cs) (length (a_maps cs))); [exact HLC | unfold LOWSH, KHI; rewrite SV; lia | exact Hapart | exact HnZ].
  - (* [comment removed for export] *)
    unfold shband_disj.
    destruct (shadow_of A k (eaddz e_pgsp0 (-8388608)) e_band_len) as [[sbB skB] snB] eqn:HsB.   (* [comment removed for export] *)
    destruct (shadow_of A k (ELit (img_lo A)) (ELit (img_hi A - img_lo A))) as [[sbI skI] snI] eqn:HsI.
    destruct (shadow_of A k nb ne) as [[sbN skN] snN] eqn:HsN.
    set (PT := pagedown (alloc_top (m_vmmaps model))) in *.
    assert (HPge : alloc_top (m_vmmaps model) - 4095 <= PT).
    { pose proof (Z.div_mod (alloc_top (m_vmmaps model)) 4096 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound (alloc_top (m_vmmaps model)) 4096 ltac:(lia)) as Hmb. subst PT. unfold pagedown. lia. }
    assert (HPT' : bv_unsigned (edenot E e_pgsp0) = PT + 8388608) by (unfold uE in HPT; lia).
    assert (UB : bv_unsigned (edenot E (eaddz e_pgsp0 (-8388608))) = PT).
    { unfold eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite HPT'.
      replace (-8388608 mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
      replace (PT + 8388608 + (2 ^ 64 - 8388608)) with (PT + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    assert (UL : bv_unsigned (edenot E e_band_len) = 2 ^ 47 - PT).
    { unfold e_band_len, esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite HPT'.
      rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia.
      match goal with |- ?x mod _ = _ => replace x with (2 ^ 47 - PT) by lia end. apply Z.mod_small. lia. }
    (* [comment removed for export] *)
    assert (SH : forall b0 n0 sb sk sn, shadow_of A k b0 n0 = (sb, sk, sn) -> flat_x k sb sk sn = true ->
              estart E (SA sb sk) = bv_unsigned (edenot E b0) / 8 + shadow_off A /\ elenZ E sn = bv_unsigned (edenot E n0) / 8).
    { intros b0 n0 sb sk sn Hs Hf. destruct (APS.shadow_of_val SEGS A SHADOW_ok E Mk k b0 n0 sb sk sn HKk Hs Hf) as [V1 V2].
      split; [|exact V2]. rewrite V1. apply Z.mod_small. pose proof (u64_range (edenot E b0)). rewrite SV.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    apply Forall_app; split; [|apply Forall_app; split].
    + destruct (flat_x k sbB skB snB && flat_x k sbN skN snN)%bool eqn:Hf; [|apply Forall_nil]. apply andb_prop in Hf as [F1 F2].
      apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
      destruct (SH _ _ _ _ _ HsB F1) as [-> ->]. destruct (SH _ _ _ _ _ HsN F2) as [-> ->]. rewrite UB, UL, Hb, Hn, Un.
      right.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + destruct (flat_x k sbI skI snI && flat_x k sbN skN snN)%bool eqn:Hf; [|apply Forall_nil]. apply andb_prop in Hf as [F1 F2].
      apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
      destruct (SH _ _ _ _ _ HsI F1) as [-> ->]. destruct (SH _ _ _ _ _ HsN F2) as [-> ->]. rewrite Hb, Hn, Un.
      rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      destruct HH as [HH|HH]; [right | left]; first [ solve [clear - HH; lia] | lia ].   (* [comment removed for export] *)
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + destruct (has_shadow_maps A (a_maps cs) && flat_x k sbB skB snB)%bool eqn:Hf; [|apply Forall_nil]. apply andb_prop in Hf as [Hsm F1].
      apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
      destruct (SH _ _ _ _ _ HsB F1) as [-> ->]. rewrite UB, UL. unfold estart, elenZ. cbn [a_base a_off]. rewrite Hb, Hn, Un, Z.add_0_r.
      unfold has_shadow_maps in Hsm. apply andb_prop in Hsm as [_ Hsm]. apply existsb_exists in Hsm as [m [Hm Hmm]].
      apply andb_prop in Hmm as [Hmm HL]. apply andb_prop in Hmm as [Hmm HB]. apply andb_prop in Hmm as [Hnf _]. apply negb_true_iff in Hnf.
      apply expr_eqb_eq in HB. apply expr_eqb_eq in HL.
      pose proof (Hapart m Hm Hnf) as D. rewrite HB, HL in D. cbn [edenot] in D. unfold HIGHSH, KHI in D. rewrite SV in D.
      replace (17594333495296 / 8) with 2199291686912 in D by reflexivity.
      rewrite !u64_lit in D by lia. rewrite SV.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      destruct D as [D|D]; [right | left]; first [ solve [clear - D; lia] | lia ].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - apply Forall_flat_map. apply Forall_forall. intros m Hm. destruct (is_fog m) eqn:Hfm; [apply Forall_nil|].
    apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Hb, Hn, Un.
    pose proof (Hapart m Hm Hfm) as D. lia.
Qed.
Lemma kdisj_new_pure : forall k ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new A k ms nb ne).
Proof.
  intros. unfold kdisj_new, shband_disj. repeat (apply Forall_cons; [exact I|]). apply (proj2 (Forall_app _ _ _)); split; [|apply (proj2 (Forall_app _ _ _)); split].
  - destruct (lit_cover _ _ _ _); repeat constructor.
  - destruct (shadow_of A k (eaddz e_pgsp0 (-8388608)) e_band_len) as [[? ?] ?]; destruct (shadow_of A k (ELit (img_lo A)) (ELit (img_hi A - img_lo A))) as [[? ?] ?];
    destruct (shadow_of A k nb ne) as [[? ?] ?].
    repeat (apply Forall_app; split); match goal with |- Forall _ (if ?c then _ else _) => destruct c; repeat constructor end.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.

#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma escale_4096_denot : forall E v (a : word),
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> bv_unsigned a mod 4096 = 0 ->
  edenot E (escale 4096 (EVar v)) = a.
Proof.
  intros E v a Hv Hal. unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite Hv.
  pose proof (u64_range a) as Ra. apply bv_eq. rewrite u_mul64.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite !u64_lit by lia. rewrite Z.mod_small; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="cs_ok_agree' kimg_clip_in_hull' regs_ok_set_n' kentry_keep_sem' reg_lit_sound' reg_sound' HULL_ok' RES_len' argH_top NX0_ok SHADOW_val RES_cover SINV_agree SINV_frame argH_agree SHADOW_ok HULL_ok RES_len"] Lemma mmap_null_cs1 : forall cs kd (eager : bool) ne nlo nhi E R FULL model (a : word) model' FULL',
  CSOK E cs R FULL model ->
  mmap_len cs = Some (ne, nlo, nhi) ->
  fresh_ok nx0 cs = true -> expr_vars_lt (nxt cs) ne = true ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  no_holes (a_maps cs) = true ->      (* [comment removed for export] *)
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  grant_ok_na_pin model a nZ = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  let v := nxt cs in
  let E' := ext1 E v (Z_to_bv 64 (bv_unsigned a / 4096)) in
  let cs1 := null_cs1 cs kd eager ne nlo nhi in
  CSOK E' cs1 (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model'
  /\ edenot E' (escale 4096 (EVar v)) = a /\ edenot E' ne = n /\ bv_unsigned n = nZ
  /\ env_agree nx0 E E'
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
        /\ argH E' x = false /\ in_hull A (bv_unsigned x) = false /\ (alloc_top (m_vmmaps model) <=? bv_unsigned x) = false).
Proof.
  intros cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hnoh len nZ n Hg GPo GM v E' cs1.
  assert (Hnoholes : Forall (fun m => is_hole m = false) (a_maps cs)).
  { unfold no_holes in Hnoh. apply Forall_forall. intros m Hm. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. apply negb_true_iff in X. exact X. }
  (* [comment removed for export] *)
  (first [ pose proof ((mmap_len_sound E cs R FULL model ne nlo nhi HC HML)) as dR_28; dand7 dR_28 as R11 Hlen Hne Hnlo HnZ HnZal HneE | destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE) ]).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof Hg as Hg0.
  unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg Hrf].
  apply andb_prop in Hg as [Hg Hceil]. apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hceil. fold n in Hrf.
  unfold page_size in Hal.
  pose proof (u64_range a) as Ra.
  pose proof (alloc_top_room (m_vmmaps model)) as HTR. unfold two_pow_64, stack_max_size in HTR.
  assert (Un : bv_unsigned n = nZ) by (subst n; apply u64_lit; lia).
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  assert (HnZpos : 0 < nZ) by lia.
  (* [comment removed for export] *)
  pose proof (ext1_agree'' E v (Z_to_bv 64 (bv_unsigned a / 4096))) as Hag. fold E' in Hag.
  (first [ pose proof ((fresh_ok_parts nx0 cs Hfresh)) as dR_29; dand7 dR_29 as Fsr Fkn Fmaps Fvis Fbrk Ffd Fle | destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle) ]). fold v in Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle.
  assert (HC' : CSOK E' cs R FULL model) by (eapply cs_ok_agree'; [exact Hag | exact Hfresh | exact HC]).
  assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le'; [exact Hag | exact Fle]).
  assert (Hv : ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)) by apply ext1_at.
  assert (Hbase : edenot E' (escale 4096 (EVar v)) = a) by (apply escale_4096_denot; assumption).
  assert (HneE' : edenot E' ne = n).
  { rewrite (HneE E'); [exact Hne|]. symmetry. eapply edenot_agree'; [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  pose proof (free_apart_hull model a n nZ (APS.co_res _ _ _ _ _ _ _ _ _ _ _ HC') Hrf Un HnZpos) as Himg_a.
  pose proof Hceil as HaC.
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC') as Hmaps.
  pose proof (maps_apart_of_region_free E' (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (grant_new_facts E' cs R FULL model a n nZ HC' Hrf Un HnZpos Himg_a HaC) as NEW.
  pose proof (cs_top E' cs R FULL model HC') as HTOP'.
  (* [comment removed for export] *)
  (first [ pose proof ((grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
              (sr_upd (s_regs (a_ss cs)) 10 (escale 4096 (EVar v))) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
              (KRange (EVar v) (null_vlo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend (escale 4096 (EVar v)) ne nlo
                ++ kdisj_new A (KRange (EVar v) (null_vlo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: kn cs) (a_maps cs) (escale 4096 (EVar v)) ne)
              (escale 4096 (EVar v)) ne nhi eager (a_ylo cs - 2 * nhi) (Datatypes.S v)
              HC' Un HnZpos HnZal Hal Himg_a HaC Hrf GPo GM)) as dR_30; dand3 dR_30 as HC1 MROUT MRSAME | destruct (grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
              (sr_upd (s_regs (a_ss cs)) 10 (escale 4096 (EVar v))) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
              (KRange (EVar v) (null_vlo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend (escale 4096 (EVar v)) ne nlo
                ++ kdisj_new A (KRange (EVar v) (null_vlo A (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: kn cs) (a_maps cs) (escale 4096 (EVar v)) ne)
              (escale 4096 (EVar v)) ne nhi eager (a_ylo cs - 2 * nhi) (Datatypes.S v)
              HC' Un HnZpos HnZal Hal Himg_a HaC Hrf GPo GM) as (HC1 & MROUT & MRSAME) ]).
  - apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | exact Hbase].
  - exact Hbase.
  - exact HneE'.
  - (* [comment removed for export] *)
    apply Forall_cons; [|apply Forall_app; split].
    + (* [comment removed for export] *) cbn [kentry_ok edenot]. rewrite Hv.
      pose proof (APS.co_tophi _ _ _ _ _ _ _ _ _ _ _ HC') as HTH.
      pose proof (null_vlo_sound E' (a_maps cs) a nZ nlo Hapart Himg_a) as HVLO.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite u64_lit by lia. unfold TOPMAX in *. split; [apply HVLO; lia | lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + (* [comment removed for export] *)
      pose proof (APS.co_tophi _ _ _ _ _ _ _ _ _ _ _ HC') as HTH.
      eapply null_kend_ok; [exact Hbase | exact HneE' | | rewrite Un; lia | rewrite Un; unfold TOPMAX in *; lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hal Hpos Ra. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + (* [comment removed for export] *) eapply kdisj_new_ok; [exact HC' | | exact Hbase | exact HneE' | exact Un | exact HnZpos | exact Hrf | exact HaC | exact Hal | exact HnZal].
      apply Forall_cons; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC')].
      cbn [kentry_ok edenot]. rewrite Hv.
      pose proof (APS.co_tophi _ _ _ _ _ _ _ _ _ _ _ HC') as HTH.
      pose proof (null_vlo_sound E' (a_maps cs) a nZ nlo Hapart Himg_a) as HVLO.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite u64_lit by lia. unfold TOPMAX in *. split; [apply HVLO; lia | lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - cbn [a_ylo]. lia.
  - intros m Hm Hk. exfalso. pose proof (proj1 (Forall_forall _ _) Hnoholes m Hm) as X. congruence.
  - split; [exact HC1|]. split; [exact Hbase|]. split; [exact HneE'|]. split; [exact Un|]. split; [exact Hag0|].
    intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_31; dand6 dR_31 as N0 N1 N2 N3 N4 _ | destruct (NEW x Hx) as (N0 & N1 & N2 & N3 & N4 & _) ]).
    split; [|auto]. rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A"] Lemma kmem_ok : forall E M b ne (lo n : Z),
  estart E (SA b 0) = lo -> elenZ E ne = n -> 0 <= lo < 2 ^ 64 -> 0 <= n -> lo + n <= 2 ^ 64 ->
  (forall x : word, lo <= bv_unsigned x < lo + n -> M x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M [KWr (SA b 0) ne; KZero (SA b 0) ne].
Proof.
  intros E M b ne lo n Hs Hn Hlo Hn0 Hhi BYTE.
  assert (Hfl : flat E (SA b 0) (elenZ E ne)) by (unfold flat; rewrite Hs, Hn; lia).
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; rewrite ?Hs, ?Hn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by lia. lia.
Qed.

Lemma kimg_in_hull_pure : forall k,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) k -> kimg_in_hull A k.
Proof.
  intros k H. unfold kimg_in_hull. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) H K Hin) as HK. destruct K; try exact I. destruct HK.
Qed.

(* [comment removed for export] *)
#[using="H_off_segments_cs' hid_hull' know_ok_unhide' vis_add_sound' HULL_ok' RES_len' XB XE XN HS argH_top SHADOW_val argH_high SHADOW_ok HULL_ok RES_len SEGS_in_hull"] Lemma grant_vis_add : forall E cs1 cs2 base ne R FULL model (a n : word) nZ,
  CSOK E cs1 R FULL model ->
  vis_add A LIMIT cs1 base ne ([KWr (SA base 0) ne; KZero (SA base 0) ne] ++ kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  edenot E base = a -> edenot E ne = n -> bv_unsigned n = nZ -> 0 <= nZ -> bv_unsigned a + nZ <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
     /\ argH E x = false) ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ -> FULL x = Some (Z_to_bv 8 0)) ->
  CSOK E cs2 R FULL model.
Proof.
  intros E cs1 cs2 base ne R FULL model a n nZ HC1 Hva Hkh Hbase Hne Un HnZ Hhi NEW ZERO.
  pose proof (u64_range a) as Ra.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  (first [ pose proof ((vis_add_inv cs1 base ne _ cs2 Hva)) as dR_32; dex1 dR_32 as nhi; destruct dR_32 as [Hnhi Ecs2] | pose proof ((vis_add_inv cs1 base ne _ cs2 Hva)) as dR_32; dand3 dR_32 as nhi Hnhi Ecs2 | destruct (vis_add_inv cs1 base ne _ cs2 Hva) as (nhi & Hnhi & Ecs2) ]).
  apply Forall_app. split.
  - (* [comment removed for export] *)
    eapply (kmem_ok E _ base ne (bv_unsigned a) nZ); [unfold estart; cbn [a_base a_off]; rewrite Hbase; lia | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
    intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_33; dand3 dR_33 as N1 N2 N3 | destruct (NEW x Hx) as (N1 & N2 & N3) ]).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
    unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
  - (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="RES_len' RES_len A SEGS"] Lemma gap_weight_eq : forall nZ l, gap_weight nZ l = sum_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof. induction l as [|[b sz] l IH]; cbn -[Z.of_nat Z.add Z.mul]; [lia|]. rewrite IH. rewrite Nat2Z.inj_succ. cbn [snd]. lia. Qed.

(* [comment removed for export] *)
#[using="SHADOW_ok' HULL_ok' RES_len' SHADOW_ok HULL_ok RES_len"] Lemma gap_ok_sound : forall E cs R FULL model nhi nZ,
  CSOK E cs R FULL model -> gap_ok A cs nhi = true -> 0 <= nZ <= nhi ->
  exists a : word, grant_ok_na (Z_to_bv 64 0) model a nZ = true.
Proof.
  intros E cs R FULL model nhi nZ HC Hg HnZ. unfold gap_ok in Hg. apply Z.leb_le in Hg.
  pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as T.
  assert (L : (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= n_res A + length (a_maps cs))%nat).
  { rewrite length_app, (co_res _ _ _ _ _ _ _ _ _ _ _ HC), RES_len'. pose proof (maps_match_length E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). lia. }
  assert (GW : gw_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs).
  { pose proof (gap_weight_sizes nZ (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) as G1.
    rewrite gap_weight_eq in G1. lia. }
  (first [ pose proof ((free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW)) as dR_34; dex1 dR_34 as g; dand5 dR_34 as Hal Hfl Hc Hfree Hpl | pose proof ((free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW)) as dR_34; dand6 dR_34 as g Hal Hfl Hc Hfree Hpl | destruct (free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW) as (g & Hal & Hfl & Hc & Hfree & Hpl) ]).
  { rewrite FLOOR_eq, CEIL_eq.
    assert (0 <= a_totsz cs).
    { assert (0 <= sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))); [|lia].
      clear. induction (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) as [|[b sz] l IH]; cbn; [lia|]. pose proof (u64_range sz). lia. }
    set (len1 := length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) in *.
    set (len2 := (n_res A + length (a_maps cs))%nat) in *.
    assert (Z.of_nat len1 * (nZ + 4095) <= Z.of_nat len2 * (nhi + 4095)) by nia. nia. }
  pose proof bottomup_floor_val as Hfv. pose proof alloc_ceiling_val as Hcv.
  assert (Hg64 : 0 <= g < 2 ^ 64) by lia.
  exists (Z_to_bv 64 g). unfold grant_ok_na. rewrite u64_lit by lia.
  rewrite Hfree, Hpl. unfold page_size in Hal |- *.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite (proj2 (Z.ltb_lt 0 g)) by lia. rewrite (proj2 (Z.leb_le _ _) Hc). reflexivity.
Qed.

#[using="A_wf_allowA' HULL_ok' RES_len' XB XE XN HS HULL_ok RES_len"] Lemma budget_slack : forall E cs R FULL model extra,
  CSOK E cs R FULL model -> budget_ok LIMIT cs extra = true ->
  vm_backing_used model + extra <= vm_limit (m_vmmaps model).
Proof.
  intros E cs R FULL model extra HC Hb. unfold budget_ok in Hb. apply Z.leb_le in Hb.
  pose proof (vm_backing_used_le (ALLOW E cs) model (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (A_wf_allowA' E cs)).
  pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC).
  rewrite (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.

Lemma lazy_interior_fresh : forall (a n : word),
  bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> lazy_interior a n = [(a, n)].
Proof. intros. apply lazy_interior_aligned; unfold page_size; assumption. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refuse_eq : forall cs,
  refuse cs = with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs (a_ss cs)) 10 (ELit ENOMEM_RET)) (kn cs) (nxt cs)).
Proof. reflexivity. Qed.

Lemma refuse_pc : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

#[using="cs_ok_frame' regs_ok_set_n' RES_len' SINV_frame RES_len"] Lemma refuse_ok : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  CSOK E (refuse cs) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model.
Proof.
  intros E cs R FULL model HC. rewrite refuse_eq.
  eapply cs_ok_frame'; [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
  cbn [s_regs mk_ss]. apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia |].
  cbn [edenot]. rewrite errno_ret_ENOMEM. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="cs_ok_frame' regs_ok_set_n' RES_len' SINV_frame RES_len"] Lemma refuse_cont : forall cs E R FULL model TA,
  CSOK E cs R FULL model -> 0 <= pc cs -> pc cs + 4 < 2 ^ 64 ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (refuse cs) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc (refuse cs)) FULL' model') TA) ->
  srealizes SEGS (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA.
Proof.
  intros cs E R FULL model TA HC Hp0 Hp4 HKA.
  specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
                  (conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
  unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="RES_len' RES_len A"] Lemma page_aligned_sound : forall E M k e,
  know_ok SEGS E M k -> page_aligned k e = true -> bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
  intros E M k e HK H.
  assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
  { intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr [q Hq]]. rewrite Hq.
    replace (2 ^ ealign k e) with (2 ^ (ealign k e - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
    rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
  unfold page_aligned in H. destruct e as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact H).
  apply Z.eqb_eq in H. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.mod_mod_divide; [exact H | exists (2 ^ 52); reflexivity].
Qed.

#[using="reg_sound' HULL_ok' RES_len' HULL_ok RES_len"] Lemma fixed_args_sound : forall E cs R FULL model top b off ne nlo nhi,
  CSOK E cs R FULL model -> fixed_args A cs top = Some (b, off, ne, nlo, nhi) ->
  split_lit (reg cs 10) = (b, off) /\ mmap_len cs = Some (ne, nlo, nhi)
  /\ bv_unsigned (edenot E (reg cs 10)) mod 4096 = 0
  /\ 0 < bv_unsigned (edenot E (reg cs 10))
  /\ img_hi A <= bv_unsigned (edenot E (reg cs 10))
  /\ bv_unsigned (edenot E (reg cs 10)) + nhi <= top
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = edenot E (reg cs 10)
  /\ flat_x (kn cs) b off ne = true.
Proof.
  intros E cs R FULL model top b off ne nlo nhi HC H. unfold fixed_args in H.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Himg. apply Z.leb_le in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

(* [comment removed for export] *)
#[using="reg_sound' HULL_ok' RES_len' HULL_ok RES_len"] Lemma fixed_args_in_sound : forall E cs R FULL model b off ne nlo nhi,
  CSOK E cs R FULL model -> fixed_args_in cs = Some (b, off, ne, nlo, nhi) ->
  split_lit (reg cs 10) = (b, off) /\ mmap_len cs = Some (ne, nlo, nhi)
  /\ bv_unsigned (edenot E (reg cs 10)) mod 4096 = 0
  /\ 0 < bv_unsigned (edenot E (reg cs 10))
  /\ bv_unsigned (edenot E (reg cs 10)) + nhi < two64
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = edenot E (reg cs 10)
  /\ flat_x (kn cs) b off ne = true.
Proof.
  intros E cs R FULL model b off ne nlo nhi HC H. unfold fixed_args_in in H.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.ltb_lt in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A"] Lemma split_flat_estart : forall E M k e b off n,
  know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
  estart E (SA b off) = bv_unsigned (edenot E e)
  /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  (first [ pose proof ((APS.flat_x_sound SEGS E M k b off n HK Hfl)) as dR_35; dand3 dR_35 as F1 F2 F3 | destruct (APS.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3) ]).
  pose proof (APS.u_of_split E e b off Hsp ltac:(lia)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

(* [comment removed for export] *)
#[using="maps_match_exact' RES_hullH HULL_ok' RES_len' XB XE XN HS HULL_ok RES_hull RES_len nx0"] Lemma region_free_of_apart : forall E cs R FULL model b off ne (lo n : word),
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  estart E (SA b off) = bv_unsigned lo -> elenZ E ne = bv_unsigned n ->
  img_hi A <= bv_unsigned lo ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) lo n = true.
Proof.
  intros E cs R FULL model b off ne lo n HC Hnf Hall Hs Hn Himg.
  rewrite region_free_app. apply andb_true_intro. split.
  - apply reserved_free_above; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg].
  - rewrite (proj1 (maps_match_exact' E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). apply RefNodes.region_free_intro. intros bm sm Hin.
    apply in_map_iff in Hin as (m & Hm & Hinm). unfold amap_den in Hm. injection Hm as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hall m Hinm) as Hap.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D, Hn. rewrite Hs, Hn in D. lia.
Qed.

Definition fixed_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nhi : Z) : acs :=
  let k := kn cs in
  let m := AM (reg cs 10) ne kd in
  let ksh := if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A k [m] (fst p) (snd p)) (a_vis cs) else [] in
  add_entry cs (s_regs (a_ss cs)) (ksh ++ kn_grant_filter A k (a_maps cs)) (nxt cs) m nhi eager (a_ylo cs).

(* [comment removed for export] *)
#[using="SHADOW_ok' HULL_ok' RES_len' SHADOW_ok HULL_ok RES_len"] Lemma shadow_facts_new_ok : forall E cs R FULL model (a n : word) nZ ne model' FULL',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> edenot E ne = n -> bv_unsigned a + nZ <= CEIL -> edenot E (reg cs 10) = a ->
  grant_post KRWLAZY a n model model' -> grant_mem KRWLAZY a n FULL FULL' ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false) ->
  know_ok SEGS E (MR E cs model' FULL')
    (flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) (snd p)) (a_vis cs)).
Proof.
  intros E cs R FULL model a n nZ ne model' FULL' HC Un Hne HaC Hra GPo [GM1 GM2] NEW.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (u64_range a) as Ra. pose proof SHADOW_ok' as SO.
  unfold know_ok. apply Forall_flat_map. apply Forall_forall. intros p Hp.
  unfold shadow_facts.
  destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  destruct (find_containing (kn cs) [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn) as [m|] eqn:Hf.
  2: { (* [comment removed for export] *)
       destruct (split_lit (fst p)) as [bb bk].
       destruct (band_split A (kn cs) [AM (reg cs 10) ne KRWLAZY] bb bk (snd p) sb sk sn) eqn:HB; [|constructor]. exfalso.
       unfold band_split, has_shadow_maps in HB.
       apply andb_prop in HB as [HB _]. apply andb_prop in HB as [HB _]. apply andb_prop in HB as [HB _]. apply andb_prop in HB as [HL HH].
       cbn [existsb am_base am_len am_kind] in HL, HH. rewrite orb_false_r in HL, HH.
       apply andb_prop in HL as [HL _]. apply andb_prop in HL as [_ HL]. apply andb_prop in HH as [HH _]. apply andb_prop in HH as [_ HH].
       apply expr_eqb_eq in HL. apply expr_eqb_eq in HH. rewrite HL in HH. injection HH as HH'.
       pose proof SHADOW_ok' as SO'. unfold LOWSH, HIGHSH, KHI in HH'. lia. }
  unfold find_containing in Hf. cbn [find] in Hf.
  match type of Hf with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [_ Hins]. cbn [am_base am_len] in Hins.
  pose proof (APS.xinsideX_sound SEGS E _ (kn cs) sb sk sn (reg cs 10) 0 ne HK Hins) as [I1 I2].   (* [comment removed for export] *)
  unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. rewrite Z.add_0_r in I1, I2. unfold elenZ in I2. rewrite Hne, Un in I2. rewrite Hra in I1, I2.
  pose proof HaC as HaC'. unfold CEIL in HaC'.
  (* [comment removed for export] *)
  unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl (kn cs) (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
  assert (Usn : bv_unsigned (edenot E (mkSrl (kn cs) (snd p) 3)) = bv_unsigned (edenot E (snd p)) / 8).
  { rewrite (mkSrl_denot SEGS E _ (kn cs) (snd p) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  rewrite Usn in I2.
  set (S0 := bv_unsigned (edenot E sb) + sk) in *.
  pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
  pose proof (u64_range (edenot E (mkSrl (kn cs) (snd p) 3))) as Rsn.
  assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E (fst p)) / 8).
  { pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
    apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
    rewrite (mkSrl_denot SEGS E _ (kn cs) (fst p) 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64 in D. fold S0 in D.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite !u64_lit in D by (unfold CEIL in *; lia).
    change (2 ^ (3 mod 64)) with 8 in D.
    rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (unfold CEIL in *; lia).
    unfold CEIL in *. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (BYTE : forall y : word, S0 <= bv_unsigned y < S0 + bv_unsigned (edenot E (snd p)) / 8 ->
            MR E cs model' FULL' y = Some (Z_to_bv 8 0)).
  { intros y Hy.
    assert (Hya : bv_unsigned a <= bv_unsigned y < bv_unsigned a + nZ) by (clear -Hy I1 I2; lia).
    destruct (NEW y Hya) as [N1 N2].
    assert (Hsh2 : in_sh A E cs (bv_unsigned y) = true).
    { unfold in_sh. apply existsb_exists. exists p. split; [exact Hp|]. unfold sh_lo, sh_hi, uE.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
      - lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (V : VIS E cs model' y = true).
    { unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo). cbn [kind_none].
      rewrite in_ivs_cons. cbn [fst snd]. rewrite Un, N1.
      rewrite (proj2 (Z.leb_le (bv_unsigned a) (bv_unsigned y))) by lia.
      rewrite (proj2 (Z.ltb_lt (bv_unsigned y) (bv_unsigned a + nZ))) by lia.
      unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. cbn [andb orb negb]. rewrite ?orb_true_r. reflexivity. }
    unfold Mr, mrestrict, hid. rewrite N2, V. cbn [orb negb].
    rewrite (GM2 y) by (rewrite Un; exact Hya). reflexivity. }
  assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) (snd p) 3))).
  { unfold flat, estart, elenZ. cbn [a_base a_off]. fold S0. rewrite Usn. unfold CEIL in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl;
    unfold estart, elenZ; cbn [a_base a_off]; fold S0; rewrite Usn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in *; lia); unfold CEIL in *; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in *; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in *; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="reg_lit_sound' reg_sound' HULL_ok' RES_len' HULL_ok RES_len"] Lemma fixed_pre : forall cs top b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  edenot E ne = n /\ bv_unsigned n = nZ /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr /\ img_hi A <= bv_unsigned addr
  /\ bv_unsigned addr + nZ <= top
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ nZ mod 4096 = 0 /\ 0 < nZ <= nhi.
Proof.
  intros cs top b off ne nlo nhi E R FULL model HC HFA Htop addr len nZ n.
  (first [ pose proof ((fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA)) as dR_36; dand8 dR_36 as Hsp HML Hal Hpos Himg HtopA R10 Hflat | destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & HtopA & R10 & Hflat) ]).
  fold addr in Hal, Hpos, Himg, HtopA, R10.
  (first [ pose proof ((mmap_len_sound E cs R FULL model ne nlo nhi HC HML)) as dR_37; dand7 dR_37 as R11 Hlen Hne Hnlo HnZ HnZal HneE | destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE) ]).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  (first [ pose proof ((split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat)) as dR_38; dand3 dR_38 as Hest Hfl2 Hfl3 | destruct (split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat) as (Hest & Hfl2 & Hfl3) ]). fold addr in Hest.
  pose proof (u64_range addr) as Ra.
  assert (Un0 : bv_unsigned n = nZ).
  { subst n. apply u64_lit. split; [lia|]. pose proof (u64_range (Z_to_bv 64 nZ)) as Rn. unfold CEIL in Htop. lia. }
  split; [exact Hne|]. split; [exact Un0|]. split; [exact Hest|]. split; [exact Hal|]. split; [exact Hpos|].
  split; [exact Himg|]. split; [lia|]. split; [exact R10|]. split; [exact HnZal | lia].
Qed.

(* [comment removed for export] *)
#[using="SHADOW_ok' HULL_ok' SHADOW_ok HULL_ok A"] Lemma maps_match_unhole : forall E ms h l, maps_match E ms l <-> maps_match E (unhole ms h) l.
Proof.
  intros E ms h. unfold unhole. induction ms as [|m ms IH]; intros l; [cbn; tauto|].
  cbn [List.map maps_match].
  destruct (is_hole m && amap_eqb m h)%bool eqn:Hc.
  - apply andb_prop in Hc as [Hh _].
    assert (Hf : is_fog m = true) by (unfold is_fog, is_hole in *; destruct (am_kind m); cbn in Hh |- *; congruence).
    rewrite Hf. cbn [is_fog is_tok_kind am_kind am_len].
    split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
  - destruct (is_fog m).
    + split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
    + split; (((first [ intro dR_77; dex1 dR_77 as l'; destruct dR_77 as [H1 H2] | intro dR_77; dand3 dR_77 as l' H1 H2 | intros (l' & H1 & H2) ])); exists l'; split; [exact H1 | apply IH; exact H2]).
Qed.

(* [comment removed for export] *)
#[using="RES_len' RES_len A"] Lemma same_val_sound : forall E M k a b,
  know_ok SEGS E M k -> same_val k a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E M k a b HK H. unfold same_val in H.
  destruct (expr_eqb a b) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
  destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as X2.
  cbn [xt_den] in X1, X2. lia.
Qed.

(* [comment removed for export] *)
#[using="RES_len' RES_len A"] Lemma find_hole_sound : forall E M k ms a ne h,
  know_ok SEGS E M k -> find_hole k ms a ne = Some h ->
  In h ms /\ is_hole h = true
  /\ uE E (am_base h) = bv_unsigned (edenot E a) /\ uE E (am_len h) = bv_unsigned (edenot E ne).
Proof.
  intros E M k ms a ne h HK H. unfold find_hole in H. apply find_some in H as [Hin Hc].
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hh H1].
  split; [exact Hin|]. split; [exact Hh|]. unfold uE.
  split; symmetry; [exact (same_val_sound E M k _ _ HK H1) | exact (same_val_sound E M k _ _ HK H2)].
Qed.

(* [comment removed for export] *)
#[using="SHADOW_ok' HULL_ok' SHADOW_ok HULL_ok"] Lemma cs_ok_unhole : forall E cs R FULL model h,
  CSOK E cs R FULL model -> CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model.
Proof.
  intros E cs R FULL model h HC.
  assert (ELEM : forall m, In m (unhole (a_maps cs) h) ->
            In m (a_maps cs) \/ exists m0, In m0 (a_maps cs) /\ m = AM (am_base m0) (am_len m0) KFOG).
  { intros m Hm. unfold unhole in Hm. apply in_map_iff in Hm as (m0 & Hm0 & Hin).
    destruct (is_hole m0 && amap_eqb m0 h)%bool; [right; exists m0; split; [exact Hin | symmetry; exact Hm0] | left; subst; exact Hin]. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xsplit Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv].
  constructor; unfold with_maps0 in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply (proj1 (maps_match_unhole E _ h _)). exact Xmaps.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xholes m Hin Hk) | cbn in Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xnone m Hin Hk) | cbn in Hk; destruct Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xkinds m Hin Hk) | cbn in Hk; discriminate].
Qed.

(* [comment removed for export] *)
#[using="kimg_clip_in_hull' kentry_keep_sem' reg_lit_sound' reg_sound' SHADOW_ok' HULL_ok' RES_len' argH_top SHADOW_val SINV_frame SHADOW_ok HULL_ok RES_len"] Lemma mmap_fixed_grant_cs1 : forall cs ms0 kd (eager : bool) top b off ne nlo nhi E R FULL model model' FULL',
  CSOK E cs R FULL model ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr) ->
  (bv_unsigned addr + nZ <= KHI \/ a_ylo cs <= bv_unsigned addr) ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' ->
  CSOK E (fixed_cs1 (with_maps0 cs ms0) kd eager ne nhi) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model'
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false).
Proof.
  intros cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 addr len nZ n Hrf Hholes Hside Hbudget Hkind Hkfog GPo GM.
  (first [ pose proof ((fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop)) as dR_39; dand10 dR_39 as Hne Un Hest Hal Hpos Himg HtopA R10 HnZal HnZ | destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ) ]).
  fold addr len nZ n in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaC : bv_unsigned addr + nZ <= CEIL) by lia.
  assert (HnZpos : 0 < nZ) by lia.
  (* [comment removed for export] *)
  (first [ pose proof ((co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_40; dand4 dR_40 as _ _ _ Hisp | pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Hisp) ]).
  assert (HaT : bv_unsigned addr + nZ <= alloc_top (m_vmmaps model)) by (apply (alloc_top_ge_of_ceiling _ _ Hisp); rewrite CEIL_eq; exact HaC).
  assert (HimgD : bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr) by (right; exact Himg).
  pose proof (grant_new_facts E cs R FULL model addr n nZ HC Hrf Un HnZpos HimgD HaT) as NEW.
  (first [ pose proof ((grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
              (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
              (if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne kd] (fst p) (snd p)) (a_vis cs) else [])
              (reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
              HC0 Un HnZpos HnZal Hal HimgD HaT Hrf GPo GM)) as dR_41; dand3 dR_41 as HC1 MROUT MRSAME | destruct (grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
              (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
              (if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne kd] (fst p) (snd p)) (a_vis cs) else [])
              (reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
              HC0 Un HnZpos HnZal Hal HimgD HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME) ]).
  - apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | exact R10].
  - reflexivity.
  - exact Hne.
  - destruct kd; cbn [mkind_eqb]; try constructor.
    change (MR E (with_maps0 cs ms0) model' FULL') with (MR E cs model' FULL').
    eapply shadow_facts_new_ok; [exact HC | exact Un | exact Hne | exact HaC | reflexivity | exact GPo | exact GM |].
    intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_42; dand4 dR_42 as _ N1 N2 _ | destruct (NEW x Hx) as (_ & N1 & N2 & _) ]). auto.
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - cbn [with_maps0 a_ylo]. lia.
  - cbn [with_maps0 a_maps]. exact Hholes.
  - split; [exact HC1|].
    intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_43; dand4 dR_43 as N0 N1 N2 _ | destruct (NEW x Hx) as (N0 & N1 & N2 & _) ]). split; [|auto].
    rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
#[using="maps_match_exact' reg_lit_sound' reg_sound' RES_hullH HULL_ok' RES_len' XB XE XN HS HULL_ok RES_hull RES_len nx0"] Lemma mmap_fixed_old_facts : forall cs b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs KHI = Some (b, off, ne, nlo, nhi) ->
  no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  let addr := edenot E (reg cs 10) in
  let nZ := page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) in
  CSOK E (with_maps0 cs (a_maps cs)) R FULL model
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr (Z_to_bv 64 nZ) = true
  /\ (forall m, In m (a_maps cs) -> is_hole m = true ->
        bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr)
  /\ (bv_unsigned addr + nZ <= KHI \/ a_ylo cs <= bv_unsigned addr).
Proof.
  intros cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall addr nZ.
  (first [ pose proof ((fixed_pre cs KHI b off ne nlo nhi E R FULL model HC HFA ltac:(unfold KHI, CEIL; lia))) as dR_44; dand10 dR_44 as Hne Un Hest Hal Hpos Himg HtopA R10 HnZal HnZ | destruct (fixed_pre cs KHI b off ne nlo nhi E R FULL model HC HFA ltac:(unfold KHI, CEIL; lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ) ]).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  split; [|split; [|split]].
  - destruct cs; exact HC.
  - eapply region_free_of_apart; [exact HC | exact Hnf | exact Hall | exact Hest | unfold elenZ; rewrite Hne; reflexivity | exact Himg].
  - intros m Hm Hk. exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X.
    apply negb_true_iff in X. unfold is_fog, is_hole in *. destruct (am_kind m); cbn in X, Hk; congruence.
  - left. exact HtopA.
Qed.

(* [comment removed for export] *)
#[using="reg_lit_sound' reg_sound' SHADOW_ok' HULL_ok' RES_len' SHADOW_ok HULL_ok RES_len"] Lemma mmap_fixed_hole_facts : forall cs b off ne nlo nhi h E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs CEIL = Some (b, off, ne, nlo, nhi) ->
  find_hole (kn cs) (a_maps cs) (reg cs 10) ne = Some h ->
  forallb (fun m => negb (is_hole m) || ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (unhole (a_maps cs) h) = true ->
  let addr := edenot E (reg cs 10) in
  let nZ := page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) in
  CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr (Z_to_bv 64 nZ) = true
  /\ (forall m, In m (unhole (a_maps cs) h) -> is_hole m = true ->
        bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr)
  /\ (bv_unsigned addr + nZ <= KHI \/ a_ylo cs <= bv_unsigned addr).
Proof.
  intros cs b off ne nlo nhi h E R FULL model HC HFA Hfh Hap addr nZ.
  (first [ pose proof ((fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia))) as dR_45; dand10 dR_45 as Hne Un Hest Hal Hpos Himg HtopA R10 HnZal HnZ | destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ) ]).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  (first [ pose proof ((find_hole_sound E _ (kn cs) (a_maps cs) (reg cs 10) ne h HK Hfh)) as dR_46; dand4 dR_46 as Hin Hh Hhb Hhn | destruct (find_hole_sound E _ (kn cs) (a_maps cs) (reg cs 10) ne h HK Hfh) as (Hin & Hh & Hhb & Hhn) ]).
  fold addr in Hhb. rewrite Hne, Un in Hhn.
  destruct (proj1 (Forall_forall _ _) (co_holes _ _ _ _ _ _ _ _ _ _ _ HC) h Hin Hh) as [F1 F2].
  rewrite Hhb, Hhn in F1, F2.
  split; [apply cs_ok_unhole; exact HC|]. split; [|split].
  - apply RefNodes.region_free_intro. intros b' s' Hin'. rewrite Un. destruct (F1 (b', s') Hin'); cbn [fst snd] in *; lia.
  - intros m Hm Hk. pose proof (proj1 (forallb_forall _ _) Hap m Hm) as X. cbn beta in X. rewrite Hk in X. cbn [negb orb] in X.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) HK X) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D. rewrite Hest, Hne, Un in D. unfold uE. lia.
  - exact F2.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RES_len' RES_len A SEGS"] Lemma seps_map_disjoint : forall (f : amap -> word * word) ms m m',
  seps (map f ms) -> In m ms -> In m' ms -> m <> m' -> iv_disjoint (f m) (f m').
Proof.
  intros f ms. induction ms as [|h t IH]; intros m m' Hs Hm Hm' Hne; [destruct Hm|].
  cbn [map] in Hs. inversion Hs as [|p l Hf Hl]; subst.
  destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf (f m') (in_map f t m' Hm')).
  - pose proof (proj1 (Forall_forall _ _) Hf (f m) (in_map f t m Hm)) as D. unfold iv_disjoint in *. lia.
  - exact (IH m m' Hl Hm Hm' Hne).
Qed.

(* [comment removed for export] *)
#[using="RES_len' RES_len A SEGS"] Lemma maps_match_disjoint : forall E ms l m m',
  maps_match E ms l -> seps l -> In m ms -> In m' ms -> is_fog m = false -> is_fog m' = false -> m <> m' ->
  iv_disjoint (amap_den E m) (amap_den E m').
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m m' HM Hs Hm Hm' Hf Hf' Hne; [destruct Hm|].
  cbn [maps_match] in HM. destruct (is_fog h) eqn:Hfh.
  - assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    assert (Hmt' : In m' t) by (destruct Hm' as [<-|Hm']; [congruence | exact Hm']).
    destruct HM as [HM|(iv & l' & -> & _ & HM)].
    + exact (IH l m m' HM Hs Hmt Hmt' Hf Hf' Hne).
    + inversion Hs as [|p l0 Hfa Hl]; subst. exact (IH l' m m' HM Hl Hmt Hmt' Hf Hf' Hne).
  - (first [ dex1 HM as l'; destruct HM as [-> HM] | dand3 HM as l' -> HM | destruct HM as (l' & -> & HM) ]). inversion Hs as [|p l0 Hfa Hl]; subst.
    destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
    + exfalso. exact (Hne eq_refl).
    + exact (proj1 (Forall_forall _ _) Hfa (amap_den E m') (maps_match_In E t l' m' HM Hm' Hf')).
    + pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hm Hf)) as D. unfold iv_disjoint in *. lia.
    + exact (IH l' m m' HM Hl Hm Hm' Hf Hf' Hne).
Qed.

(* [comment removed for export] *)
#[using="HULL_ok' RES_len' HULL_ok RES_len A SEGS"] Lemma overlap_sum_contained : forall l (b s : word) lo hi,
  seps l -> In (b, s) l -> bv_unsigned b <= lo -> hi <= bv_unsigned b + bv_unsigned s -> lo <= hi ->
  overlap_sum l lo hi <= hi - lo.
Proof.
  intros l b s lo hi Hs Hin H1 H2 Hlh. induction l as [|p l IH]; [destruct Hin|].
  inversion Hs as [|p' l' Hf Hl]; subst. rewrite overlap_sum_cons. destruct Hin as [->|Hin].
  - pose proof (iv_count_in_rng_le (b, s) lo hi Hlh).
    assert (Z0 : overlap_sum l lo hi = 0); [|lia].
    clear IH Hs. revert Hf Hl. induction l as [|q l IH2]; intros Hf Hl; [reflexivity|]. rewrite overlap_sum_cons.
    apply Forall_cons_iff in Hf as [Hq Hf']. inversion Hl; subst.
    rewrite (IH2 Hf' ltac:(assumption)). rewrite iv_count_in_rng_disjoint; [lia|].
    unfold iv_disjoint, B, S in *. cbn [fst snd] in Hq. lia.
  - pose proof (IH Hl Hin) as IH'. rewrite iv_count_in_rng_disjoint; [lia|].
    pose proof (proj1 (Forall_forall _ _) Hf (b, s) Hin) as D. unfold iv_disjoint, B, S in *. cbn [fst snd] in D. lia.
Qed.

(* [comment removed for export] *)

Lemma in_rekind : forall ms m m', In m' (rekind ms m) ->
  exists m0, In m0 ms /\ ((m0 = m /\ m' = AM (am_base m) (am_len m) KRW) \/ (m0 <> m /\ m' = m0)).
Proof.
  intros ms m m' H. unfold rekind in H. apply in_map_iff in H as (m0 & Hm0 & Hin). exists m0. split; [exact Hin|].
  destruct (amap_eqb m0 m) eqn:He.
  - left. apply APS.amap_eqb_eq in He. subst m0. auto.
  - right. split; [|symmetry; exact Hm0]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

Lemma covered_maps_subtract : forall l lo hi x,
  ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.

Inductive slarm := SlE | SlF | SlG | SlM.

Definition sl_nn (s : slarm) : bool := match s with SlG => true | _ => false end.
Definition sl_charge (s : slarm) : bool := match s with SlE | SlM => true | _ => false end.

Record slice_post (s : slarm) (addr n : word) (model model' : Model) : Prop := SP {
  sp_maps : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model);
  sp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  sp_noacc : vm_noaccess (m_vmmaps model') =
             (if sl_nn s then [(addr, n)] else [])
               ++ maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  sp_lazy : m_vm_lazy model' =
            match s with
            | SlM => m_vm_lazy model
            | SlF => (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            | _ => maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            end;
  sp_mat : m_vm_materialized model' =
           match s with
           | SlM => m_vm_materialized model
           | _ => List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model)
           end;
  sp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  sp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  sp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  sp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  sp_halted : m_halted model' = m_halted model;
  sp_fds : m_fds model' = m_fds model;
  sp_fs : m_fs model' = m_fs model;
  sp_tid : m_tid model' = m_tid model;
  sp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)  (* [comment removed for export] *) }.

Definition slice_mem (s : slarm) (addr n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
        FULL' x = if sl_nn s then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
Record slice_hyps (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
       (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte) : Prop := SH_ {
  sh_C : CSOK E cs R FULL model;
  sh_m : In m (a_maps cs);
  sh_nf : is_fog m = false;
  sh_Un : bv_unsigned n = nZ;
  sh_pos : 0 < nZ;
  sh_nal : nZ mod 4096 = 0;
  sh_al : bv_unsigned addr mod 4096 = 0;
  sh_in1 : bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr;
  sh_in2 : bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m));
  sh_post : slice_post s addr n model model';
  sh_mem : slice_mem s addr n FULL FULL';
  sh_F : s = SlF -> am_kind m = KRWLAZY;
  sh_nF : s <> SlF -> am_kind m <> KRWLAZY }.

Section Slice.
  Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Variables (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte).
  Hypothesis SH : slice_hyps E cs R FULL model s m addr n nZ model' FULL'.
  Let HC := sh_C _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hm := sh_m _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hnf := sh_nf _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Un := sh_Un _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZpos := sh_pos _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZal := sh_nal _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hal := sh_al _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin1 := sh_in1 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin2 := sh_in2 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SPo := sh_post _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SM := sh_mem _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HF := sh_F _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnF := sh_nF _ _ _ _ _ _ _ _ _ _ _ _ SH.

  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + nZ.

  (* [comment removed for export] *)
  #[using="Hnf Hm HC SH FULL' model' nZ n addr s FULL R cs FS0 argH SINV LIMIT SEGS"] Lemma sl_bounds : 0 < bv_unsigned (edenot E (am_len m)) /\ bv_unsigned (edenot E (am_base m)) mod 4096 = 0
                    /\ bv_unsigned (edenot E (am_len m)) mod 4096 = 0
                    /\ (bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (am_base m)))
                    /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= alloc_top (m_vmmaps model).
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as B.
    exact (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)).
  Qed.

  #[using="Hin2 Hin1 Hal HnZal HnZpos Hnf Hm HC SH FULL' model' n m s FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT SEGS"] Lemma sl_lohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= alloc_top (m_vmmaps model) /\ lo < hi /\ hi <= 2 ^ 64 /\ lo mod 4096 = 0 /\ hi mod 4096 = 0.
  Proof.
    (first [ pose proof (sl_bounds) as dR_48; dand5 dR_48 as B1 B2 B3 B4 B5 | pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5) ]). subst lo hi. pose proof (alloc_top_lt (m_vmmaps model)) as HT. unfold two_pow_64 in HT.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. rewrite Z.add_mod, Hal, HnZal by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="hi lo HC SH FULL' model' nZ n addr m s FULL R cs RES_len' RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_top : alloc_top (m_vmmaps model) + 8388608 < 2 ^ 64 /\ alloc_top (m_vmmaps model) + 8388608 = uE E e_sp0.
  Proof.
    split; [pose proof (alloc_top_room (m_vmmaps model)) as HT; unfold two_pow_64, stack_max_size in HT; lia | exact (cs_top E cs R FULL model HC)].
  Qed.

  #[using="Hin2 Hin1 HnZpos Hnf Hm HC SH FULL' model' n m s FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_in_maps : forall x : word, lo <= bv_unsigned x < hi -> in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true.
  Proof.
    intros x Hx. eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hnf |]. subst lo hi. lia.
  Qed.

  #[using="hi lo SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH FULL' nZ n addr m s model FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_wf' : model_ivs_wf model'.
  Proof.
    (first [ pose proof ((co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_49; dand4 dR_49 as W1 W2 W3 Wsp | pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & Wsp) ]). (first [ pose proof (sl_lohi) as dR_50; dand6 dR_50 as L1 L2 L3 L4 L5 L6 | pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6) ]).
    assert (iv_wf (addr, n)) by (unfold iv_wf, B, S; cbn; subst lo hi; lia).
    unfold model_ivs_wf. rewrite (sp_maps _ _ _ _ _ SPo), (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo).
    split; [exact W1|]. split; [|split; [|unfold init_sp_ok in *; rewrite (sp_isp _ _ _ _ _ SPo); exact Wsp]].
    - apply ivs_wf_app; [destruct (sl_nn s); [apply ivs_wf_cons; [assumption | apply ivs_wf_nil] | apply ivs_wf_nil] |].
      apply maps_subtract_wf; [exact W2 | rewrite Un; lia].
    - destruct s; try exact W3; try (apply ivs_wf_cons; [assumption|]); apply maps_subtract_wf; try assumption; rewrite Un; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SPo HnZpos Un HC SH FULL' n m s FULL R cs E RES_len' RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_noacc_out : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
    in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)).
  Proof.
    intros x Hx. (first [ pose proof ((co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_51; dand4 dR_51 as W1 W2 W3 _ | pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _) ]).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite !in_ivs_covered.
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with false
      by (symmetry; unfold in_rng; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    destruct (sl_nn s); cbn [app]; [|rewrite andb_true_r; reflexivity].
    rewrite <- in_ivs_covered, in_ivs_cons. cbn [fst snd in_ivs existsb]. rewrite Un.
    replace ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + nZ))%bool with false
      by (symmetry; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [orb]. rewrite andb_true_r. reflexivity.
  Qed.

  #[using="SPo HnZpos Un HC SH FULL' n m model FULL R cs E RES_len' RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_noacc_in : forall x : word, lo <= bv_unsigned x < hi ->
    in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = sl_nn s.
  Proof.
    intros x Hx. (first [ pose proof ((co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_52; dand4 dR_52 as W1 W2 W3 _ | pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _) ]).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite (in_ivs_covered _ (maps_subtract _ _ _)).
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with true
      by (symmetry; unfold in_rng; apply andb_true_intro; subst lo hi; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [negb]. rewrite andb_false_r, orb_false_r.
    destruct (sl_nn s); cbn [app in_ivs existsb fst snd]; [|reflexivity]. rewrite Un.
    rewrite (proj2 (Z.leb_le _ _)) by (subst lo; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (subst hi; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SPo Hin2 Hin1 Hal HnZal HnZpos Hnf Hm HC SH FULL' n m s FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_lazy_out : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
    page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model).
  Proof.
    intros x Hx. (first [ pose proof ((co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_53; dand4 dR_53 as W1 W2 W3 _ | pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _) ]). (first [ pose proof (sl_lohi) as dR_54; dand6 dR_54 as L1 L2 L3 L4 L5 L6 | pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6) ]).
    pose proof (page_of_byte_out_aligned x lo hi L5 L6 Hx) as P. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - rewrite page_in_ranges_cons_out; [| unfold page_size; rewrite Un; lia | rewrite Un; lia].
      apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
  Qed.

  #[using="SPo Hin2 Hin1 Hal HnZal HnZpos Hnf Hm HC SH FULL' n m FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_lazy_in : forall x : word, lo <= bv_unsigned x < hi ->
    page_in_ranges (page_base x) (m_vm_lazy model') =
      match s with SlM => page_in_ranges (page_base x) (m_vm_lazy model) | SlF => true | _ => false end.
  Proof.
    intros x Hx. (first [ pose proof ((co_wf _ _ _ _ _ _ _ _ _ _ _ HC)) as dR_55; dand4 dR_55 as W1 W2 W3 _ | pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _) ]). (first [ pose proof (sl_lohi) as dR_56; dand6 dR_56 as L1 L2 L3 L4 L5 L6 | pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6) ]).
    destruct (page_of_byte_in_aligned x lo hi L5 L6 Hx) as [P1 P2]. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
    - apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH FULL' n m s FULL R HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT SEGS"] Lemma sl_vis_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros cs1 x Hv Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_noacc_out x Hx), (sl_lazy_out x Hx), (in_allow_ext E cs cs1 Hv).
    unfold alloc_top. rewrite (sp_isp _ _ _ _ _ SPo). reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="SPo SH FULL' nZ n addr m s FULL R cs E FS0 argH SINV LIMIT A SEGS"] Lemma sl_top_eq : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model).
  Proof. unfold alloc_top. rewrite (sp_isp _ _ _ _ _ SPo). reflexivity. Qed.

  #[using="SM SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH n m s R HULL_ok' RES_len' HULL_ok RES_len FS0 SINV LIMIT SEGS"] Lemma sl_MR_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    MR E cs1 model' FULL' x = MR E cs model FULL x.
  Proof.
    intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (sl_vis_out cs1 x Hv Hx). rewrite (proj1 SM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH FULL' n m model FULL R cs HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT SEGS"] Lemma sl_vis_in_E : s = SlE -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> VIS E cs1 model' x = true.
  Proof.
    intros Hs cs1 x Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx). subst s.
    cbn. rewrite !orb_true_r. reflexivity.
  Qed.

  #[using="SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH FULL' n m model FULL R cs HULL_ok' RES_len' HULL_ok RES_len FS0 SINV LIMIT SEGS"] Lemma sl_vis_in_G : s = SlG -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> argH E x = false -> VIS E cs1 model' x = false.
  Proof.
    intros Hs cs1 x Hx Ha. (first [ pose proof (sl_lohi) as dR_57; dand6 dR_57 as L1 L2 L3 L4 L5 L6 | pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6) ]). pose proof sl_top_eq as TE. unfold vis. rewrite TE.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx). subst s. cbn [sl_nn negb andb].
    replace (in_hull A (bv_unsigned x)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    replace (alloc_top (m_vmmaps model) <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  #[using="HF SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH FULL' n m FULL R HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT SEGS"] Lemma sl_vis_in_F : s = SlF -> forall cs1 (x : word), a_vis cs1 = a_vis cs -> lo <= bv_unsigned x < hi -> VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros Hs cs1 x Hv Hx. pose proof sl_top_eq as TE. unfold vis. rewrite TE.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx), (in_allow_ext E cs cs1 Hv).
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) x ltac:(subst lo hi; lia)) as [K1 K2].
    rewrite K1, K2. subst s. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="hi lo SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH FULL' n addr m FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT A SEGS"] Lemma sl_eager : eager_used model' <= eager_used model + (if sl_charge s then nZ else 0).
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. (first [ pose proof (Hwf) as dR_58; dand4 dR_58 as W1 W2 W3 _ | pose proof Hwf as (W1 & W2 & W3 & _) ]). (first [ pose proof (sl_lohi) as dR_59; dand6 dR_59 as L1 L2 L3 L4 L5 L6 | pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6) ]).
    rewrite (eager_used_sem model' sl_wf'), (eager_used_sem model Hwf). rewrite (sp_maps _ _ _ _ _ SPo).
    set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
    set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
    assert (CEQ : forall x, covered C' x =
              ((sl_nn s && in_rng lo hi x)
               || (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng lo hi x))
               || match s with
                  | SlM => covered (m_vm_lazy model) x
                  | SlF => in_rng lo hi x || (covered (m_vm_lazy model) x && negb (in_rng lo hi x))
                  | _ => covered (m_vm_lazy model) x && negb (in_rng lo hi x)
                  end)%bool).
    { intros x. subst C'. rewrite (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo). rewrite !covered_app.
      rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un. fold hi. fold lo.
      assert (HD : covered (if sl_nn s then [(addr, n)] else []) x = (sl_nn s && in_rng lo hi x)%bool).
      { destruct (sl_nn s); cbn [covered existsb]; [|reflexivity]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. fold lo hi. apply orb_false_r. }
      rewrite HD. f_equal.
      assert (SC : lo <= hi) by (unfold lo, hi; lia).
      destruct s; cbn [sl_nn]; rewrite ?covered_maps_subtract by first [exact W3 | exact SC]; try reflexivity.
      unfold covered at 1. cbn [existsb]. fold (covered (maps_subtract (m_vm_lazy model) lo hi) x).
      rewrite covered_maps_subtract by first [exact W3 | exact SC]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. reflexivity. }
    assert (CC : forall x, covered C x = (covered (vm_noaccess (m_vmmaps model)) x || covered (m_vm_lazy model) x)%bool).
    { intros x. subst C. apply covered_app. }
    assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                   <= sum_count (fun x => (negb (covered C x) || (in_rng lo hi x && sl_charge s))%bool) (vm_maps (m_vmmaps model))).
    { apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. rewrite CEQ in Hx. rewrite CC.
      destruct s; cbn [sl_nn sl_charge] in Hx |- *;
        destruct (in_rng lo hi x), (covered (vm_noaccess (m_vmmaps model)) x), (covered (m_vm_lazy model) x); cbn in Hx |- *; congruence. }
    pose proof (sum_count_or_le (fun x => negb (covered C x)) (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model))) as OR.
    assert (CH : sum_count (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model)) <= (if sl_charge s then nZ else 0)).
    { destruct (sl_charge s).
      - rewrite (sum_count_ext _ (in_rng lo hi)) by (intros; apply andb_true_r).
        pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) lo hi
                      (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)
                      ltac:(unfold lo; lia) ltac:(unfold hi; lia) ltac:(unfold lo, hi; lia)) as OV.
        unfold overlap_sum in OV. unfold lo, hi in *. lia.
      - rewrite (sum_count_ext _ (fun _ => false)) by (intros; apply andb_false_r).
        clear. induction (vm_maps (m_vmmaps model)) as [|q l IH]; cbn; [lia|]. unfold iv_count. rewrite zcount_const_false. lia. }
    cbv beta in OR. lia.
  Qed.

  #[using="hi lo HnZpos SH FULL' model' nZ n addr m s model FULL R cs E HULL_ok' RES_len' HULL_ok RES_len FS0 argH SINV LIMIT A SEGS"] Lemma page_base_aligned : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
  Proof.
    intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite u64_lit; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  #[using="hi lo HnF HF SM SPo Hin2 Hin1 Hal HnZal HnZpos Un Hnf Hm HC SH n addr model FULL R SHADOW_ok' HULL_ok' RES_len' argH_top SINV_frame SHADOW_ok HULL_ok RES_len"] Lemma slice_cs1_ok : forall sr' R' k' p nx nhi,
    regs_ok E sr' R' ->
    know_ok SEGS E (MR E cs model' FULL') k' ->
    nZ <= nhi ->
    (sl_charge s = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
    CSOK E (ACS (mk_ss p sr' k' nx)
                (match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end)
                (a_totsz cs) (a_ylo cs)
                (if sl_charge s then a_eager cs + nhi else a_eager cs)
                (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)) R' FULL' model'.
  Proof.
    intros sr' R' k' p nx nhi Hregs Hknow Hnhi Hbudget.
    assert (Es : exists s0, s0 = s) by (exists s; reflexivity). destruct Es as [s0 Es].
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. (first [ pose proof (Hwf) as dR_60; dand4 dR_60 as W1 W2 W3 _ | pose proof Hwf as (W1 & W2 & W3 & _) ]).
    (first [ pose proof (sl_lohi) as dR_61; dand6 dR_61 as L1 L2 L3 L4 L5 L6 | pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6) ]). (first [ pose proof (sl_bounds) as dR_62; dand5 dR_62 as B1 B2 B3 B4 B5 | pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5) ]).
    pose proof sl_wf' as Hwf'. pose proof sl_eager as EG.
    pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS. pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
    assert (DISJ := fun m' Hm' Hnf' Hne => maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne).
    assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
              bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo
              \/ hi <= bv_unsigned (edenot E (am_base m'))).
    { intros m' Hm' Hnf' Hne. pose proof (DISJ m' Hm' Hnf' Hne) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold lo, hi. lia. }
    assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
    { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
    (* [comment removed for export] *)
    assert (NONE : forall m', In m' (a_maps cs) -> m <> m' -> (am_kind m' = KNONE \/ am_kind m' = KNONELAZY) ->
              In (amap_den E m') (vm_noaccess (m_vmmaps model'))).
    { intros m' Hm' Hne Hk. rewrite (sp_noacc _ _ _ _ _ SPo). apply in_app_iff. right.
      assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
      pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk) as X.
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
                    (maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _).
      unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact Bm1 | exact X |].
      cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hm' Hnf' Hne). unfold lo, hi in *. lia. }
    (* [comment removed for export] *)
    assert (KINDS : forall m', In m' (a_maps cs) -> am_kind m' = KRWLAZY ->
              forall x : word, bv_unsigned (edenot E (am_base m')) <= bv_unsigned x < bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) ->
                in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
                /\ page_in_ranges (page_base x) (m_vm_lazy model') = true).
    { intros m' Hm' Hk x Hx.
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk x Hx) as [K1 K2].
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto.
      - (* [comment removed for export] *)
        assert (Hmm : m = m').
        { destruct (amap_eqb m m') eqn:He; [apply APS.amap_eqb_eq in He; exact He|]. exfalso.
          assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
          pose proof (DISJ' m' Hm' ltac:(apply KNF; tauto) Hne). lia. }
        subst m'. rewrite sl_noacc_in, sl_lazy_in by lia.
        destruct s0; rewrite <- Es; cbn [sl_nn]; auto; exfalso; refine (HnF _ Hk); rewrite <- Es; discriminate.
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto. }
    match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
    assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
    { intros x Hx. unfold hid. rewrite (sl_vis_out cs1 x eq_refl Hx). reflexivity. }
    assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
    pose proof sl_top_eq as TE. pose proof sl_top as [TR TSP].
    destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xsplit Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xtop Xptop Xlzsub Xtophi Xnapos].
    constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss]; fold cs1; rewrite ?TE.
    - exact Hregs.
    - reflexivity.
    - unfold Mr. rewrite (hid_ext A argH E cs _ model') by reflexivity. exact Hknow.
    - rewrite (sp_halted _ _ _ _ _ SPo). exact Xhalt.
    - unfold fds_ok in *. rewrite (sp_fds _ _ _ _ _ SPo), (sp_fs _ _ _ _ _ SPo). exact Xfds.
    - rewrite (sp_fs _ _ _ _ _ SPo). exact Xfs.
    - rewrite (sp_tid _ _ _ _ _ SPo). exact Xtid.
    - rewrite (sp_res _ _ _ _ _ SPo). exact Xres.
    - rewrite (sp_limit _ _ _ _ _ SPo). exact Xlimit.
    - rewrite (sp_maps _ _ _ _ _ SPo).
      assert (RK : maps_match E (rekind (a_maps cs) m) (vm_maps (m_vmmaps model))).
      { unfold rekind. apply maps_match_rekind; [|exact Xmaps]. intros m0. destruct (amap_eqb m0 m) eqn:He; [|auto].
        apply APS.amap_eqb_eq in He. subst m0. cbn [am_base am_len]. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnf. reflexivity. }
      destruct s0; rewrite <- Es; first [exact RK | exact Xmaps].
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo).
      assert (RKH : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (rekind (a_maps cs) m)).
      { unfold rekind. apply Forall_forall. intros m0 HinR Hh. apply in_map_iff in HinR as (m1 & <- & HinR1).
        destruct (amap_eqb m1 m) eqn:He.
        - exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. discriminate.
        - exact (proj1 (Forall_forall _ _) Xholes m1 HinR1 Hh). }
      destruct s0; rewrite <- Es; first [exact RKH | exact Xholes].
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xseps.
    - exact Hwf'.
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xbounds.
    - (* [comment removed for export] *) rewrite (sp_lazy _ _ _ _ _ SPo).
      assert (SUB : Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top (m_vmmaps model))
                      (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
      { apply Forall_forall. intros q Hq. (first [ pose proof ((maps_subtract_pieces _ _ _ q W3 Hq)) as dR_63; dex1 dR_63 as r; dand4 dR_63 as Hr R1 R2 _ | pose proof ((maps_subtract_pieces _ _ _ q W3 Hq)) as dR_63; dand5 dR_63 as r Hr R1 R2 _ | destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _) ]).
        pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia. }
      destruct s0; rewrite <- Es; try exact SUB; try exact Xlazyb. apply Forall_cons; [cbn [fst snd]; unfold lo, hi in *; lia | exact SUB].
    - (* [comment removed for export] *) intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app in Hz.
      apply orb_prop in Hz as [Hz|Hz].
      + destruct (sl_nn s); [|discriminate]. rewrite in_ivs_cons in Hz. cbn [fst snd in_ivs existsb] in Hz. rewrite orb_false_r in Hz.
        apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
        eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
      + apply Xnasub. rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz by (try exact W2; rewrite Un; lia).
        apply andb_prop in Hz as [Hz _]. exact Hz.
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply NONE; [exact Hm' | | exact Hk']. intros <-. rewrite (HF (eq_sym Es)) in Hk'. destruct Hk'; discriminate. }
      all: (first [ pose proof ((in_rekind _ _ _ Hm')) as dR_64; dex1 dR_64 as m0; destruct dR_64 as [Hm0 [[-> ->]|[Hne ->]]] | pose proof ((in_rekind _ _ _ Hm')) as dR_64; dand3 dR_64 as m0 Hm0 [[-> ->]|[Hne ->]] | destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]) ]); [cbn in Hk'; destruct Hk'; discriminate|];
           apply NONE; [exact Hm0 | congruence | exact Hk'].
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply KINDS; assumption. }
      all: (first [ pose proof ((in_rekind _ _ _ Hm')) as dR_65; dex1 dR_65 as m0; destruct dR_65 as [Hm0 [[-> ->]|[Hne ->]]] | pose proof ((in_rekind _ _ _ Hm')) as dR_65; dand3 dR_65 as m0 Hm0 [[-> ->]|[Hne ->]] | destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]) ]); [cbn in Hk'; discriminate|];
           apply KINDS; assumption.
    - rewrite (sp_res _ _ _ _ _ SPo), (sp_maps _ _ _ _ _ SPo). exact Xtotsz.
    - exact I.   (* [comment removed for export] *)
    - rewrite (sp_brk _ _ _ _ _ SPo). exact Xbrk.
    - rewrite (sp_brk _ _ _ _ _ SPo), (sp_sbrk _ _ _ _ _ SPo). exact Xsbrk.
    - (* [comment removed for export] *) destruct (sl_charge s); lia.
    - exact Xabytes.
    - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5].
      assert (MAT : forall q, In q (m_vm_materialized model') -> In q (m_vm_materialized model)
                      /\ (s <> SlM -> bv_unsigned q < lo \/ hi <= bv_unsigned q)).
      { intros q Hq. pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT in Hq; try (split; [exact Hq | congruence]).
        all: apply filter_In in Hq as [Hq Ho]; split; [exact Hq|]; intros _;
             unfold page_outside_range in Ho; apply negb_true_iff in Ho; apply andb_false_iff in Ho as [Ho|Ho];
             [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold lo, hi; rewrite <- ?Un; lia. }
      constructor; rewrite ?(sp_limit _ _ _ _ _ SPo).
      + pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT; try apply NoDup_filter; exact N1.
      + intros q Hq. apply N2. apply MAT. exact Hq.
      + intros q Hq. apply N3. apply MAT. exact Hq.
      + intros q Hq. destruct (MAT q Hq) as [Hq0 Hout]. pose proof (N4 q Hq0) as L0.
        pose proof (sl_lazy_out q) as LO. pose proof (sp_lazy _ _ _ _ _ SPo) as SL.
        destruct s0; rewrite <- Es in SL, Hout; [| | | rewrite SL; exact L0].
        all: specialize (Hout ltac:(discriminate)); rewrite <- (page_base_aligned q (N2 q Hq0)); rewrite LO by exact Hout;
             rewrite page_base_aligned by exact (N2 q Hq0); exact L0.
      + destruct (sl_charge s); [specialize (Hbudget eq_refl)|]; rewrite Xlimit in *; lia.
    - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 SM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
      + rewrite sl_noacc_in in Hna by lia. rewrite (proj2 SM x) by (unfold lo, hi in *; rewrite Un; lia). rewrite Hna. reflexivity.
      + rewrite (proj1 SM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
    - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply (proj1 SM). pose proof (argH_top _ _ _ Xsinv Hx). unfold hi, uE in *. rewrite Un. lia.
    - (* [comment removed for export] *) exact Xtop.
    - (* [comment removed for export] *) first [exact Xptop | rewrite sl_top_eq; exact Xptop].
    - (* [comment removed for export] *) intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_lazy _ _ _ _ _ SPo) in Hz.
      assert (SUBL : in_ivs z (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) = true ->
                     in_ivs z (vm_maps (m_vmmaps model)) = true).
      { intros Hq. apply Xlzsub. rewrite in_ivs_covered in Hq |- *. rewrite covered_maps_subtract in Hq by (try exact W3; rewrite Un; lia).
        apply andb_prop in Hq as [Hq _]. exact Hq. }
      destruct s0; rewrite <- Es in Hz; try exact (SUBL Hz); try exact (Xlzsub z Hz).
      rewrite in_ivs_cons in Hz. apply orb_prop in Hz as [Hz|Hz]; [| exact (SUBL Hz)].
      cbn [fst snd] in Hz. apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
      eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
    - (* [comment removed for export] *) exact Xtophi.
    - (* [comment removed for export] *) rewrite (sp_noacc _ _ _ _ _ SPo). apply Forall_app. split.
      + destruct (sl_nn s); [|constructor]. constructor; [cbn [snd]; rewrite Un; exact HnZpos | constructor].
      + apply maps_subtract_pos. exact Xnapos.
  Qed.

End Slice.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="kimg_clip_in_hull' kentry_apart_b_sem' kentry_keep_sem' HULL_ok' RES_len' HULL_ok RES_len"] Lemma kn_unfill_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kimg_clip A (kn_unfill k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout.
  pose proof (kimg_clip_in_hull' (kn_unfill k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. unfold kn_unfill in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  apply orb_prop in Hkeep as [Himg|Hap].
  - destruct K; try discriminate. unfold kfoot_apart, kfoot. cbn in HKh. lia.
  - rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.

(* [comment removed for export] *)
#[using="kentry_apart_b_sem' kentry_keep_sem' HULL_ok' RES_len' HULL_ok RES_len"] Lemma kn_rezero_ok_gen : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  forall K, In K (kn_rezero k b off ne) ->
    match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end ->
    kentry_ok SEGS E M' K.
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0 K Hin HKh.
  assert (DEF : forall x : word, M x <> None -> M' x <> None).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [rewrite (Hin0 x ltac:(lia) Hx); discriminate | rewrite Hout by lia; exact Hx]. }
  assert (ZERO : forall x : word, M x = Some (Z_to_bv 8 0) -> M' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [apply Hin0; [lia | rewrite Hx; discriminate] | rewrite Hout by lia; exact Hx]. }
  unfold kn_rezero in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk|ilo ihi|e mm|e rlo rhi|[kb kk] l|a1 n1 a2 n2|[kb kk] l fc|[kb kk] l];
    try (rewrite APS.kentry_apart_bp_eq in Hkeep; eapply kentry_keep_sem'; [exact HKK | eapply kentry_apart_b_sem'; [exact HK | exact Hkeep] | exact Hout]).
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply ZERO. apply Hz. exact Hi.
  - (* [comment removed for export] *) eapply kentry_keep_sem'; [exact HKK | | exact Hout]. unfold kfoot_apart, kfoot. lia.
  - exact HKK.
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d mm Hd Hdm. eapply store_ok_mono; [exact DEF | apply Hs; assumption].
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply DEF. apply Hz. exact Hi.
Qed.

#[using="kimg_clip_in_hull' kentry_apart_b_sem' kentry_keep_sem' HULL_ok' RES_len' HULL_ok RES_len"] Lemma kn_rezero_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kimg_clip A (kn_rezero k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0. pose proof (kimg_clip_in_hull' (kn_rezero k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin. pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

#[using="kentry_apart_b_sem' kentry_keep_sem' HULL_ok' RES_len' HULL_ok RES_len"] Lemma kn_rezero_hull_ok : forall E M M' k b off ne,
  know_ok SEGS E M k -> kimg_in_hull A k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kn_rezero k b off ne).
Proof.
  intros E M M' k b off ne HK Hh Hhull Hout Hin0.
  unfold know_ok. apply Forall_forall. intros K Hin.
  assert (Hin' : In K k) by (unfold kn_rezero in Hin; apply filter_In in Hin as [Hin _]; exact Hin).
  pose proof (proj1 (Forall_forall _ _) Hh K Hin') as HKh.
  apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

#[using="SHADOW_ok' HULL_ok' SHADOW_ok HULL_ok"] Lemma kimg_in_hull_cons2 : forall K1 K2 k,
  match K1 with KImg _ _ => False | _ => True end -> match K2 with KImg _ _ => False | _ => True end ->
  kimg_in_hull A k -> kimg_in_hull A (K1 :: K2 :: k).
Proof.
  intros K1 K2 k H1 H2 Hk. unfold kimg_in_hull in *. constructor; [destruct K1; tauto|]. constructor; [destruct K2; tauto | exact Hk].
Qed.

(* [comment removed for export] *)
#[using="H_off_segments_cs' hid_hull' know_ok_unhide' vis_add_sound' HULL_ok' RES_len' XB XE XN HS argH_top SHADOW_val argH_high SHADOW_ok HULL_ok RES_len SEGS_in_hull"] Lemma vis_add_slice_ok : forall E cs1 cs2 (ea : expr) b off ne R FULL' model' (lo nZ : Z),
  CSOK E cs1 R FULL' model' ->
  vis_add A LIMIT cs1 ea ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  uE E ea = lo -> estart E (SA b off) = lo -> elenZ E ne = nZ -> 0 <= lo -> 0 < nZ -> lo + nZ <= TOPMAX ->   (* [comment removed for export] *)
  (forall x : word, lo <= bv_unsigned x < lo + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
     /\ argH E x = false /\ FULL' x = Some (Z_to_bv 8 0)) ->
  CSOK E cs2 R FULL' model'.
Proof.
  intros E cs1 cs2 ea b off ne R FULL' model' lo nZ HC1 Hva Hkh Hea Hest Hne Hlo HnZ Hhi NEW.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  (first [ pose proof ((vis_add_inv cs1 ea ne _ cs2 Hva)) as dR_66; dex1 dR_66 as nhi; destruct dR_66 as [Hnhi Ecs2] | pose proof ((vis_add_inv cs1 ea ne _ cs2 Hva)) as dR_66; dand3 dR_66 as nhi Hnhi Ecs2 | destruct (vis_add_inv cs1 ea ne _ cs2 Hva) as (nhi & Hnhi & Ecs2) ]).
  assert (BYTE : forall x : word, lo <= bv_unsigned x < lo + nZ -> MR E cs2 model' FULL' x = Some (Z_to_bv 8 0)).
  { intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_67; dand4 dR_67 as N1 N2 N3 N4 | destruct (NEW x Hx) as (N1 & N2 & N3 & N4) ]).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. rewrite Hea. unfold uE. fold (elenZ E ne). rewrite Hne.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal, !orb_true_r. cbn [negb]. exact N4. }
  assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat; rewrite Hest, Hne; unfold TOPMAX in Hhi; lia).
  constructor; [|constructor].
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold TOPMAX in Hhi; lia); unfold TOPMAX in Hhi; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold TOPMAX in Hhi; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros i Hi. apply BYTE. rewrite u64_lit by (unfold TOPMAX in Hhi; lia). lia.
  - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
#[using="RES_len' RES_len A"] Lemma find_containing_sound : forall E M k ms kinds b off ne m,
  know_ok SEGS E M k -> find_containing k ms kinds b off ne = Some m ->
  In m ms /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ bv_unsigned (edenot E (am_base m)) <= estart E (SA b off)
  /\ estart E (SA b off) + elenZ E ne <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
  intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
  apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
  apply existsb_exists in Hk as (k0 & Hk0 & Hkk). apply APS.mkind_eqb_eq in Hkk. subst k0.
  pose proof (APS.xinsideX_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].   (* [comment removed for export] *)
  unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="reg_lit_sound' reg_sound' RES_hullH HULL_ok' RES_len' HULL_ok RES_hull RES_len"] Lemma slice_args : forall E cs R FULL model b off ne nlo nhi kinds m,
  CSOK E cs R FULL model ->
  fixed_args_in cs = Some (b, off, ne, nlo, nhi) ->   (* [comment removed for export] *)
  find_containing (kn cs) (a_maps cs) kinds b off ne = Some m ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  In m (a_maps cs) /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len /\ 0 < len < 2 ^ 64
  /\ edenot E ne = n /\ bv_unsigned n = nZ /\ 0 < nZ /\ nZ <= nhi /\ nZ mod 4096 = 0
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr
  /\ (bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr)   (* [comment removed for export] *)
  /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr
  /\ bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
  /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= TOPMAX   (* [comment removed for export] *)
  /\ map_contains (vm_maps (m_vmmaps model)) addr n = true
  /\ region_free (vm_reserved (m_vmmaps model)) addr n = true
  /\ overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) <= nZ.
Proof.
  intros E cs R FULL model b off ne nlo nhi kinds m HC HFA Hf addr len nZ n.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  (first [ pose proof ((fixed_args_in_sound E cs R FULL model b off ne nlo nhi HC HFA)) as dR_68; dand7 dR_68 as Hsp HML Hal Hpos Htop R10 _ | destruct (fixed_args_in_sound E cs R FULL model b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Htop & R10 & _) ]).
  (first [ pose proof ((mmap_len_sound E cs R FULL model ne nlo nhi HC HML)) as dR_69; dand7 dR_69 as R11 Hlen Hne Hnlo HnZ HnZal _ | destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & _) ]).
  fold addr in Hal, Hpos, Htop, R10. fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  (first [ pose proof ((find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf)) as dR_70; dand4 dR_70 as Hm [Hkind Hnf] I1 I2 | destruct (find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf) as (Hm & [Hkind Hnf] & I1 & I2) ]).
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf) as HIN.
  (first [ pose proof ((proj1 (Forall_forall _ _) HB (amap_den E m) HIN)) as dR_71; dand5 dR_71 as B1 B2 B3 B4 B5T | pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5T) ]). cbn [amap_den fst snd] in B1, B2, B3, B4, B5T.
  pose proof (APS.co_tophi _ _ _ _ _ _ _ _ _ _ _ HC) as HTH.
  assert (B5 : bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= TOPMAX) by lia. clear B5T.
  pose proof (u64_range (edenot E (am_base m))) as Rb.
  assert (Hest : bv_unsigned addr = estart E (SA b off)).
  { unfold addr. apply (APS.u_of_split E (reg cs 10) b off Hsp). unfold elenZ in I2. pose proof (u64_range (edenot E ne)). unfold TOPMAX in B5. lia. }
  unfold elenZ in I2. rewrite Hne in I2.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. apply u64_lit. pose proof (u64_range (Z_to_bv 64 nZ)). fold n in H. unfold two64, TOPMAX in *. lia. }
  rewrite Un in I2.
  assert (Himg : bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr) by lia.   (* [comment removed for export] *)
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
  { eapply map_contains_intro; [exact HIN | lia | rewrite Un; lia]. }
  split; [exact Hm|]. split; [split; [exact Hkind | exact Hnf]|].
  repeat (split; [first [assumption | lia | symmetry; assumption] |]).
  split; [apply reserved_free_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Un; exact Himg] |].
  rewrite Un. pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + nZ)
    (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) HIN ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.



(* [comment removed for export] *)


End Nodes.
