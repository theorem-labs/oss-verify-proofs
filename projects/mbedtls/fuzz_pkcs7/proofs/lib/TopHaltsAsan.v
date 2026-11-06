(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ShapeAlg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SpinAlg SrzHaltsB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Spec SpecExits.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.LimSim Require Import LimSimSys.
Import ListNotations.

Definition asan_img : Image :=
  mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.

(* [comment removed for export] *)
Definition HSEGS : list Segment := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition asan_realizes_spec_stmt : Prop :=
  forall (sp brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk HSEGS brk0 ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> in_abort_terminal inp = false -> in_va_size inp = Sv48 -> valid_hwcap (in_hwcap inp) ->
    SpinAlg.srealizes HSEGS
      (init_config HSEGS Asan.M.init_pc Asan.M.phdrs sp brk0 mbase rdraw target_alloc_limit inp)
      (Spec.spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Theorem asan_must_exit_at_target_limit : asan_realizes_spec_stmt ->
  forall en inp, valid_entry asan_img en inp -> valid_input inp ->
    must_exit_in_scfg forced_only_cfg SpecExits.codes02 asan_img target_alloc_limit en inp.
Proof.
  intros REAL [asp abrk amb arnd] inp Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. cbn [asan_img] in Hent.
  destruct Hent as [Vsp [Vbrk [Vmb Vfit]]].
  pose proof Hvalid as (Va & Ve & Vfs & Vrel & [Vuid Vgid] & Vnf & Vsm & Vhw & Vab & Vva & _).   (* [comment removed for export] *)
  unfold asan_img.
  apply (SrzHaltsB.srealizes_must_exit_in_scfg HSEGS SpecExits.codes02 _ _ _ _ _ _ _ _ (Spec.spec (in_argv inp) (in_fs inp))).
  - exact (REAL asp abrk amb arnd inp Vsp Vbrk Va Ve Vfit Vuid Vab Vva Vhw).
  - apply SpecExits.exits_in_spec.
Qed.

Lemma shipped_lim_source_le_target : (Equivalence.ShippedBudgets.lim_source <= target_alloc_limit)%Z.
Proof. unfold Equivalence.ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.

(* [comment removed for export] *)
Theorem halts_asan_of_realizes : asan_realizes_spec_stmt ->
  halts_allowed_T_scfg_budgets forced_only_cfg Equivalence.ShippedBudgets.lim_source SpecExits.codes02 asan_img.
Proof.
  intros REAL en inp Hent Hvalid SWB.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg SpecExits.codes02 asan_img target_alloc_limit
           Equivalence.ShippedBudgets.lim_source en inp shipped_lim_source_le_target SWB).
  exact (asan_must_exit_at_target_limit REAL en inp Hent Hvalid).
Qed.

(* [comment removed for export] *)
Check (fun H : asan_realizes_spec_stmt =>
  (halts_asan_of_realizes H :
    LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
      LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
      [Z_to_bv 64 0; Z_to_bv 64 2]
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.mbedtls.fuzz_pkcs7.images.Asan.M.loaded_segments OSSVerify.mbedtls.fuzz_pkcs7.images.Asan.M.init_pc OSSVerify.mbedtls.fuzz_pkcs7.images.Asan.M.phdrs))).

(* [comment removed for export] *)
