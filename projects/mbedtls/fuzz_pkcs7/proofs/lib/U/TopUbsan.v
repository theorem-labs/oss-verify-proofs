(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (shape_error_free_equiv_lims restated over the run's segments, run_segments; the ubsan hypothesis U_realizes_spec_lim gains the channel-reader and launch premises; each binary's walk lifted to the run by RomStable.run_init, with new lemmas vdso_none_plain and vdso_none_ubsan; amb_of given the channel reader and the vDSO run; Lib.RomStable imported). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Shape HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Spec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_lim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require RomStable.

Definition src_img : Image :=
  mkImage Plain.M.loaded_segments Plain.M.init_pc
          Plain.M.phdrs.
Definition ubsan_img : Image :=
  mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
          Ubsan.M.phdrs.

(* [comment removed for export] *)
Lemma shape_error_free_equiv_lims :
  forall (lim_s lim_t : Z)
         source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw)
         target_segs apc aph asp abrk amb (arnd : EntryDraw)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd lim_s inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd lim_t inp) T ->
  Equivalence.strong_equiv_error_free_budgets lim_s lim_t (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
     (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros lim_s lim_t source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold Equivalence.strong_equiv_error_free_budgets, Equivalence.error_free. cbn [run bh_errors bh_traces].
  split; [|split].
  - eapply realizes_no_error; exact Hsource.
  - eapply realizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (realizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

Lemma target_alloc_limit_ge31 : (2 ^ 31 <= target_alloc_limit)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* Neither image carries a vDSO text mapping of its own ([RomStable.run_init]'s side condition). *)
Lemma vdso_none_plain : RiscvSemantics.vdso_image Plain.M.loaded_segments = None.
Proof. reflexivity. Qed.
Lemma vdso_none_ubsan : RiscvSemantics.vdso_image Ubsan.M.loaded_segments = None.
Proof. reflexivity. Qed.

Section TopUbsan.
  Hypothesis U_realizes_spec_lim : forall {AMB : Amb} (lim : Z) sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    (2 ^ 31 <= lim)%Z ->
    valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) -> in_channel_reader inp = true -> valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rd) inp ->
    realizes Ubsan.M.loaded_segments
      (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
         sp brk mbase rd lim inp)
      (Spec.spec (in_argv inp) (in_fs inp)).

  (* [comment removed for export] *)
  #[using="U_realizes_spec_lim"] Theorem top_ubsan_lim : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
    (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
    (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
    forall lim_s : Z, (2 ^ 31 <= lim_s)%Z ->
    forall en_source en_target inp,
      valid_entry src_img en_source inp -> valid_entry ubsan_img en_target inp -> valid_input inp ->
      Equivalence.strong_equiv_error_free_budgets lim_s target_alloc_limit src_img ubsan_img en_source en_target inp.
  Proof.
    intros SIP FPP PF lim_s Hlim [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    cbn [src_img ubsan_img] in Hens, Hent.
    destruct Hens as [Vsp [Vbrk [Vmb [Vfit Vlau]]]]. destruct Hent as [Vsp' [Vbrk' [Vmb' [Vfit' Vlau']]]].
    pose proof Hvalid as (Va & Ve & Vfs & Vrel & Vreal & [Vuid Vgid] & Vnf & Vsm & Vhw & Vab & Vva & _).   (* [comment removed for export] *)
    pose proof (Run.valid_input_channel_reader inp Hvalid) as Vrd. pose proof (Run.valid_input_launch inp Hvalid) as Vvl.
    eapply shape_error_free_equiv_lims.
    (* LPS revision (run_segments): each walk is over the binary's own segments; [run_init]
       lifts it to the run's list from the run's start (Lib/RomStable.v). *)
    - eapply RomStable.run_init; [exact vdso_none_plain|].
      eapply (@P_top.P_realizes_spec_lim SIP FPP PF (amb_of inp (Run.valid_input_channel_reader inp Hvalid) (Vdso.vdso_run_init (ed_vdso rrnd))) lim_s); eassumption.
    - eapply RomStable.run_init; [exact vdso_none_ubsan|].
      exact (@U_realizes_spec_lim (amb_of inp (Run.valid_input_channel_reader inp Hvalid) (Vdso.vdso_run_init (ed_vdso rrnd))) target_alloc_limit asp abrk amb arnd inp target_alloc_limit_ge31
               Vsp' Vbrk' Va Ve Vfs Vfit' Vrd Vvl Vlau').
  Qed.

  (* [comment removed for export] *)
  #[using="U_realizes_spec_lim"] Theorem top_ubsan_shipped : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
    (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
    (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
    strong_universal_error_free_T_budgets Equivalence.ShippedBudgets.lim_source Equivalence.ShippedBudgets.lim_target
      src_img ubsan_img.
  Proof.
    intros SIP FPP PF en_s en_t inp Hs Ht Hv _.
    exact (top_ubsan_lim SIP FPP PF source_alloc_limit source_alloc_limit_ge31 en_s en_t inp Hs Ht Hv).
  Qed.
End TopUbsan.

(* [comment removed for export] *)
