(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Shape HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_lim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_top.

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
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd lim_s inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd lim_t inp) T ->
  Equivalence.strong_equiv_error_free_budgets lim_s lim_t (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
     (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros lim_s lim_t source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold Equivalence.strong_equiv_error_free_budgets, Equivalence.error_free. cbn [run bh_errors bh_traces].
  split; [|split].
  - eapply realizes_no_error; exact Hsource.
  - eapply realizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (realizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

Lemma target_alloc_limit_ge31 : (2 ^ 31 <= target_alloc_limit)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section TopUbsan.
  Hypothesis U_realizes_spec_lim : forall {AMB : Amb} (lim : Z) sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    (2 ^ 31 <= lim)%Z ->
    valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
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
    destruct Hens as [Vsp [Vbrk [Vmb Vfit]]]. destruct Hent as [Vsp' [Vbrk' [Vmb' Vfit']]].
    pose proof Hvalid as (Va & Ve & Vfs & Vrel & [Vuid Vgid] & Vnf & Vsm & Vhw & Vab & Vva & _).   (* [comment removed for export] *)
    eapply shape_error_free_equiv_lims.
    - eapply (@P_top.P_realizes_spec_lim SIP FPP PF (amb_of inp) lim_s); eassumption.
    - exact (@U_realizes_spec_lim (amb_of inp) target_alloc_limit asp abrk amb arnd inp target_alloc_limit_ge31
               Vsp' Vbrk' Va Ve Vfs Vfit').
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
