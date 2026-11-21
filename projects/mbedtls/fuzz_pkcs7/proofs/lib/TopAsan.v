(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mixed_shape_error_free_equiv and its lims form restated over run_segments; new lemmas vdso_none_plain and vdso_none_asan; the top proof lifts each walk to the run's segment list with the two RomStable modules, now imported, and passes the input's channel-reader, launch and entry-launch facts and the mmap base check to the new amb_of arguments and to the restated boot theorem). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Shape HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Spec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_lim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SpinAlg AsanPlanSound AsanPlanImages AsanCertDefs AsanInit AsanMainEntryFacts AsanBoot.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require AImg A_main_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require RomStable.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require RomStable.

(* Neither image carries a vDSO text mapping of its own (the bridges' side condition). *)
Lemma vdso_none_plain : RiscvSemantics.vdso_image Plain.M.loaded_segments = None.
Proof. reflexivity. Qed.
Lemma vdso_none_asan : RiscvSemantics.vdso_image Asan.M.loaded_segments = None.
Proof. reflexivity. Qed.

Definition src_img : Image :=
  mkImage Plain.M.loaded_segments Plain.M.init_pc
          Plain.M.phdrs.
Definition asan_img : Image :=
  mkImage Asan.M.loaded_segments Asan.M.init_pc
          Asan.M.phdrs.

(* [comment removed for export] *)
Lemma mixed_shape_error_free_equiv :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw)
         target_segs apc aph asp abrk amb (arnd : EntryDraw)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
  SpinAlg.srealizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd target_alloc_limit inp) T ->
  Equivalence.strong_equiv_error_free (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
     (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold Equivalence.strong_equiv_error_free, Equivalence.error_free. cbn [run bh_errors bh_traces].
  split; [|split].
  - eapply realizes_no_error; exact Hsource.
  - eapply SpinAlg.srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (SpinAlg.srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mixed_shape_error_free_equiv_lims :
  forall (lim_s lim_t : Z)
         source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw)
         target_segs apc aph asp abrk amb (arnd : EntryDraw)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd lim_s inp) T ->
  SpinAlg.srealizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd lim_t inp) T ->
  Equivalence.strong_equiv_error_free_budgets lim_s lim_t (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
     (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros lim_s lim_t source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold Equivalence.strong_equiv_error_free_budgets, Equivalence.error_free. cbn [run bh_errors bh_traces].
  split; [|split].
  - eapply realizes_no_error; exact Hsource.
  - eapply SpinAlg.srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (SpinAlg.srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Definition asan_bridge_stmt : Prop :=
  forall (sp brk0 : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw ->
    A_main_top.entry_bridgeA (AsanMainEntryFacts.main_entry_A sp brk0 rdraw argv envp fs uid hw) argv fs sp.

(* [comment removed for export] *)
Lemma ASEGS_asegs : AsanCertDefs.ASEGS = AImg.asegs.
Proof. reflexivity. Qed.

Lemma cfg_of_mkCfg : forall R mem md,
  AsanPlanSound.APS.cfg_of AImg.asegs R 0x96b6c mem md
  = mkCfg (MS R bvmap_empty (Z_to_bv 64 0x96b6c) (Z_to_bv 32 0) None mem (seg_rom AImg.asegs)) md.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Theorem top_asan_lim : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
  (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
  (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
  asan_bridge_stmt ->
  forall lim_s : Z, (2 ^ 31 <= lim_s)%Z ->
  forall en_source en_target inp,
    valid_entry src_img en_source inp -> valid_entry asan_img en_target inp -> valid_input inp ->
    Equivalence.strong_equiv_error_free_budgets lim_s target_alloc_limit src_img asan_img en_source en_target inp.
Proof.
  intros SIP FPP PF BRIDGE lim_s Hlim [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  cbn [src_img asan_img] in Hens, Hent.
  destruct Hens as [Vsp [Vbrk [Vmb [Vfit Vlau]]]]. destruct Hent as [Vsp' [Vbrk' [Vmb' [Vfit' Vlau']]]].
  pose proof Hvalid as (Va & Ve & Vfs & Vrel & Vreal & [Vuid Vgid] & Vnf & Vsm & Vhw & Vab & Vva & _).   (* [comment removed for export] *)
  pose proof (Run.valid_input_channel_reader inp Hvalid) as Vrd. pose proof (Run.valid_input_launch inp Hvalid) as Vvl.
  eapply mixed_shape_error_free_equiv_lims.
  (* LPS revision (run_segments): each walk is over the binary's own segments;
     [Lib.RomStable.run_init] / [ABoot.RomStable.srun_init] lift it to the run's list from the
     run's start. *)
  - eapply Lib.RomStable.run_init; [exact vdso_none_plain|].
    eapply (@P_top.P_realizes_spec_lim SIP FPP PF (amb_of inp (Run.valid_input_channel_reader inp Hvalid) (Vdso.vdso_run_init (ed_vdso rrnd))) lim_s); eassumption.
  - eapply ABoot.RomStable.srun_init; [exact vdso_none_asan|].
    pose proof (@P_top.P_realizes_spec_lim SIP FPP PF (amb_of inp (Run.valid_input_channel_reader inp Hvalid) (Vdso.vdso_run_init (ed_vdso rrnd))) lim_s rsp rbrk rmb rrnd inp Hlim Vsp Vbrk Va Ve Vfs Vfit Vrd Vvl Vlau) as HP.
    pose proof (realizes_nonempty _ _ _ HP) as Hnil.
    apply (AsanBoot.asan_boot_entry_inp asp abrk amb arnd inp Vsp' Vbrk' Vmb' Va Ve Vuid Vvl Vrd Vlau'
             (fun _ _ => Spec.spec (in_argv inp) (in_fs inp))).
    + intros; reflexivity.
    + intros E fs'. exact Hnil.
    + intros R mem md E _ HME Hfs. rewrite ASEGS_asegs, cfg_of_mkCfg.
      exact (A_main_top.A_main_stmt_of_bridge _ (in_argv inp) (in_fs inp) asp
               (BRIDGE asp abrk arnd (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Vsp' Va Ve Vfit' Vuid Vhw)
               R mem md HME Hfs).
Qed.

(* [comment removed for export] *)
Theorem top_asan : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
  (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
  (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
  asan_bridge_stmt ->
  strong_universal_error_free_T src_img asan_img.
Proof.
  intros SIP FPP PF BRIDGE en_s en_t inp Hs Ht Hv.
  exact (top_asan_lim SIP FPP PF BRIDGE source_alloc_limit source_alloc_limit_ge31 en_s en_t inp Hs Ht Hv).
Qed.

(* [comment removed for export] *)
Theorem top_asan_sanitizer : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
  (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
  (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
  asan_bridge_stmt ->
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img asan_img.
Proof.
  intros SIP FPP PF BRIDGE en_s en_t inp Hs Ht Hv _.
  exact (top_asan_lim SIP FPP PF BRIDGE sanitizer_source_limit sanitizer_source_limit_ge31 en_s en_t inp Hs Ht Hv).
Qed.

(* [comment removed for export] *)
