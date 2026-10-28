(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Shape HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_lim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SpinAlg AsanPlanSound AsanInit AsanPlan AxSymExec3 AxSymRun3.

Definition src_img : Image :=
  mkImage Plain.M.loaded_segments Plain.M.init_pc
          Plain.M.phdrs.
Definition both_img : Image :=
  mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
          AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Lemma mixed_shape_error_free_equiv_lims :
  forall (lim_s lim_t : Z)
         source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw)
         target_segs apc aph asp abrk amb (arnd : EntryDraw)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd lim_s inp) T ->
  SpinAlg.srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd lim_t inp) T ->
  Equivalence.strong_equiv_error_free_budgets lim_s lim_t (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
     (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros lim_s lim_t source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold Equivalence.strong_equiv_error_free_budgets, Equivalence.error_free. cbn [run bh_errors bh_traces].
  split; [|split].
  - eapply realizes_no_error; exact Hsource.
  - eapply SpinAlg.srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (SpinAlg.srealizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Definition both_side : Prop :=
  forall asp abrk amb (arnd : EntryDraw) (inp : ProcInput),
    valid_entry both_img (mkEntry asp abrk amb arnd) inp -> valid_input inp ->
    SpinAlg.srealizes AsanUbsan.M.loaded_segments
      (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
         asp abrk amb arnd target_alloc_limit inp)
      (Spec.spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Theorem top_both_lim : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
  (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
  (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
  both_side ->
  forall lim_s : Z, (2 ^ 31 <= lim_s)%Z ->
  forall en_source en_target inp,
    valid_entry src_img en_source inp -> valid_entry both_img en_target inp -> valid_input inp ->
    Equivalence.strong_equiv_error_free_budgets lim_s target_alloc_limit src_img both_img en_source en_target inp.
Proof.
  intros SIP FPP PF BOTH lim_s Hlim [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  cbn [src_img] in Hens.
  destruct Hens as [Vsp [Vbrk [Vmb Vfit]]].
  pose proof Hvalid as (Va & Ve & Vfs & _).
  eapply mixed_shape_error_free_equiv_lims.
  - eapply (@P_top.P_realizes_spec_lim SIP FPP PF (amb_of inp) lim_s); eassumption.
  - exact (BOTH asp abrk amb arnd inp Hent Hvalid).
Qed.

(* [comment removed for export] *)
Theorem top_both : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
  (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
  (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
  both_side ->
  strong_universal_error_free_T src_img both_img.
Proof.
  intros SIP FPP PF BOTH en_s en_t inp Hs Ht Hv.
  exact (top_both_lim SIP FPP PF BOTH source_alloc_limit source_alloc_limit_ge31 en_s en_t inp Hs Ht Hv).
Qed.

(* [comment removed for export] *)
Theorem top_both_sanitizer : forall (SIP : forall sp0 : word, sinv (P_layout sp0)),
  (forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8)%Z ->
  (forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c) ->
  both_side ->
  strong_universal_error_free_T_budgets Equivalence.SanitizerBudgets.lim_source Equivalence.SanitizerBudgets.lim_target
    src_img both_img.
Proof.
  intros SIP FPP PF BOTH en_s en_t inp Hs Ht Hv _.
  exact (top_both_lim SIP FPP PF BOTH sanitizer_source_limit sanitizer_source_limit_ge31 en_s en_t inp Hs Ht Hv).
Qed.

(* [comment removed for export] *)
Definition BOTH_MAIN : Z := 0x970e0.

Lemma spec_has_nil : forall argv fs, Spec.spec argv fs [].
Proof.
  intros argv fs. unfold Spec.spec.
  destruct argv as [|a0 [|path [|a2 rest]]]; cbv beta iota;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    | |- context [match ?o with Some _ => _ | None => _ end] => destruct o
    end;
    first [ apply t_emit_has_nil | left; apply t_emit_has_nil ].
Qed.

(* [comment removed for export] *)
Lemma cfg_of_mkCfg_both : forall R mem md,
  AsanPlanSound.APS.cfg_of AsanUbsan.M.loaded_segments R BOTH_MAIN mem md
  = mkCfg (MS R bvmap_empty (Z_to_bv 64 BOTH_MAIN) (Z_to_bv 32 0) None mem
              (seg_rom AsanUbsan.M.loaded_segments)) md.
Proof. intros. reflexivity. Qed.

Section Parts.
Variable MENTRY : word -> word -> EntryDraw -> list (list byte) -> list (list byte) -> Fs.Fs -> word -> word ->
                  bvmap 5 word -> (word -> option byte) -> Model -> Prop.

Definition both_boot_stmt : Prop :=
  forall (sp brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk0 -> valid_argv (in_argv inp) ->
    valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_id (in_uid inp) ->
    in_abort_terminal inp = false -> in_va_size inp = Sv48 ->
    forall MAIN : AxSymExec3.AX2.env -> Fs.Fs -> TSet,
    (forall E E' fs', AxSymRun3.env_agree AsanPlan.AP.NX0 E E' -> MAIN E fs' = MAIN E' fs') ->
    (forall E fs', MAIN E fs' []) ->
    (forall R mem md E,
       (forall n, (n < AsanPlan.AP.NX0)%nat ->
          AxSymExec3.AX2.ev E n
          = AxSymExec3.AX2.ev (AsanInit.E0 AsanUbsan.M.phdrs sp rdraw brk0 (in_argv inp) (in_envp inp)
                                 (in_uid inp) (in_hwcap inp)) n) ->
       MENTRY sp brk0 rdraw (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) R mem md ->
       m_fs md = in_fs inp ->
       SpinAlg.srealizes AsanUbsan.M.loaded_segments
         (AsanPlanSound.APS.cfg_of AsanUbsan.M.loaded_segments R BOTH_MAIN mem md) (MAIN E (in_fs inp))) ->
    SpinAlg.srealizes AsanUbsan.M.loaded_segments
      (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
         sp brk0 mbase rdraw AsanInit.LIMIT inp)
      (MAIN (AsanInit.E0 AsanUbsan.M.phdrs sp rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp)
               (in_hwcap inp)) (in_fs inp)).

Definition both_main_stmt : Prop :=
  forall (sp brk0 : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw ->
    forall R mem md, MENTRY sp brk0 rdraw argv envp fs uid hw R mem md -> m_fs md = fs ->
    SpinAlg.srealizes AsanUbsan.M.loaded_segments
      (mkCfg (MS R bvmap_empty (Z_to_bv 64 BOTH_MAIN) (Z_to_bv 32 0) None mem
                 (seg_rom AsanUbsan.M.loaded_segments)) md)
      (Spec.spec argv fs).

Theorem both_side_of_parts : both_boot_stmt -> both_main_stmt -> both_side.
Proof.
  intros BOOT MAINS asp abrk amb arnd inp Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  cbn [both_img] in Hent.
  destruct Hent as [Vsp' [Vbrk' [Vmb' Vfit']]].
  pose proof Hvalid as (Va & Ve & Vfs & Vrel & [Vuid Vgid] & Vnf & Vsm & Vhw & Vab & Vva & _).   (* [comment removed for export] *)
  apply (BOOT asp abrk amb arnd inp Vsp' Vbrk' Va Ve Vfit' Vuid Vab Vva
           (fun _ _ => Spec.spec (in_argv inp) (in_fs inp))).
  - intros; reflexivity.
  - intros E fs'. apply spec_has_nil.
  - intros R mem md E _ HME Hfs. rewrite cfg_of_mkCfg_both.
    exact (MAINS asp abrk arnd (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp)
             Vsp' Va Ve Vfit' Vuid Vhw R mem md HME Hfs).
Qed.
End Parts.

(* [comment removed for export] *)
