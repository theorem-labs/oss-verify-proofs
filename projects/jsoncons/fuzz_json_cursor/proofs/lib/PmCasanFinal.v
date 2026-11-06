(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp KillFree VmLimitFrame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm10DrvLibL Pm10HeapBridge PmFinal PmFinalSan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8IcptLayout PmLibIfaceA AsanInitK Pm8DefsK
  Pm8ArtFsInv Pm8ArtIfaceInst Pm8ArtIfaceInstX Pm8DrvG Pm8DrvLibL Pm8DrvLibInit Pm8MainPhaseA Pm8InstA Pm8DrvMain Pm8DiagArms Pm8UsageEntry Pm8UsageArm.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfg0 : SpuriousCfg := PmFinal.cfg0.

Definition art_IL : icpt_layout :=
  ICL 0x6a54c 2304 0x103c0 0x103e0 ART_GLOBALS ART_POISON 0x7ee70 0x7ee6c 0x6b1f08 0x6a5c4 4320 [(0x690a20, 8, 0x6b0d18); (0x6b0d40, 8, 0)] 0x10000 0x154000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.
Definition art_ILX : icpt_layout_x := ICLX 0x6a564 8192 0x6a62c 512 0x6b0aa0 0x74c7c 512 0x82c5c 0x6b0ce3 0x6a560 0x7ee68 0x829e4 0x82aec 0x82b04 256.
Lemma art_ILX_ok : pm_icpt_layout_x art_ILX.
Proof. constructor; reflexivity. Qed.

Definition BUDGET0 : Z := 2 ^ 34.
Lemma BUDGET0_lo : 2 ^ 34 <= BUDGET0.  Proof. unfold BUDGET0. lia. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.  Proof. unfold BUDGET0. lia. Qed.

Lemma budA_of_bounds : forall (LayA : lib_layoutA),
  (forall n, 0 <= n < 67108864 -> 0 <= fst (lla_credit LayA n) <= 2000 /\ 0 <= snd (lla_credit LayA n) <= 2 ^ 31) ->
  drv_budgetA art_L LayA.
Proof.
  intros LayA HB n Hn. specialize (HB n Hn). unfold credA, CAPk, adebit.
  cbn [fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. lia.
Qed.

Abbreviation IMG_csrc9 :=
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Abbreviation IMG_tgt :=
  (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Definition pm_casan_tgt_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    srealizes Asan.M.loaded_segments scfg
      (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Section Hyps.

  Variable LayA : lib_layoutA.
  Variable LStA : asan_run -> lib_statics.
  Hypothesis DLLA : drv_lib_layoutA LayA art_L.
  Hypothesis DLCA : drv_lib_cellsA LayA.
  Hypothesis BUDA : drv_budgetA art_L LayA.
  Hypothesis LIBA : lib_ok_stmt cfg0 art_L art_LX art_C art_IL art_ILX LayA LStA.

  Let ICPTX : icptx_stmt cfg0 art_ILX BUDGET0 := as0_icptx cfg0 art_ILX BUDGET0 art_ILX_ok.

  Theorem pm_casan_tgt : pm_casan_tgt_stmt cfg0.
  Proof.
    intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hva Hve Hvfs Hcreds Hhw Hsv.
    destruct inp as [argv envp ifs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0].
    unfold in_fs in *. cbn [in_argv in_envp in_image_fs in_tmp in_uid in_hwcap in_va_size] in *. subst va.
    destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
    exact (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL art_LX art_ILX LayA LStA BUDGET0 BUDGET0_lo BUDGET0_hi
             (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
             (as0_icpt_ok cfg0 art_IL art_ILX BUDGET0 art_IL_ok art_ILX_ok ICPTX) (as0_sfree_ok cfg0 BUDGET0 eq_refl) LIBA
             (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok)
             (as0_drv_main_closed cfg0 art_L art_C art_IL LayA LStA DLLA DLCA BUDA)
             (as0_usage cfg0 art_L art_C art_IL art_ILX BUDGET0 BUDGET0_lo BUDGET0_hi (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
                (as0_icpt_ok cfg0 art_IL art_ILX BUDGET0 art_IL_ok art_ILX_ok ICPTX) (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok) (dg_usage_ok cfg0 art_L art_C art_IL))
             sp brk mbase rdraw argv envp (fs_seed_tmp ifs0 tmp0) stdin0 uid gid hw groups net nofile sigmask abt ifs0 urnd tmp0 Hsp Hbrk Hva Hve Hfit Hu Hhw Hvfs eq_refl).
  Qed.

  Theorem pm_casan_half : forall en_t inp,
    valid_entry IMG_tgt en_t inp -> valid_input_abort inp ->
    PmFinalSan.half_ok cfg0 IMG_tgt SanitizerBudgets.lim_target en_t inp (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros [sp brk mb rnd] inp Hen Hvalid.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    apply PmFinalSan.half_ok_of_srealizes.
    - exact (pm_casan_tgt sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw Hsv48).
    - apply Safe_init_big. exact nbr_limit_target.
    - apply kill_free_spec.
  Qed.

  Variable Lay0F : word -> lib_layout.
  Variable LS0F : word -> lib_statics.
  Hypothesis DLL0 : forall sp, valid_sp sp -> Pm10DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst10.L0 (bv_unsigned sp)).
  Hypothesis LIB0 : forall sp, valid_sp sp -> lib_iface_ok_fp (Lay0F sp) cfg0 (PmHeapInst10.HI0 (bv_unsigned sp)) (LS0F sp).
  Hypothesis LX0 : forall sp, valid_sp sp -> Pm10DrvLibL.lib_exit_ok (LS0F sp).
  Hypothesis BUD0 : PmFinal.budget0_ok Lay0F.

  Theorem fuzz_json_cursor_asan_base_abort :
    strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_csrc9 IMG_tgt.
  Proof.
    exact (PmFinalSan.san_base_of_target_half Lay0F LS0F DLL0 LIB0 LX0 BUD0 IMG_tgt pm_casan_half).
  Qed.

  Theorem fuzz_json_cursor_asan_base_shipped :
    strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target IMG_csrc9 IMG_tgt.
  Proof.
    exact (PmFinalSan.shipped_base_of_target_half Lay0F LS0F DLL0 LIB0 LX0 BUD0 IMG_tgt pm_casan_half).
  Qed.

  Theorem fuzz_json_cursor_asan_base_scfg :
    strong_universal_error_free_T_scfg cfg0 IMG_csrc9 IMG_tgt.
  Proof.
    pose proof (Pm10HeapBridge.src0_realizes_spec_heap_lim cfg0 eq_refl eq_refl Lay0F LS0F DLL0 LIB0 LX0 BUD0 source_alloc_limit) as SRC.
    pose proof pm_casan_tgt as TGT.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
    specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw Hsv48).
    split; [| split].
    - eapply srealizes_error_free_big; [exact SRC | exact nbr_limit_source].
    - eapply srealizes_error_free_big; [exact TGT | exact nbr_limit_target].
    - intro tr.
      rewrite (srealizes_traces_iff_big cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC nbr_limit_source).
      rewrite (srealizes_traces_iff_big cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT nbr_limit_target).
      reflexivity.
  Qed.
End Hyps.
End FPX_1.
