(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0DrvLibL Src0DrvG Src0DrvMain Src0HeapBridge BigintTop2 L5Top BigintFinal KillFree BigintBaseH BigintBaseS0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct HeapIfaceA IcptIfaceAB0 LibIfaceA AsanInitK Bo0DefsK Bo0MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition as0_tgt_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    srealizes AsanUbsan.M.loaded_segments scfg
      (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Lemma as0_tgt_of_run : forall scfg,
  (forall sp brk0 mbase (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word)
          (net : NetQueue) (nofile sigmask : word) (abrt : bool) (ur : InputStream),
      valid_sp sp -> valid_brk ASEGS0 brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_fs fs ->
      srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                   (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
                (spec argv fs)) ->
  as0_tgt_stmt scfg.
Proof.
  intros scfg RUN sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hva Hve Hvfs Hcreds Hhw Hsv.
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va ur tmp].
  cbn [in_argv in_envp in_uid in_hwcap in_va_size] in *. subst va.
  destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
  exact (RUN sp brk mbase rdraw argv envp (in_fs (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt Sv48 ur tmp))
             stdin0 uid gid hw groups net nofile sigmask abt ur Hsp Hbrk Hva Hve Hfit Hu Hhw Hvfs).
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_both_final_abort :
  as0_tgt_stmt cfg0 ->
  strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros TGT.
  pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
                (fun sp => L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp)))
                (fun sp => L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))
                drv_lib_layout_top0 (LIB0_of_divide OPMOD1_src0_ok OPMOD2_src0_ok) budget0) as SRC.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
  specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
  specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds Hhw Hsv48).
  unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
  split; [| split].
  - eapply srealizes_error_free_unkilled; [exact SRC | apply kill_free_spec].
  - eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
  - intro tr.
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_both_base_abort_modulo :
  forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> LibIface.lib_statics) (BUDGET : Z),
    2 ^ 34 <= BUDGET -> BUDGET <= 2 ^ 39 - 2 ^ 35 ->
    inst_ok_stmt cfg0 L C BUDGET -> free_null_stmt cfg0 L BUDGET -> h4e_stmt BUDGET -> icpt_ok_stmt cfg0 L IL BUDGET -> lib_ok_stmt cfg0 L C IL Lay LSt -> dla_ok_stmt cfg0 L C IL -> drv_consts_stmt L C IL ->
    drv_main_stmt cfg0 L C IL Lay LSt -> usage_stmt cfg0 ->
    strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros L C IL Lay LSt BUDGET B1 B2 H1 H1n H2 H3 H4 H5 H6 H7 H8.
  apply fuzz_bigint_both_final_abort. apply as0_tgt_of_run.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
  exact (as0_realizes_spec_run cfg0 eq_refl eq_refl L C IL Lay LSt BUDGET B1 B2 H1 H1n H2 H3 H4 H5 H6 H7 H8
           sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs).
Qed.

End FPX_1.
