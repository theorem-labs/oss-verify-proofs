(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP ImgA ImgSame.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg Spec SpecNoKill ShapeEF ShapeEFS
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanLibNode AsanPlan AsanPlanSound AsanPlanImages AsanPlanImagesInit
  AsanInit AsanStartup AsanNodesArg AsanNodesIO AsanMainLib AsanShape AsanMainDefs AsanMain AsanMainClosed AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Record asan_certs : Type := ASAN_CERTS {
  ac_IT0 : itab;                                  (* [comment removed for export] *)
  ac_IT0_ok : itab_sound ASEGS ac_IT0;            (* [comment removed for export] *)
  ac_HS : nat -> option acs;                      (* [comment removed for export] *)
  ac_plan : plan;                                 (* [comment removed for export] *)
  ac_shape : shape;                               (* [comment removed for export] *)
  ac_KC0 : nat; ac_BFUEL : nat; ac_FUEL : nat;
  ac_TT0 : nat -> option (acs * plan * shape);      (* [comment removed for export] *)
  ac_TT0_ok : AP.tails_ok0 ASEGS ac_IT0 ASAN NX0 AsanInit.LIMIT ac_TT0 ac_KC0;   (* [comment removed for export] *)
  ac_cert : check ASEGS ac_IT0 ASAN NX0 AsanInit.LIMIT (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 ac_HS HL0 ac_TT0 ac_KC0 ac_BFUEL ac_FUEL None asan_init ac_plan = COk ac_shape;   (* [comment removed for export] *)
  ac_all_holes : all_holes ac_shape = true;
  ac_noblob : forall h ch, ac_HS h = Some ch -> acs_noblob ch = true;   (* [comment removed for export] *)
  ac_KCm : nat; ac_BFUELm : nat; ac_FUELm : nat;  (* [comment removed for export] *)
  ac_ITm : itab;                                  (* [comment removed for export] *)
  ac_ITm_ok : itab_sound ASEGS ac_ITm;
  ac_TTm : nat -> option (acs * plan * shape);      (* [comment removed for export] *)
  ac_TTm_ok : tails_all_ok ac_KCm ac_BFUELm ac_FUELm ac_ITm ac_TTm;   (* [comment removed for export] *)
  ac_TREE : nat -> nat -> mtree;                  (* [comment removed for export] *)
  ac_TREES : forall h ch i, ac_HS h = Some ch -> (i < 6)%nat ->
               mtree_ok ac_KCm ac_BFUELm ac_FUELm ac_ITm ac_TTm 0 0 (HSA ac_HS h) (root_class i) (ac_TREE h i) = true
}.

(* [comment removed for export] *)
Record asan_obls : Type := ASAN_OBLS {
  ao_LINV : (word -> option byte) -> Prop;
  ao_linv : LINV_STMT ao_LINV;      (* [comment removed for export] *)
  ao_xall : XALL_STMT ao_LINV;      (* [comment removed for export] *)
  ao_xlib : XLIB_STMT ao_LINV;      (* [comment removed for export] *)
  ao_xarg : XARG_STMT ao_LINV;      (* [comment removed for export] *)
  ao_xrp : XRP_STMT ao_LINV         (* [comment removed for export] *)
}.


Definition plain_stmt : Prop :=
  forall (sp brk mbase : word) (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk ImgP.M.loaded_segments brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes ImgP.M.loaded_segments
      (init_config ImgP.M.loaded_segments ImgP.M.init_pc ImgP.M.phdrs sp brk mbase rdraw sanitizer_source_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Section Top.
  Hypothesis HPLAIN : plain_stmt.
  Variable O : asan_obls.
  Variable C : asan_certs.

  (* [comment removed for export] *)
  Lemma asan_side : forall (asp abrk amb : word) (arnd : EntryDraw) (inp : ProcInput),
    valid_sp asp -> valid_brk ImgA.M.loaded_segments abrk -> entry_stack_fits asp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    srealizes ImgA.M.loaded_segments
      (init_config ImgA.M.loaded_segments ImgA.M.init_pc ImgA.M.phdrs asp abrk amb arnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Huid Hhw Hva.
    destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abort va ur tmp]. cbn in *. subst va.
    exact (asan_realizes_spec_closed (ao_LINV O) (ao_linv O) (ao_xall O) (ao_xlib O) (ao_xarg O) (ao_xrp O)
             asp arnd abrk amb argv envp (fs_seed_tmp ifs tmp) stdin uid gid hw nofile sigmask abort groups net ur
             Hasp Habrk Hargv Henvp Hafit Huid Hhw
             (ac_IT0 C) (ac_IT0_ok C)
             (ac_HS C) (ac_plan C) (ac_shape C) (ac_KC0 C) (ac_BFUEL C) (ac_FUEL C) (ac_TT0 C) (ac_cert C) (ac_TT0_ok C) (ac_all_holes C) (ac_noblob C)
             (ac_KCm C) (ac_BFUELm C) (ac_FUELm C) (ac_ITm C) (ac_TTm C) (ac_ITm_ok C) (ac_TTm_ok C)
             (ac_TREE C) (ac_TREES C)).
  Qed.

  
  Theorem asan_top_abort :
    strong_universal_error_free_T_budgets_abort SanitizerBudgets.lim_source SanitizerBudgets.lim_target image_P image_A.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & [Huid Hgid] & Hnofile & Hsigmask & Hhw & Habort & _).
    unfold strong_equiv_error_free_budgets_abort, SanitizerBudgets.lim_source, SanitizerBudgets.lim_target.
    apply (shape_strong_equiv_efs_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (HPLAIN rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
    - exact (asan_side asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Huid Hhw Hsv48).
    - apply spec_no_kill.
  Qed.
End Top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
