From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_link Require Statements Images.
From OSSVerify.reac_pw.fuzz_link.images Require Plain.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI14 YI5b YI5c YL01 YL0g YL0i YL0s YL0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import
  ZImage TraceHalting TraceHaltingB ZTraceSpec AllocSlots AllocRoom ZComplete Agree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFileSink MemFile StdioExitMF.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Theorem plain_rz_of_contracts_R : forall (LS : lib_shape) RI G R GI f,
  (forall data, leaves (run_RI RI (payload data)) (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  (forall j T m, GI j T m -> mf_gi src0_msyms link_mf T m) ->
  zlib_runtime_contracts_R LS RI G R GI f ->
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
    rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=LS) inp).
Proof.
  intros LS RI G R GI f HDRV HG HR GIL GI0 GImf HC [sp brk0 mbase rnd] inp Hentry Hinput.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  destruct (HC rc) as [API [AX [MWC LX]]].
  change (realizes zsegs (init_config zsegs Plain.M.init_pc Plain.M.phdrs
    sp brk0 mbase rnd Budgets.Standard.lim_source inp) (SPECX (LS:=LS) inp)).
  apply (src0_realizes_specX (rc:=rc) (LS:=LS) API AX GI RI f
    (G_local_T_mono src0segs G YL0k.src0_G GI HG GIL)
    (fun mem H => GI0 mem (G_img_mono src0segs G YL0k.src0_G mem HG H))
    GImf MWC
    (lib_contract_x_R_all_mono src0_msyms API RI G YL0k.src0_G R YL0k.src0_R GI f LIBPC RA_LIB EMPTY LIB_STACK HG HR LX)
    driver_obligationsX_proved HDRV sp brk0 mbase rnd
    Budgets.Standard.lim_source inp Hsp Hbrk Hmb Hfits Hinput).
  - apply SRC_LIM_MIN_le_source.
  - unfold rc. apply ceil_of_top_run.
Qed.
Definition ubsan_realizes_specX (LS : lib_shape) : Prop :=
  forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
    rz_run Images.ubsan Budgets.Standard.lim_target en inp (SPECX (LS:=LS) inp).
Definition ubsan_cut_free : Prop :=
  forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
    cf_run Images.ubsan Budgets.Standard.lim_target en inp.
Theorem ubsan_agrees_of_cut_free : forall (LS : lib_shape) RI G R GI f,
  (forall data, leaves (run_RI RI (payload data)) (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  (forall j T m, GI j T m -> mf_gi src0_msyms link_mf T m) ->
  zlib_runtime_contracts_R LS RI G R GI f ->
  ubsan_realizes_specX LS -> ubsan_cut_free -> Statements.ubsan_agrees.
Proof.
  intros LS RI G R GI f HDRV HG HR GIL GI0 GImf HC HU HUC.
  unfold Statements.ubsan_agrees, agrees_in. intros en_p en_s inp Hp Hs Hinput Hbud.
  exact (agree_frame Images.plain Budgets.Standard.lim_source en_p Images.ubsan Budgets.Standard.lim_target en_s inp
    (SPECX (LS:=LS) inp) (SPECX (LS:=LS) inp)
    (plain_rz_of_contracts_R LS RI G R GI f HDRV HG HR GIL GI0 GImf HC en_p inp Hp Hinput)
    (HU en_s inp Hs Hinput) (t_eq_refl _)
    (cf_run_of_budget Images.plain Budgets.Standard.lim_source en_p inp Hbud) (HUC en_s inp Hs Hinput)).
Qed.
