From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit HaltsAllowed.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_knock Require Images.
From OSSVerify.libreac.fuzz_knock.images Require Ubsan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI14 YI5b YI5c YL01 YL0g YL0i YL0s YL0j YO0d_mf YO06_mf YL0j_mf.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import
  ZImage TraceHalting TraceHaltingB TraceHaltingMF ZTraceSpec ZTraceSpecMF AllocSlots AllocRoom ZComplete.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import DriverSlots.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Definition mf_alloc_facts {rc : RunCeil} (API : AllocAPI src0_msyms) : Prop :=
  (forall fx : FPState, @malloc_realizes fx rc MayFail src0_msyms (aa_MR API)) /\
  (forall fx : FPState, @free_realizes fx rc MayFail src0_msyms (aa_MR API)) /\
  (forall fx : FPState, @free_null_realizes fx MayFail src0_msyms).
Definition zlib_runtime_contracts_R_mf (LS : lib_shape) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop)
    (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\ mf_alloc_facts API /\
    @lib_contract_x_R_all MayFail rc LS src0_msyms API src0_sink_head src0_sink RI G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Definition zlib_runtime_contracts_G_mf (LS : lib_shape) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\ mf_alloc_facts API /\
    (forall (fx : FPState) (j : nat), (j < 4)%nat ->
       @lib_contract_x_G fx rc LS MayFail src0_msyms API src0_sink_head src0_sink G R GI f j LIBPC RA_LIB EMPTY LIB_STACK).
Theorem plain_halts_mf_from_runtime_contracts_R : forall (LS : lib_shape) RI G R GI f,
  shape_permitted LS ->
  (forall data, leaves (run_RI RI (payload data)) (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  zlib_runtime_contracts_R_mf LS RI G R GI f -> halts_may_fail Exits.any Images.ubsan.
Proof.
  intros LS RI G R GI f HLSP HDRV HG HR GIL GI0 HC. unfold halts_may_fail.
  intros [sp brk0 mbase rnd] inp Hentry Hinput.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp) source_alloc_limit).
  destruct (HC rc) as [API [AX [[HMm [HFm HFNm]] LX]]].
  change (must_exit_in_at_cfg may_fail_cfg zsegs Exits.any
    (init_config zsegs Ubsan.M.init_pc Ubsan.M.phdrs sp brk0 mbase rnd source_alloc_limit inp)).
  apply (realizes_must_exit_mf zsegs _ (SPECX_mf (LS:=LS) inp)).
  - apply (src0_realizes_specX_mf (rc:=rc) (LS:=LS) API AX HMm HFm HFNm GI RI f
      (G_local_T_mono src0segs G YL0k.src0_G GI HG GIL)
      (fun mem H => GI0 mem (G_img_mono src0segs G YL0k.src0_G mem HG H))
      (@lib_contract_x_R_all_mono MayFail rc LS src0_msyms API src0_sink_head src0_sink RI G YL0k.src0_G R YL0k.src0_R GI f
         LIBPC RA_LIB EMPTY LIB_STACK HG HR LX)
      HDRV sp brk0 mbase rnd source_alloc_limit inp Hsp Hbrk Hmb Hfits Hinput).
    + apply SRC_LIM_MIN_le_source.
    + unfold rc. apply ceil_of_top_run.
    + unfold rc. reflexivity.
  - exact (checksum_SPECX_mf_exits_any HLSP inp).
  - reflexivity.
Qed.
Theorem plain_halts_mf_from_runtime_contracts_G : forall (LS : lib_shape) G R GI f,
  shape_permitted LS ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat mem) ->
  zlib_runtime_contracts_G_mf LS G R GI f -> halts_may_fail Exits.any Images.ubsan.
Proof.
  intros LS G R GI f HLSP HROOM HG HR GIL GI0 HC.
  apply (plain_halts_mf_from_runtime_contracts_R LS (@RI_G LS) G R (fun j T m => T = [] /\ GI j m) f HLSP).
  - exact (driver_RI_G LS HROOM).
  - exact HG.
  - exact HR.
  - exact (G_local_T_of_G src0segs G GI GIL).
  - intros mem H. exact (conj eq_refl (GI0 mem H)).
  - intros rc. destruct (HC rc) as [API [AX [MF LX]]]. exists API. split; [exact AX|]. split; [exact MF|].
    apply (@lib_contract_x_R_all_of_T MayFail rc LS src0_msyms API src0_sink_head src0_sink (@RI_G LS) G R _ f
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step LS GI)).
    exact (@lib_contract_x_T_all_of_G MayFail rc LS src0_msyms API src0_sink_head src0_sink G R GI f
      LIBPC RA_LIB EMPTY LIB_STACK LX).
Qed.
