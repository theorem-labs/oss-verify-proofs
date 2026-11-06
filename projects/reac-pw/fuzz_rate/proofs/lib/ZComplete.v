(* SPDX-License-Identifier: MIT *)
(** Composition for the unchanged full catalog statement.
    The remaining runtime contracts below are premises to be proved, not axioms
    and not an accepted proof of plain_halts. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_rate Require Statements Images.
From OSSVerify.reac_pw.fuzz_rate.images Require Plain.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI14 YI5b YI5c YL01 YL0g YL0i YL0s YL0j.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import
  ZImage TraceHalting TraceHaltingB ZTraceSpec AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import DriverSlots.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Definition zlib_runtime_contracts : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\
    lib_contract_x_all (rc:=rc) (LS:=checksum_shape)
      src0_msyms API LIBPC RA_LIB EMPTY LIB_STACK.
Definition zlib_runtime_contracts_G (LS : lib_shape) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\
    lib_contract_x_G_all (rc:=rc) (LS:=LS)
      src0_msyms API G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Definition zlib_runtime_contracts_R (LS : lib_shape) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\
    lib_contract_x_R_all (rc:=rc) (LS:=LS)
      src0_msyms API RI G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Lemma checksum_room_calls : forall n k,
  @room_calls checksum_shape n k SBD.
Proof.
  intros n k. induction k as [|k IH]; cbn [room_calls lib_room lib_delta checksum_shape]; [exact I|].
  split; [unfold SBD, CAPMAX; cbn [sb_live sb_bytes sb_cap]; lia | exact IH].
Qed.
Lemma valid_sp_window_for_ceil : forall sp,
  valid_sp sp -> sp_window_lo <= bv_unsigned sp <= sp_window_hi.
Proof. intros sp [Hlo [Hhi Hal]]. auto. Qed.
Lemma calls_witness : forall n, 0 <= n -> exists data, payload_len data = n /\ calls data = 4%nat.
Proof.
  intros n Hn. set (d := Z_to_bv 8 1 :: Z_to_bv 8 0 :: Z_to_bv 8 3 :: repeat (Z_to_bv 8 0) (Z.to_nat n + 4)).
  assert (Hc : config_len d = 1) by reflexivity.
  exists d. split.
  - unfold payload_len. rewrite Hc. unfold dlen, d, HDR_MIN. cbn [length]. rewrite repeat_length. lia.
  - reflexivity.
Qed.
Lemma driver_RI_G : forall (LS : lib_shape), (forall data, @room_calls LS (payload_len data) (calls data) SBD) ->
  forall data, leaves (run_RI (@RI_G LS) (payload data)) (driver_tree data).
Proof.
  intros LS HROOM data. eapply leaves_mono; [| exact (driver_slots data)].
  intros [d A] H. unfold run_slots, run_RI in *. cbn [fst snd] in *. destruct d; cbv beta iota in H |- *; try exact I.
  exists SBD. split; [exact H|].
  destruct (calls_witness (Z.of_nat (length (YO06.payload data))) (Nat2Z.is_nonneg _)) as (d' & Hd1 & Hd2).
  pose proof (HROOM d') as Hr. rewrite Hd1, Hd2 in Hr. exact Hr.
Qed.
Theorem plain_halts_from_runtime_contracts_R : forall (LS : lib_shape) RI G R GI f,
  shape_permitted LS ->
  (forall data, leaves (run_RI RI (payload data)) (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  zlib_runtime_contracts_R LS RI G R GI f -> Statements.plain_halts.
Proof.
  intros LS RI G R GI f HLSP HDRV HG HR GIL GI0 HC. unfold Statements.plain_halts, halts_within_budget.
  intros [sp brk0 mbase rnd] inp Hentry Hinput Hbudget.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp) Budgets.Standard.lim_source).
  destruct (HC rc) as [API [AX LX]].
  change (must_exit_in_at_cfg forced_only_cfg zsegs zallowed
    (init_config zsegs Plain.M.init_pc Plain.M.phdrs
      sp brk0 mbase rnd Budgets.Standard.lim_source inp)).
  eapply realizes_must_exit_forced_budget with (T:=SPECX (LS:=LS) inp).
  - apply (src0_realizes_specX (rc:=rc) (LS:=LS) API AX GI RI f
      (G_local_T_mono src0segs G YL0k.src0_G GI HG GIL)
      (fun mem H => GI0 mem (G_img_mono src0segs G YL0k.src0_G mem HG H))
      (lib_contract_x_R_all_mono src0_msyms API RI G YL0k.src0_G R YL0k.src0_R GI f LIBPC RA_LIB EMPTY LIB_STACK HG HR LX)
      driver_obligationsX_proved HDRV sp brk0 mbase rnd
      Budgets.Standard.lim_source inp Hsp Hbrk Hmb Hfits Hinput).
    + apply SRC_LIM_MIN_le_source.
    + unfold rc. apply ceil_of_top_run.
    + unfold rc. reflexivity.
  - apply (checksum_SPECX_exits_allowed HLSP).
  - reflexivity.
  - exact Hbudget.
Qed.
Theorem plain_halts_from_runtime_contracts_G : forall (LS : lib_shape) G R GI f,
  shape_permitted LS ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat mem) ->
  zlib_runtime_contracts_G LS G R GI f -> Statements.plain_halts.
Proof.
  intros LS G R GI f HLSP HROOM HG HR GIL GI0 HC.
  apply (plain_halts_from_runtime_contracts_R LS (@RI_G LS) G R (fun j T m => T = [] /\ GI j m) f HLSP).
  - exact (driver_RI_G LS HROOM).
  - exact HG.
  - exact HR.
  - exact (G_local_T_of_G src0segs G GI GIL).
  - intros mem H. exact (conj eq_refl (GI0 mem H)).
  - intros rc. destruct (HC rc) as [API [AX LX]]. exists API. split; [exact AX|].
    apply (lib_contract_x_R_all_of_T src0_msyms API (@RI_G LS) G R _ f LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step LS GI)).
    exact (lib_contract_x_T_all_of_G src0_msyms API G R GI f LIBPC RA_LIB EMPTY LIB_STACK LX).
Qed.
Theorem plain_halts_from_runtime_contracts :
  zlib_runtime_contracts -> Statements.plain_halts.
Proof.
  intros HC. apply (plain_halts_from_runtime_contracts_G checksum_shape [] [] (fun _ _ => True) (fun _ => [])).
  - exact checksum_permitted.
  - intros data. apply checksum_room_calls.
  - intros a Ha. destruct (in_globals_nil a Ha).
  - intros a Ha. destruct (in_globals_nil a Ha).
  - apply G_local_True.
  - intros mem _. exact I.
  - intros rc. destruct (HC rc) as [API [AX LX]]. exists API. split; [exact AX|].
    apply lib_contract_x_G_all_of_x. exact LX.
Qed.
