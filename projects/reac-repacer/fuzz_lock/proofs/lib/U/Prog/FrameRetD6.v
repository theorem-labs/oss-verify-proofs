(* SPDX-License-Identifier: MIT *)
(* Modified by Theorem Labs: the twin of lib/U/ZComplete.v (the SPDX line), lib/U/SlotTopG.v and lib/U/FrameSlotG.v (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/U/ZComplete.v, lib/U/SlotTopG.v and lib/U/FrameSlotG.v
   at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.FrameRetD6. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_lock Require Statements Images.
From OSSVerify.reac_repacer.fuzz_lock.images Require Ubsan.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet FrameRetD1 FrameRetD2 FrameRetD3 FrameRetD5.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0d YO05 YO09 YO06 YO04
  YH00 YH02 YI14 YI5b YI5c YL01 YL0g YL0i YL0s YL0j.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import
  YP09 YI06 YI16 YL0k YN03 YN2b YN33.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import
  ZImage TraceHalting TraceHaltingB ZTraceSpec AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import
  ZComplete ZAllocator SlotTopG Contract FrameAPI FrameSlotG Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* FrameSlotG.v Bridge, for FrameRet.v lib_post_gr / lib_contract_gr *)
Section Bridge.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_post_x_G_r_of_gr : forall r G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_gr B API r G stk L A regs mem md p n b l L' A' regs' mem' md' ->
  lib_post_x_G_r B API r G [] stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof using.
  intros r G stk L A regs mem md p n b l L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H11 & H12 & H13 & H14 & H15 & H16 & _ & H17 & H18).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 H18))))))))))))))))).
Qed.
Lemma lib_contract_x_G_r_of_gr : forall rt G R GI j pc ra empty stk,
  lib_contract_gr B API rt G R GI j pc ra empty stk -> lib_contract_x_G_r B API rt G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros rt G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hpre)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_G_r_of_gr (rt pl) G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | exact HGI'].
Qed.
End Bridge.

#[local] Existing Instance YK11.fx0.

(* ZComplete.v zlib_runtime_contracts_G and zlib_runtime_contracts_R, for the return function rt *)
Definition zlib_runtime_contracts_G_r (LS : lib_shape) (rt : list byte -> Z) (G R : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\
    lib_contract_x_G_all_r (rc:=rc) (LS:=LS)
      src0_msyms API rt G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Definition zlib_runtime_contracts_R_r (LS : lib_shape) (rt : list byte -> Z)
    (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\
    lib_contract_x_R_all_r (rc:=rc) (LS:=LS)
      src0_msyms API rt RI G R GI f LIBPC RA_LIB EMPTY LIB_STACK.

(* ZComplete.v checksum_room_calls, for ret_shape rt *)
Lemma ret_room_calls : forall rt n k, @room_calls (ret_shape rt) n k SBD.
Proof.
  intros rt n k. induction k as [|k IH]; cbn [room_calls lib_room lib_delta ret_shape]; [exact I|].
  split; [unfold SBD, CAPMAX; cbn [sb_live sb_bytes sb_cap]; lia | exact IH].
Qed.

(* ZComplete.v plain_halts_from_runtime_contracts_R, with SPECX_r *)
Theorem plain_halts_from_runtime_contracts_R_r : forall (LS : lib_shape) rt RI G R GI f,
  shape_permitted LS ->
  (forall pl fs K, @LIBK LS pl fs K = K (LL (rt pl) fs [])) ->
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1 ->
  (forall data, leaves (run_RI RI (payload data)) (driver_tree data)) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  zlib_runtime_contracts_R_r LS rt RI G R GI f -> Statements.ubsan_halts.
Proof.
  intros LS rt RI G R GI f HLSP HLS HR01 ARMS HDRV HG HR GIL GI0 HC. unfold Statements.ubsan_halts, halts_within_budget.
  intros [sp brk0 mbase rnd] inp Hentry Hinput Hbudget.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  destruct (HC rc) as [API [AX LX]].
  change (must_exit_in_at_cfg forced_only_cfg zsegs zallowed
    (init_config zsegs Ubsan.M.init_pc Ubsan.M.phdrs
      sp brk0 mbase rnd Budgets.Standard.lim_source inp)).
  eapply realizes_must_exit_forced_budget with (T:=SPECX_r (LS:=LS) inp).
  - apply (src0_realizes_specX_r (rc:=rc) (LS:=LS) API AX GI RI f rt
      (G_local_T_mono src0segs G YL0k.src0_G GI HG GIL)
      (fun mem H => GI0 mem (G_img_mono src0segs G YL0k.src0_G mem HG H))
      (lib_contract_x_R_all_r_mono src0_msyms API rt RI G YL0k.src0_G R YL0k.src0_R GI f LIBPC RA_LIB EMPTY LIB_STACK HG HR LX)
      HLS HR01 ARMS HDRV sp brk0 mbase rnd
      Budgets.Standard.lim_source inp Hsp Hbrk Hmb Hfits Hinput).
    + apply SRC_LIM_MIN_le_source.
    + unfold rc. apply ceil_of_top_run.
  - apply (SPECX_r_exits_allowed HLSP).
  - reflexivity.
  - exact Hbudget.
Qed.

(* ZComplete.v plain_halts_from_runtime_contracts_G, for the return function rt *)
Theorem plain_halts_from_runtime_contracts_G_r : forall (LS : lib_shape) rt G R GI f,
  shape_permitted LS ->
  (forall pl fs K, @LIBK LS pl fs K = K (LL (rt pl) fs [])) ->
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1 ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD) ->
  (forall a, in_globals G a -> in_globals YL0k.src0_G a) ->
  (forall a, in_globals R a -> in_globals YL0k.src0_R a) ->
  G_local src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat mem) ->
  zlib_runtime_contracts_G_r LS rt G R GI f -> Statements.ubsan_halts.
Proof.
  intros LS rt G R GI f HLSP HLS HR01 ARMS HROOM HG HR GIL GI0 HC.
  apply (plain_halts_from_runtime_contracts_R_r LS rt (@RI_G LS) G R (fun j T m => T = [] /\ GI j m) f HLSP HLS HR01 ARMS).
  - exact (driver_RI_G LS HROOM).
  - exact HG.
  - exact HR.
  - exact (G_local_T_of_G src0segs G GI GIL).
  - intros mem H. exact (conj eq_refl (GI0 mem H)).
  - intros rc. destruct (HC rc) as [API [AX LX]]. exists API. split; [exact AX|].
    apply (lib_contract_x_R_all_r_of_T src0_msyms API rt (@RI_G LS) G R _ f LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step LS GI)).
    exact (lib_contract_x_T_all_r_of_G src0_msyms API rt G R GI f LIBPC RA_LIB EMPTY LIB_STACK LX).
Qed.

(* SlotTopG.v zlib_checksum_contract_G and plain_halts_from_slot_G, for the return function rt *)
Definition zlib_checksum_contract_G_r (LS : lib_shape) (rt : list byte -> Z) (G R : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, @lib_contract_x_G_all_r rc LS src0_msyms (@zlib_API rc)
    src0_sink_head src0_sink rt G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Theorem plain_halts_from_slot_G_r : forall (LS : lib_shape) rt G R GI f,
  shape_permitted LS ->
  (forall pl fs K, @LIBK LS pl fs K = K (LL (rt pl) fs [])) ->
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1 ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD) ->
  (forall a, in_globals G a -> in_globals src0_G a) ->
  (forall a, in_globals R a -> in_globals src0_R a) ->
  G_local src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat mem) ->
  zlib_checksum_contract_G_r LS rt G R GI f -> Statements.ubsan_halts.
Proof.
  intros LS rt G R GI f HLSP HLS HR01 ARMS HROOM HG HR GIL GI0 H.
  apply (plain_halts_from_runtime_contracts_G_r LS rt G R GI f HLSP HLS HR01 ARMS HROOM HG HR GIL GI0).
  intros rc. exists (@zlib_API rc). split; [apply zlib_allocator_extra | apply H].
Qed.

(* FrameSlotG.v plain_halts_of_frame_slot, for FrameRet.v lib_contract_gr rt and the shape ret_shape rt *)
Theorem plain_halts_of_frame_slot_r : forall (rt : list byte -> Z) (G : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop),
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1 ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gr fx rc (ret_shape rt) src0_msyms (@zlib_API rc) src0_sink_head src0_sink rt
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.ubsan_halts.
Proof.
  intros rt G GI HR01 ARMS HG GIL GI0 H.
  apply (plain_halts_from_slot_G_r (ret_shape rt) rt G frame_RELRO GI (fun _ => []) (ret_permitted rt)
    (fun pl fs K => eq_refl) HR01 ARMS (fun data => ret_room_calls rt _ _) (fun a h => frame_G_src0 a (HG a h))).
  - exact frame_RELRO_src0.
  - exact GIL.
  - exact GI0.
  - intros rc fx j Hj.
    exact (lib_contract_x_G_r_of_gr src0_msyms (@zlib_API rc) (zlib_tables rc) rt G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
