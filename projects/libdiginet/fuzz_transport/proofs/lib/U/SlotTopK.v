(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/SlotTopK.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YH00 YH02 YI5b YI5c YL0g YL0i YL0k YL0s DriverSlots.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import ZTraceSpec ZComplete ZAllocator Img0 AllocSlots SlotTopR.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Export SlotKept.
Import ListNotations.
Open Scope Z_scope.
Definition TB_room (LS : lib_shape) : Prop :=
  forall T, (length T <= TBMAX)%nat -> (forall t k, In (t, k) T -> 0 < k <= TBBYTES) ->
    forall n, @lib_room LS (TD [] T SBD) n.
Definition zlib_contract_T (LS : lib_shape) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) : Prop :=
  forall rc : RunCeil, @lib_contract_x_T_all rc LS src0_msyms (@zlib_API rc)
    src0_sink_head src0_sink G R GI f LIBPC RA_LIB EMPTY LIB_STACK.
Definition RI_K (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate) : Prop := res_ok_slots A (TD [] T SBD).
Lemma driver_RI_K : forall data, leaves (run_RI RI_K (payload data)) (driver_tree data).
Proof.
  intros data. eapply leaves_mono; [| exact (driver_slots data)].
  intros [d A] H. unfold run_slots, run_RI, RI_K in *. cbn [fst snd] in *. destruct d; cbv beta iota in H |- *; try exact I. exact H.
Qed.
Lemma RI_K_step : forall (LS : lib_shape) GI, (forall n b, @lib_delta LS n b = b) -> TB_room LS -> TB_bound GI ->
  forall j, (j < 4)%nat -> forall pl T A m, RI_K pl j T A -> GI j T m ->
  exists b, res_ok_slots A b /\ @lib_room LS b (Z.of_nat (length pl)) /\
  forall T' A' m', res_ok_slots A' (TD T T' (@lib_delta LS (Z.of_nat (length pl)) b)) -> GI (S j) T' m' -> RI_K pl (S j) T' A'.
Proof.
  intros LS GI HD HR HB j _ pl T A m HA HGI. destruct (HB j T m HGI) as [H1 H2].
  exists (TD [] T SBD). split; [exact HA|]. split; [exact (HR T H1 H2 _)|].
  intros T' A' m' HA' _. unfold RI_K. rewrite HD, TD_chain in HA'. exact HA'.
Qed.
Theorem plain_halts_from_slot_T : forall (LS : lib_shape) G R GI f,
  shape_permitted LS ->
  (forall n b, @lib_delta LS n b = b) ->
  TB_room LS ->
  (forall a, in_globals G a -> in_globals src0_G a) ->
  (forall a, in_globals R a -> in_globals src0_R a) ->
  G_local_T src0segs G GI ->
  (forall mem, G_img src0segs G mem -> GI 0%nat [] mem) ->
  TB_bound GI ->
  zlib_contract_T LS G R GI f -> Statements.ubsan_halts.
Proof.
  intros LS G R GI f HLSP HD HR HG HRR GIL GI0 HB H.
  apply (plain_halts_from_slot_R LS RI_K G R GI f HLSP driver_RI_K HG HRR GIL GI0).
  intros rc. exact (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) RI_K G R GI f LIBPC RA_LIB EMPTY LIB_STACK
    (RI_K_step LS GI HD HR HB) (H rc)).
Qed.
