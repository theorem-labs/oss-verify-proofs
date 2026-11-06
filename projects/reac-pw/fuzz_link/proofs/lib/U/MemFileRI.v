(** * reac-pw/fuzz_link (UBSan): the kept FILE block in the slot's resource invariant.

    The frame's R-form top ([ZComplete.plain_halts_from_runtime_contracts_R]) takes a resource invariant
    [RI pl j T A] with a driver obligation ([leaves (run_RI RI (payload data)) (driver_tree data)]), and the
    T-form slot contract turns into the R form through [lib_contract_x_R_all_of_T] given RI's step
    (YL0i.v:455-461). [RI_G] (YL0i.v:84-85) only takes [T = []]; [RI_mf] takes the FILE block too:
    the allocator's blocks are bounded by the driver's bound plus the kept blocks ([TD [] T b0]), and [T] is
    empty or the one FILE block (which [mf_gi] forces). [mf_shape] is checksum_shape (the call returns 0 and
    writes nothing) with room for the kept block on top of the driver's bound [SBD]. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import
  YK11 YK15 YM05 YM02 YO0i YO0f YO0d YO05 YO09 YO06 YO04 YI16 YL0g YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import TraceHalting ZTraceSpec AllocSlots AllocRoom MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import DriverSlots.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition mf_shape : lib_shape := {|
  LIBK := @LIBK checksum_shape;
  LIBK_ext := @LIBK_ext checksum_shape;
  lib_delta := fun _ b => b;
  lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 + 2 ^ 11 /\ sb_cap b = CAPMAX |}.

Lemma mf_shape_permitted : shape_permitted mf_shape.
Proof. intros pl fs K HK. exact (checksum_permitted pl fs K HK). Qed.

Definition RI_mf (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate) : Prop :=
  exists b0, res_ok_slots A (TD [] T b0) /\
    0 <= sb_live b0 <= 63 /\ 0 <= sb_bytes b0 <= 2 ^ 28 /\ sb_cap b0 = CAPMAX /\
    (T = [] \/ exists f, T = [(f, MF_BLOCK)]).

(** RI's step, in the form [lib_contract_x_R_all_of_T] takes, for any slot GI with [mf_gi] as a conjunct. *)
Lemma RI_mf_step : forall (B : malloc_syms) {SH : sink_head} (MS : memfile_syms)
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall j T m, GI j T m -> mf_gi B MS T m) ->
  forall j, (j < 4)%nat -> forall pl T A m, RI_mf pl j T A -> GI j T m ->
  exists b, res_ok_slots A b /\ @lib_room mf_shape b (Z.of_nat (length pl)) /\
  forall T' A' m', res_ok_slots A' (TD T T' (@lib_delta mf_shape (Z.of_nat (length pl)) b)) ->
    GI (S j) T' m' -> RI_mf pl (S j) T' A'.
Proof.
  intros B SH MS GI HG j Hj pl T A m (b0 & Hb & Hl & Hy & Hc & HT) _.
  exists (TD [] T b0). split; [exact Hb|]. split.
  - cbn [lib_room mf_shape]. unfold TD. cbn [fold_left]. rewrite TD_malloc_form.
    destruct HT as [-> | (f & ->)]; cbn [length fold_right snd sb_live sb_bytes sb_cap Z.of_nat];
      unfold MF_BLOCK; lia.
  - intros T' A' m' Hb' HG'. exists b0. split.
    + cbn [lib_delta mf_shape] in Hb'. rewrite TD_chain in Hb'. exact Hb'.
    + split; [exact Hl|]. split; [exact Hy|]. split; [exact Hc|].
      destruct (HG _ _ _ HG') as [(_ & ->) | (f & _ & -> & _)]; [left; reflexivity | right; exists f; reflexivity].
Qed.

(** The driver's obligation for [RI_mf]: at every call of the driver tree the allocator is within [SBD]
    ([driver_slots]) and nothing is kept yet. *)
Lemma driver_RI_mf : forall data, leaves (run_RI RI_mf (payload data)) (driver_tree data).
Proof.
  intros data. eapply leaves_mono; [| exact (driver_slots data)].
  intros [d A] H. unfold run_slots, run_RI in *. cbn [fst snd] in *. destruct d; cbv beta iota in H |- *; try exact I.
  exists SBD. split; [exact H|]. unfold SBD, CAPMAX. cbn [sb_live sb_bytes sb_cap].
  split; [lia|]. split; [lia|]. split; [reflexivity|]. left. reflexivity.
Qed.

(** The FILE's malloc has room inside a call whenever the shape's room holds and the call's other live
    blocks leave one slot and 1304 bytes (the frame's malloc contract then returns non-zero). *)
Lemma mf_shape_room_file : forall b, @lib_room mf_shape b 0 -> sb_live b + 1 <= 64 ->
  sb_bytes b + MF_BLOCK <= 2 ^ 40 -> room_slots b MF_BLOCK.
Proof.
  intros b (H1 & H2 & H3) H4 H5. apply mf_room_slots; [unfold CAPMAX in *; lia | lia | exact H5].
Qed.

End a.
