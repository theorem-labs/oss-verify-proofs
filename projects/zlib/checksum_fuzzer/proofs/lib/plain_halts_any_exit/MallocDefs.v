(* Written by the OSS-Fuzz proof collaborators. *)
(** * MallocDefs — shared pure definitions for the musl mallocng summaries
      (enframe / malloc side and free side).  No proofs about code here,
      only the arithmetic model.

    Layout reminders (reference binary): size_classes = u16[48] at rodata
    0x103b0; struct meta: +16 mem (group address M), +24 avail_mask (u32),
    +28 freed_mask (u32), +32 packed word W = last_idx[0..4] | freeable[5] |
    sizeclass[6..11] | maplen[12..63]; group: *(u64* )M = meta, slots start at
    M+16 ("storage"), slot [idx] at M + 16 + stride*idx, its [end] =
    start + stride - 4; user pointer p = start + 16*off; in-band header:
    p[-2..-1] = (p - M - 16)/16 (u16 "offset"), p[-3] = idx + 32*min(reserved,5),
    p[-4] = 0. UNIT = 16, IB = 4. *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Definition UNIT : Z := 16.
Definition IB : Z := 4.

(** musl's [size_classes] table (units of 16 bytes), 48 entries. *)
Definition size_classes : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 18; 20; 25; 31; 36; 42; 50; 63; 72; 84; 102; 127;
   146; 170; 204; 255; 292; 340; 409; 511; 584; 682; 818; 1023; 1169; 1364; 1637; 2047;
   2340; 2730; 3276; 4095; 4680; 5460; 6552; 8191].

Definition size_class (sc : Z) : Z := nth (Z.to_nat sc) size_classes 0.

(** Fields of the packed meta word W (meta+32). *)
Definition w_lastidx (W : Z) : Z := W mod 32.
Definition w_freeable (W : Z) : Z := (W / 32) mod 2.
Definition w_sizeclass (W : Z) : Z := (W / 64) mod 64.
Definition w_maplen (W : Z) : Z := W / 4096.

(** [get_stride]: a single-slot mmapped group spans its whole map. *)
Definition slot_stride (maplen lastidx sc : Z) : Z :=
  if (negb (maplen =? 0)) && (lastidx =? 0) then maplen * 4096 - UNIT else UNIT * size_class sc.

(** Slot geometry for group memory [M]. *)
Definition slot_start (M stride idx : Z) : Z := M + UNIT + stride * idx.
Definition slot_end (M stride idx : Z) : Z := slot_start M stride idx + stride - IB.

Lemma size_class_pos : forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros sc Hsc. unfold size_class.
  assert (E : exists k, (k < 48)%nat /\ Z.to_nat sc = k) by (exists (Z.to_nat sc); split; [lia|reflexivity]).
  destruct E as (k & Hk & ->).
  do 48 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* enframe: slot-offset cycling and the in-band sizes                  *)
(* ------------------------------------------------------------------------- *)

(** [slack] = number of spare 16-byte units in the slot for a request of [n]
    bytes: [(stride - IB - n) / UNIT]. *)
Definition slack_of (stride n : Z) : Z := (stride - IB - n) / UNIT.

(** musl's "m |= m>>1; m |= m>>2; m |= m>>4" on [slack]. *)
Definition smear (slack : Z) : Z :=
  let m1 := Z.lor slack (slack / 2) in
  let m2 := Z.lor m1 (m1 / 4) in
  Z.lor m2 (m2 / 16).

(** The offset (in UNITs) finally used by [enframe], from the candidate
    [off0] = ([p[-3]] <> 0 ? u16 [p[-2]] + 1 : ctr) mod 256.
    Always [0 <= enframe_off slack off0 <= slack] (RefEnframeArith). *)
Definition enframe_off (slack off0 : Z) : Z :=
  if off0 <=? slack then off0
  else let om := Z.land off0 (smear slack) in
       if slack <? om then om - slack - 1 else om.

(** [reserved] = end - p - n for the user pointer p = start + UNIT*off;
    the 3-bit code kept in p[-3] is [min reserved 5]. *)
Definition reserved_of (stride n off : Z) : Z := stride - IB - n - UNIT * off.
Definition res_code (reserved : Z) : Z := if reserved <? 5 then reserved else 5.

(** In-band u16 "offset" field of the user pointer: (p - M - 16)/16. *)
Definition inband_off (stride idx off : Z) : Z := (stride * idx) / UNIT + off.
