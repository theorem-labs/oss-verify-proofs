From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import Mem.
Import ListNotations.
Open Scope Z_scope.

(* The REAC frame facts fuzz_egress's functions read, as plain models (no image, no address).
   is_audio(f) / w_is_audio(f): f[16] == 0 && f[17] == 0 (src/repace_wire.c, fuzz/fuzz.h). *)
Definition frame_is_audio (bs : list byte) : bool :=
  (bv_unsigned (nth 16 bs (Z_to_bv 8 1)) =? 0) && (bv_unsigned (nth 17 bs (Z_to_bv 8 1)) =? 0).

(* w_width(len) (fuzz/fuzz.h): the even nch in 2..40 with len = 52 + 36 * nch or len = 52 + 36 * nch + 2, else -1. *)
Definition w_width_model (n : Z) : Z :=
  if ((n - 52) mod 72 =? 0) && (124 <=? n) && (n <=? 1492) then (n - 52) / 36
  else if ((n - 54) mod 72 =? 0) && (126 <=? n) && (n <=? 1494) then (n - 54) / 36
  else -1.

(* want_width(f, n, slot) (fuzz_egress.c:89-95). *)
Definition want_width_model (n : Z) (bs : list byte) (slot : Z) : Z :=
  let nch := w_width_model n in
  if (nch <? 0) || negb (frame_is_audio bs) || (slot <? 0) || (nch <=? slot) then -1 else nch.

(* The braid bytes of a slot (reac_braid_pos, libreac include/reac/reac_braid.h): for width nch and time-sample s, the
   slot's pair group starts at frame index 50 + 3 * (s * nch + (slot - slot mod 2)); an even slot's lo / mid / hi bytes
   are at +3 / +0 / +1, an odd slot's at +4 / +5 / +2. *)
Definition braid_at (nch slot s j : Z) : Z :=
  50 + 3 * (s * nch + (slot - slot mod 2)) +
  (if slot mod 2 =? 0 then (if j =? 0 then 3 else if j =? 1 then 0 else 1)
   else (if j =? 0 then 4 else if j =? 1 then 5 else 2)).

(* The frame after the writes of samples 0 .. t-1: sample s's bytes 0, 1, 2 of v (vbs, little-endian int32s) at
   braid_at s 0, 1, 2, in that order. *)
Fixpoint slot_write_upto (nch slot : Z) (vbs bs : list byte) (t : nat) : list byte :=
  match t with
  | O => bs
  | S t' =>
      let s := Z.of_nat t' in
      let L := slot_write_upto nch slot vbs bs t' in
      let L1 := upd_bytes L (Z.to_nat (braid_at nch slot s 0)) [nth (Z.to_nat (4 * s)) vbs (Z_to_bv 8 0)] in
      let L2 := upd_bytes L1 (Z.to_nat (braid_at nch slot s 1)) [nth (Z.to_nat (4 * s + 1)) vbs (Z_to_bv 8 0)] in
      upd_bytes L2 (Z.to_nat (braid_at nch slot s 2)) [nth (Z.to_nat (4 * s + 2)) vbs (Z_to_bv 8 0)]
  end.
