(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtBzPins.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 0 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4; the image-derived counts in the header comment recomputed for this image. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Rt/RtBzPins.v of this library by derive_y.py b7b132fb12a7: module paths lib.A -> lib.AU, the image module Asan -> AsanUbsan and Img0 -> Img0U, addresses moved from fuzz_headamp's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Rt/RtBzPins.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
(* G2 (rom_viewO from AR), the computed half: every read-only byte of this image (fuzz_headamp.asan-ubsan) that the runtime OWNS
   (as_owned_static, AU/YF0m.v Tfib_owned_static) is pinned to its image byte by a cell of the per-binary record's
   constant table (AU/YF0m.v Tfib_const_abs, whose header says the table ends with cells for exactly these bytes).
   This is what rom_viewO (A/Rt/RtBzHBase.v) asks beyond our contracts' rt_rom_view, which speaks only of the
   UNOWNED read-only bytes; RtBzAdapt.rom_viewO_of_ARm reads it off AR.

   Measured on this image (AU/YF0m.v): 52 non-empty intersections of the 77 owned ranges with the
   read-only load segments, 1272 bytes in all (the donor's comment gave fuzz_command.asan's counts); the file builds in
   about 4 s. Only the check itself names the image and the table: the two
   lemmas that use it are stated over any list, so that no proof here asks the kernel to unfold the image. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK04 YG00 YG0a YG01 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0m.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition seg_zr (s : Segment) : Z * Z := (Z.of_N (seg_base s), Z.of_N (seg_size s)).
Definition zisect (r q : Z * Z) : Z * Z :=
  (Z.max (fst r) (fst q), Z.min (fst r + snd r) (fst q + snd q) - Z.max (fst r) (fst q)).

(* each owned range met with each read-only segment (a writable segment contributes an empty range) *)
Definition ro_part (r : Z * Z) (s : Segment) : Z * Z := if seg_writable s then (0, 0) else zisect r (seg_zr s).
Definition owned_ro : list (Z * Z) := flat_map (fun r => map (ro_part r) tfibsegs) Tfib_owned_static.

Definition img_byte (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 a)).

(* a cell that covers [a] and holds the image's byte there *)
Definition pin_cell (a ib : Z) (c : acell) : bool :=
  match c_at c, c_val c with
  | ANum ca, AV (ANum v) =>
      if ((ca <=? a) && (a <? ca + Z.of_nat (c_w c)))%bool
      then YG0f.le_byte v (c_w c) (Z.to_nat (a - ca)) =? ib
      else false
  | _, _ => false
  end.

Definition pins_in (cs : list acell) (a : Z) : bool :=
  match img_byte a with
  | None => false
  | Some ib => existsb (pin_cell a ib) cs
  end.

Definition ranges_pinned (cs : list acell) (l : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun i => pins_in cs (fst r + Z.of_nat i)) (seq 0 (Z.to_nat (snd r)))) l.

Lemma owned_ro_pinned : ranges_pinned Tfib_const_abs owned_ro = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pins_of_ranges : forall cs l a, ranges_pinned cs l = true -> Exists (in_zr a) l -> pins_in cs a = true.
Proof.
  intros cs l a HP HE. apply Exists_exists in HE as (r & Hin & Hzr). unfold in_zr in Hzr.
  unfold ranges_pinned in HP.
  pose proof (proj1 (forallb_forall _ _) HP r Hin) as H1. cbv beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 (Z.to_nat (a - fst r))) as H2. cbv beta in H2.
  assert (Hi : In (Z.to_nat (a - fst r)) (seq 0 (Z.to_nat (snd r))))
    by (apply in_seq; lia).
  specialize (H2 Hi). rewrite Z2Nat.id in H2 by lia.
  replace (fst r + (a - fst r)) with a in H2 by lia. exact H2.
Qed.

Lemma in_owned_ro : forall r sg, In r Tfib_owned_static -> In sg tfibsegs -> seg_writable sg = false ->
  In (zisect r (seg_zr sg)) owned_ro.
Proof.
  intros r sg Hr Hs Hw. unfold owned_ro. apply in_flat_map. exists r. split; [exact Hr|].
  replace (zisect r (seg_zr sg)) with (ro_part r sg) by (unfold ro_part; rewrite Hw; reflexivity).
  apply in_map. exact Hs.
Qed.
