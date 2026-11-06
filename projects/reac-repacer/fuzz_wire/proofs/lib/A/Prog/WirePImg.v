(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/DecodeImg.v (itself from proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v, from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v) for reac-repacer/fuzz_uci's image A: the code table of fuzz_uci.asan's program code (the listing's own base uci_text and its uci_nslots words), one value table over lib/A/Prog/UciPAddr.v's addresses, the listing's 10 objects and program-function addresses (uci_xcalls); the image is the core's tfibsegs (lib/A/AB1v.v) and its bounds the notations of lib/Reusable/YImgTop.v, so the page arithmetic (seg_lo .. page_up) that fuzz_decode's YImgTop defines is stated here and checked against the image by vm_compute; module paths changed. *)
(* WirePImg: facts about fuzz_wire.asan's image that the statements and the closing file use, in the form of the
   image part of fuzz_uci's lib/A/Prog/UciPImg.v: every loaded segment lies inside [IMG_LO, IMG_TOP) and below
   kLowMemEnd, IMG_TOP is the page above the highest loaded byte, the layout's image window covers the image; and, per
   program function of lib/A/Prog/WirePSyms.v, its end (wire_end), the frame it opens at entry (wire_frame) and the
   realignment below that frame (wire_realign), checked against the core's function table lib/A/AB1w.v. The page
   arithmetic is stated here and checked against the image by vm_compute, since this unit's YImgTop.v states IMG_LO
   and IMG_TOP as numerals. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AB1w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WirePList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module AB := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.AB1w.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).
Definition img_hi_of (l : list Segment) : Z := fold_right (fun s acc => Z.max (seg_hi s) acc) 0 l.
Definition page_up (x : Z) : Z := (x + 4095) / 4096 * 4096.
Definition wire_segs_in (l : list Segment) : bool :=
forallb (fun s => (IMG_LO <=? seg_lo s) && (seg_hi s <=? IMG_TOP)) l.
Lemma wire_segs_in_ok : wire_segs_in tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wire_img_top : IMG_TOP = page_up (img_hi_of tfibsegs).
Proof. vm_compute. reflexivity. Qed.

(* Every loaded segment of image A lies inside the unit's image bounds (wire_segs_in_ok). *)
Lemma wire_img_range : forall a, in_img tfibsegs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
pose proof wire_segs_in_ok as Hall. unfold wire_segs_in in Hall. rewrite forallb_forall in Hall.
pose proof (Hall sg Hin) as Hb. apply andb_true_iff in Hb as [Hlo Hhi].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold seg_lo, seg_hi in Hlo, Hhi. lia.
Qed.
Lemma wire_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a Ha. pose proof (wire_img_range a Ha) as [H1 H2]. unfold kLowMemEnd. lia.
Qed.
(* No read-only-after-relocation range is used by this image's walks: the range is empty. *)
Lemma wire_relro_img : forall a, 0 <= a < 0 -> in_img tfibsegs a.
Proof. intros a Ha. exfalso. lia. Qed.

(* The image hull of A is inside the layout's image window: the window starts at kImgLo = IMG_LO and its size is
   page-aligned, so it reaches the page above A's highest loaded byte, which is IMG_TOP. *)
Lemma img_hi_le : forall l T, 0 <= T -> Forall (fun sg => seg_hi sg <= T) l -> img_hi_of l <= T.
Proof.
intros l T HT H. induction H as [|sg l Hsg Hl IH]; cbn [img_hi_of fold_right]; [exact HT|].
unfold img_hi_of in IH. lia.
Qed.
(* A page-aligned window that reaches x reaches the page above x. *)
Lemma page_up_le : forall x T, 0 <= x -> x <= T -> T mod 4096 = 0 -> page_up x <= T.
Proof.
intros x T Hx HxT HT. unfold page_up.
destruct (proj1 (Z.mod_divide T 4096 ltac:(lia)) HT) as [q Hq].
assert (Hlt : (x + 4095) / 4096 < q + 1) by (apply Z.div_lt_upper_bound; lia).
assert (Hq0 : 0 <= q) by (destruct (Z.le_gt_cases 0 q) as [|Hn]; [exact H | exfalso; lia]).
rewrite Hq. apply Z.mul_le_mono_nonneg_r; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wire_img_cover : forall ly S md, layout_ok ly -> ALedger tfibsegs ly S md ->
fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LO LG.
pose proof (lo_img _ LO) as (J0 & J1 & J2 & J3).
assert (EK : kImgLo mod 4096 = 0) by reflexivity.
assert (HA : img_hi_of tfibsegs <= fst (ly_img ly) + snd (ly_img ly)).
{ apply img_hi_le; [rewrite J0; unfold kImgLo; lia|]. apply Forall_forall. intros sg Hsg.
  pose proof (al_img _ _ _ _ LG sg Hsg) as [_ H2]. unfold seg_hi. lia. }
unfold page_aligned in J3.
assert (HTal : (fst (ly_img ly) + snd (ly_img ly)) mod 4096 = 0).
{ rewrite J0, Z.add_mod by lia. rewrite J3, EK. reflexivity. }
split; [rewrite J0; unfold kImgLo; lia|].
rewrite wire_img_top. apply page_up_le; [vm_compute; discriminate | exact HA | exact HTal].
Qed.
End c.

(* The entry of LLVMFuzzerTestOneInput, the listing's base (WirePList.v AF_LLVMFuzzerTestOneInput = 0). *)
Definition WIRE_A_LLVMF : Z := wire_text + AF_LLVMFuzzerTestOneInput.

(* The end of each program function of the listing (0 for a runtime entry): its symbol's start + st_size in the
   unstripped twin. *)
Definition wire_end (s : wsym) : Z :=
match s with
| WS_check_forward => 0x80154
| WS_check_ret => 0x801fc
| WS_check_downstream => 0x80340
| WS_check_meter => 0x80660
| WS_check_counter => 0x80708
| WS_check_width => 0x8077c
| WS_check_read => 0x80c38
| WS_check_copy => 0x80e8c
| WS_rp_fwd_class => 0x80fe0
| WS_rp_ret_accept => 0x8106c
| WS_rp_ds_accept => 0x81168
| WS_rp_meter_counter => 0x812f4
| WS_rp_counter => 0x8136c
| WS_rp_frame_channels => 0x813e0
| WS_rp_copy_untag => 0x81554
| WS_rp_slot_width => 0x8160c
| WS_rp_slot_read => 0x817bc
| WS_reac_frame_is_reac => 0x81854
| WS_reac_frame_clean_len => 0x81894
| _ => 0
end.
Definition WIRE_E_LLVMF : Z := 0x7fff0.

(* The frame each program function opens at its entry, the N of `addi sp, sp, -N` at +0x0 (0 for a runtime entry
   and for reac_frame_clean_len, which opens none). LLVMFuzzerTestOneInput opens 0x40. *)
Definition wire_frame (s : wsym) : Z :=
match s with
| WS_check_forward => 0x30
| WS_check_ret => 0x10
| WS_check_downstream => 0x10
| WS_check_meter => 0x80
| WS_check_counter => 0x20
| WS_check_width => 0x10
| WS_check_read => 0x80
| WS_check_copy => 0x40
| WS_rp_fwd_class => 0x10
| WS_rp_ret_accept => 0x10
| WS_rp_ds_accept => 0x10
| WS_rp_meter_counter => 0x10
| WS_rp_counter => 0x10
| WS_rp_frame_channels => 0x10
| WS_rp_copy_untag => 0x20
| WS_rp_slot_width => 0x10
| WS_rp_slot_read => 0x30
| _ => 0
end.
Definition WIRE_LLVMF_FRAME : Z := 0x40.

(* check_meter (+0x3c) and check_read (+0x40) realign sp to 32 bytes after the frame (`andi sp, sp, -0x20`): at most
   0x10 more bytes below entry - frame. *)
Definition wire_realign (s : wsym) : Z :=
match s with
| WS_check_meter => 0x10
| WS_check_read => 0x10
| _ => 0
end.

(* The starts, ends and offsets agree with the core's function table and with the listing. *)
Lemma wire_sigma_ab1w :
  WIRE_A_LLVMF = AB.tfib_A_LLVMFuzzerTestOneInput /\ WIRE_E_LLVMF = AB.tfib_E_LLVMFuzzerTestOneInput /\
  wire_sigma WS_check_forward = AB.tfib_A_check_forward /\ wire_end WS_check_forward = AB.tfib_E_check_forward /\
  wire_sigma WS_check_ret = AB.tfib_A_check_ret /\ wire_end WS_check_ret = AB.tfib_E_check_ret /\
  wire_sigma WS_check_downstream = AB.tfib_A_check_downstream /\
  wire_end WS_check_downstream = AB.tfib_E_check_downstream /\
  wire_sigma WS_check_meter = AB.tfib_A_check_meter /\ wire_end WS_check_meter = AB.tfib_E_check_meter /\
  wire_sigma WS_check_counter = AB.tfib_A_check_counter /\ wire_end WS_check_counter = AB.tfib_E_check_counter /\
  wire_sigma WS_check_width = AB.tfib_A_check_width /\ wire_end WS_check_width = AB.tfib_E_check_width /\
  wire_sigma WS_check_read = AB.tfib_A_check_read /\ wire_end WS_check_read = AB.tfib_E_check_read /\
  wire_sigma WS_check_copy = AB.tfib_A_check_copy /\ wire_end WS_check_copy = AB.tfib_E_check_copy /\
  wire_sigma WS_rp_fwd_class = AB.tfib_A_rp_fwd_class /\ wire_end WS_rp_fwd_class = AB.tfib_E_rp_fwd_class /\
  wire_sigma WS_rp_ret_accept = AB.tfib_A_rp_ret_accept /\ wire_end WS_rp_ret_accept = AB.tfib_E_rp_ret_accept /\
  wire_sigma WS_rp_ds_accept = AB.tfib_A_rp_ds_accept /\ wire_end WS_rp_ds_accept = AB.tfib_E_rp_ds_accept /\
  wire_sigma WS_rp_meter_counter = AB.tfib_A_rp_meter_counter /\
  wire_end WS_rp_meter_counter = AB.tfib_E_rp_meter_counter /\
  wire_sigma WS_rp_counter = AB.tfib_A_rp_counter /\ wire_end WS_rp_counter = AB.tfib_E_rp_counter /\
  wire_sigma WS_rp_frame_channels = AB.tfib_A_rp_frame_channels /\
  wire_end WS_rp_frame_channels = AB.tfib_E_rp_frame_channels /\
  wire_sigma WS_rp_copy_untag = AB.tfib_A_rp_copy_untag /\ wire_end WS_rp_copy_untag = AB.tfib_E_rp_copy_untag /\
  wire_sigma WS_rp_slot_width = AB.tfib_A_rp_slot_width /\ wire_end WS_rp_slot_width = AB.tfib_E_rp_slot_width /\
  wire_sigma WS_rp_slot_read = AB.tfib_A_rp_slot_read /\ wire_end WS_rp_slot_read = AB.tfib_E_rp_slot_read /\
  wire_sigma WS_reac_frame_is_reac = AB.tfib_A_reac_frame_is_reac /\
  wire_end WS_reac_frame_is_reac = AB.tfib_E_reac_frame_is_reac /\
  wire_sigma WS_reac_frame_clean_len = AB.tfib_A_reac_frame_clean_len /\
  wire_end WS_reac_frame_clean_len = AB.tfib_E_reac_frame_clean_len /\
  wire_sigma WS___interceptor_trampoline_malloc = AB.tfib_A_malloc /\
  wire_sigma WS___interceptor_trampoline_free = AB.tfib_A_free /\
  wire_sigma WS___asan_memcpy = AB.tfib_A_asan_memcpy /\
  wire_sigma WS___asan_memset = AB.tfib_A_asan_memset /\
  wire_sigma WS___asan_stack_malloc_0 = AB.tfib_A_asan_stack_malloc_0 /\
  wire_sigma WS___asan_stack_malloc_1 = AB.tfib_A_asan_stack_malloc_1 /\
  wire_sigma WS___asan_report_load1 = AB.tfib_A_asan_report_load1 /\
  wire_sigma WS___asan_report_store2 = AB.tfib_A_asan_report_store2 /\
  wire_sigma WS___asan_report_store4 = AB.tfib_A_asan_report_store4 /\
  wire_sigma WS_check_forward = wire_text + AF_check_forward /\
  wire_sigma WS_check_ret = wire_text + AF_check_ret /\
  wire_sigma WS_check_downstream = wire_text + AF_check_downstream /\
  wire_sigma WS_check_meter = wire_text + AF_check_meter /\
  wire_sigma WS_check_counter = wire_text + AF_check_counter /\
  wire_sigma WS_check_width = wire_text + AF_check_width /\
  wire_sigma WS_check_read = wire_text + AF_check_read /\
  wire_sigma WS_check_copy = wire_text + AF_check_copy /\
  wire_sigma WS_rp_fwd_class = wire_text + AF_rp_fwd_class /\
  wire_sigma WS_rp_ret_accept = wire_text + AF_rp_ret_accept /\
  wire_sigma WS_rp_ds_accept = wire_text + AF_rp_ds_accept /\
  wire_sigma WS_rp_meter_counter = wire_text + AF_rp_meter_counter /\
  wire_sigma WS_rp_counter = wire_text + AF_rp_counter /\
  wire_sigma WS_rp_frame_channels = wire_text + AF_rp_frame_channels /\
  wire_sigma WS_rp_copy_untag = wire_text + AF_rp_copy_untag /\
  wire_sigma WS_rp_slot_width = wire_text + AF_rp_slot_width /\
  wire_sigma WS_rp_slot_read = wire_text + AF_rp_slot_read /\
  wire_sigma WS_reac_frame_is_reac = wire_text + AF_reac_frame_is_reac /\
  wire_sigma WS_reac_frame_clean_len = wire_text + AF_reac_frame_clean_len.
Proof. repeat split; reflexivity. Qed.
