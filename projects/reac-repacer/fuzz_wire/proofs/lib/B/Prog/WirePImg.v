(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from reac-repacer/fuzz_uci's lib/B/Prog/UciPImg.v at recipes commit 0295462466b2 for reac-repacer/fuzz_wire's image B (fuzz_wire.asan-ubsan), with module paths and names changed (uci / Uci -> wire / Wire, usym -> wsym), the listing's 14 objects for fuzz_uci's 10, and, added here, per program function of lib/B/Prog/WirePSyms.v its end (wire_end), the frame it opens at entry (wire_frame) and the realignment below that frame (wire_realign), checked against the B core's function table lib/B/YB1w.v (wire_sigma_yb1w). fuzz_uci made that file from its lib/A/Prog/UciPImg.v at the same commit (itself from proofs/libreac/fuzz_decode/lib/A/Prog/DecodeImg.v at recipes commit 88154566652a, from proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v at 4f87de75d67 and proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v at 25e3d17bdb50), as fuzz_decode's lib/B/Prog/DecodeBImg.v at 88154566652a twins its lib/A/Prog/DecodeImg.v. This file is image B's: the code table of fuzz_wire.asan-ubsan's program code (the listing's own base wire_text, lib/B/Prog/WirePAddr.v, and its wire_nslots words, lib/B/Prog/WirePList.v), one value table over lib/B/Prog/WirePAddr.v's addresses, the listing's objects and program-function addresses (wire_xcalls, lib/B/Prog/WirePPa.v); the image is the B core's tfibsegs (lib/B/YB1v.v) and its bounds the notations of lib/B/YImgTop.v, each checked against the image by vm_compute; the image-generic Pa engine stays lib/A/Prog's. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePList WirePAddr WirePPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The page arithmetic of fuzz_decode's lib/Reusable/YImgTop.v, at this unit's image B: lib/B/YImgTop.v states
   IMG_LO and IMG_TOP as numerals, and the checks below decide by vm_compute that every loaded segment of
   fuzz_wire.asan-ubsan lies inside [IMG_LO, IMG_TOP) and that IMG_TOP is the page above its highest loaded byte. *)
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

(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition wiretbl : ctable :=
Eval vm_compute in (build_table tfibsegs wire_text wire_nslots TEmpty).
Lemma wiretbl_eq : wiretbl = build_table tfibsegs wire_text wire_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl wiretbl). Qed.
Lemma wiretbl_ok : table_ok tfibsegs wiretbl.
Proof. rewrite wiretbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* The listing's value table: slot A_TEXT is the listing's base, the A_OBJ block the objects, the A_HI block the
   auipc values, all of lib/B/Prog/WirePAddr.v. *)
Definition wire_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then wire_text else if (a <? A_HI 0)%nat then wire_obj (a - A_OBJ 0) else wire_hi (a - A_HI 0).
Lemma wire_lib_check : pi_check wsym (clookup wiretbl) wire_val wire_sigma wire_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma wire_val_range : forall a, 0 <= wire_val a < 2 ^ 64.
Proof.
intros a. unfold wire_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold wire_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 20 (destruct m as [|m]; [zlit|]). zlit.
- unfold wire_hi. generalize (a - A_HI 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma wire_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* Every loaded segment of image B lies inside the unit's image bounds (wire_segs_in_ok). *)
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
Lemma wire_xcalls_ok : forall s k, In (s, k) wire_xcalls -> wire_sigma s = wire_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (wire_sigma (fst p)) (wire_val A_TEXT + snd p)) wire_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.

(* The image hull of B is inside the layout's image window: the window starts at kImgLo = IMG_LO and its size is
   page-aligned, so it reaches the page above B's highest loaded byte, which is IMG_TOP. *)
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
#[global] Instance PI_wire : PAImg wire_listing := {|
pa_segs := tfibsegs;
pa_tbl := wiretbl;
pa_tbl_ok := wiretbl_ok;
pa_val := wire_val;
pa_sigma := wire_sigma;
pa_cert := wire_lib_check;
pa_B_ok := ltac:(unfold wire_val, wire_text; cbn; lia);
pa_val_range := wire_val_range;
pa_wx := wire_wx;
pa_segs_low := wire_segs_low;
pa_img_range := wire_img_range;
pa_img_cover := wire_img_cover;
pa_obj_img := ltac:(intros i Hi;
  do 14 (destruct i as [|i]; [unfold wire_val, wire_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0;
pa_relro_hi := 0;
pa_relro_img := wire_relro_img;
pa_xcalls := wire_xcalls_ok |}.
End c.

From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YB1w.
Module BW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.YB1w.

(* The entry of LLVMFuzzerTestOneInput, the listing's base (WirePList.v AF_LLVMFuzzerTestOneInput = 0). *)
Definition WIRE_A_LLVMF : Z := wire_text + AF_LLVMFuzzerTestOneInput.

(* The end of each program function of the listing (0 for a runtime entry): its symbol's start + st_size in the
   unstripped twin. *)
Definition wire_end (s : wsym) : Z :=
match s with
| WS_check_forward => 0x7ff2c
| WS_check_ret => 0x7ffe8
| WS_check_downstream => 0x8016c
| WS_check_meter => 0x804c0
| WS_check_counter => 0x8057c
| WS_check_width => 0x805f4
| WS_check_read => 0x80abc
| WS_check_copy => 0x80d64
| WS_rp_fwd_class => 0x80ee0
| WS_rp_ret_accept => 0x80f84
| WS_rp_ds_accept => 0x8103c
| WS_is_tagged_reac => 0x81144
| WS_rp_meter_counter => 0x81314
| WS_rp_counter => 0x813a0
| WS_rp_frame_channels => 0x81414
| WS_rp_copy_untag => 0x8151c
| WS_rp_slot_width => 0x815ec
| WS_rp_slot_read => 0x8183c
| WS_reac_frame_is_reac => 0x818e8
| WS_reac_frame_clean_len => 0x81928
| _ => 0
end.
Definition WIRE_E_LLVMF : Z := 0x7fda4.

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
| WS_check_read => 0xc0
| WS_check_copy => 0x40
| WS_rp_fwd_class => 0x10
| WS_rp_ret_accept => 0x10
| WS_rp_ds_accept => 0x10
| WS_is_tagged_reac => 0x10
| WS_rp_meter_counter => 0x10
| WS_rp_counter => 0x10
| WS_rp_frame_channels => 0x10
| WS_rp_copy_untag => 0x30
| WS_rp_slot_width => 0x10
| WS_rp_slot_read => 0x60
| WS_reac_frame_is_reac => 0x10
| _ => 0
end.
Definition WIRE_LLVMF_FRAME : Z := 0x40.

(* check_meter (+0x3c) and check_read (+0x40) realign sp to 32 bytes after the frame (`andi sp, sp, -0x20`): the
   entry sp and both frames are multiples of 16, so at most 0x10 more bytes below entry - frame. *)
Definition wire_realign (s : wsym) : Z :=
match s with
| WS_check_meter => 0x10
| WS_check_read => 0x10
| _ => 0
end.

(* The starts, ends and offsets agree with the B core's function table lib/B/YB1w.v and with the listing. *)
Lemma wire_sigma_yb1w :
  WIRE_A_LLVMF = BW.tfib_A_LLVMFuzzerTestOneInput /\
  WIRE_E_LLVMF = BW.tfib_E_LLVMFuzzerTestOneInput /\
  wire_sigma WS_check_forward = BW.tfib_A_check_forward /\
  wire_end WS_check_forward = BW.tfib_E_check_forward /\
  wire_sigma WS_check_ret = BW.tfib_A_check_ret /\
  wire_end WS_check_ret = BW.tfib_E_check_ret /\
  wire_sigma WS_check_downstream = BW.tfib_A_check_downstream /\
  wire_end WS_check_downstream = BW.tfib_E_check_downstream /\
  wire_sigma WS_check_meter = BW.tfib_A_check_meter /\
  wire_end WS_check_meter = BW.tfib_E_check_meter /\
  wire_sigma WS_check_counter = BW.tfib_A_check_counter /\
  wire_end WS_check_counter = BW.tfib_E_check_counter /\
  wire_sigma WS_check_width = BW.tfib_A_check_width /\
  wire_end WS_check_width = BW.tfib_E_check_width /\
  wire_sigma WS_check_read = BW.tfib_A_check_read /\
  wire_end WS_check_read = BW.tfib_E_check_read /\
  wire_sigma WS_check_copy = BW.tfib_A_check_copy /\
  wire_end WS_check_copy = BW.tfib_E_check_copy /\
  wire_sigma WS_rp_fwd_class = BW.tfib_A_rp_fwd_class /\
  wire_end WS_rp_fwd_class = BW.tfib_E_rp_fwd_class /\
  wire_sigma WS_rp_ret_accept = BW.tfib_A_rp_ret_accept /\
  wire_end WS_rp_ret_accept = BW.tfib_E_rp_ret_accept /\
  wire_sigma WS_rp_ds_accept = BW.tfib_A_rp_ds_accept /\
  wire_end WS_rp_ds_accept = BW.tfib_E_rp_ds_accept /\
  wire_sigma WS_is_tagged_reac = BW.tfib_A_is_tagged_reac /\
  wire_end WS_is_tagged_reac = BW.tfib_E_is_tagged_reac /\
  wire_sigma WS_rp_meter_counter = BW.tfib_A_rp_meter_counter /\
  wire_end WS_rp_meter_counter = BW.tfib_E_rp_meter_counter /\
  wire_sigma WS_rp_counter = BW.tfib_A_rp_counter /\
  wire_end WS_rp_counter = BW.tfib_E_rp_counter /\
  wire_sigma WS_rp_frame_channels = BW.tfib_A_rp_frame_channels /\
  wire_end WS_rp_frame_channels = BW.tfib_E_rp_frame_channels /\
  wire_sigma WS_rp_copy_untag = BW.tfib_A_rp_copy_untag /\
  wire_end WS_rp_copy_untag = BW.tfib_E_rp_copy_untag /\
  wire_sigma WS_rp_slot_width = BW.tfib_A_rp_slot_width /\
  wire_end WS_rp_slot_width = BW.tfib_E_rp_slot_width /\
  wire_sigma WS_rp_slot_read = BW.tfib_A_rp_slot_read /\
  wire_end WS_rp_slot_read = BW.tfib_E_rp_slot_read /\
  wire_sigma WS_reac_frame_is_reac = BW.tfib_A_reac_frame_is_reac /\
  wire_end WS_reac_frame_is_reac = BW.tfib_E_reac_frame_is_reac /\
  wire_sigma WS_reac_frame_clean_len = BW.tfib_A_reac_frame_clean_len /\
  wire_end WS_reac_frame_clean_len = BW.tfib_E_reac_frame_clean_len /\
  wire_sigma WS___interceptor_trampoline_malloc = BW.tfib_A_malloc /\
  wire_sigma WS___interceptor_trampoline_free = BW.tfib_A_free /\
  wire_sigma WS___asan_memcpy = BW.tfib_A_asan_memcpy /\
  wire_sigma WS___asan_stack_malloc_0 = BW.tfib_A_asan_stack_malloc_0 /\
  wire_sigma WS___asan_stack_malloc_1 = BW.tfib_A_asan_stack_malloc_1 /\
  wire_sigma WS___asan_report_load1 = BW.tfib_A_asan_report_load1 /\
  wire_sigma WS___asan_report_store2 = BW.tfib_A_asan_report_store2 /\
  wire_sigma WS___asan_report_store4 = BW.tfib_A_asan_report_store4 /\
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
  wire_sigma WS_is_tagged_reac = wire_text + AF_is_tagged_reac /\
  wire_sigma WS_rp_meter_counter = wire_text + AF_rp_meter_counter /\
  wire_sigma WS_rp_counter = wire_text + AF_rp_counter /\
  wire_sigma WS_rp_frame_channels = wire_text + AF_rp_frame_channels /\
  wire_sigma WS_rp_copy_untag = wire_text + AF_rp_copy_untag /\
  wire_sigma WS_rp_slot_width = wire_text + AF_rp_slot_width /\
  wire_sigma WS_rp_slot_read = wire_text + AF_rp_slot_read /\
  wire_sigma WS_reac_frame_is_reac = wire_text + AF_reac_frame_is_reac /\
  wire_sigma WS_reac_frame_clean_len = wire_text + AF_reac_frame_clean_len.
Proof. repeat split; reflexivity. Qed.
