(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy
   (proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v, file sha256 55cdd426b78b; donor not released; itself from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v
   and A/ACbj.v) for libreac/fuzz_decode image A: the code table of fuzz_decode.asan's program code (the listing's
   own base decode_text and its decode_nslots words), one value table over lib/A/Prog/DecodeAddr.v's addresses, the
   image bounds of lib/Reusable/YImgTop.v, the listing's 15 objects, and the listing's program-function addresses
   (decode_xcalls); module paths changed.  No address or range is written by hand: every bound is computed from the
   image modules or taken from DecodeAddr.v / DecodeList.v. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodeImg.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBImg.v (file sha256 bd3308c98629; donor not released): the segments are fuzz_decode.asan-ubsan's (lib/A/DecodeTFIB.v decodesegsB0); the code table covers decodeb_listing's decodeb_nslots words from decodeb_text; the value table runs over lib/B/Prog/DecodeBAddr.v's 16 objects and 31 auipc values; the image range check is YImgTop.segs_in_asan_ubsan; img_cover keeps image A's layout_ok premise, because image B's last PT_LOAD also ends off a page (at 0x5f5bb8); the read-only range stays empty, as in image A; module paths changed. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition transportbtbl : ctable :=
Eval vm_compute in (build_table tfibsegs transportb_text transportb_nslots TEmpty).
Lemma transportbtbl_eq : transportbtbl = build_table tfibsegs transportb_text transportb_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl transportbtbl). Qed.
Lemma transportbtbl_ok : table_ok tfibsegs transportbtbl.
Proof. rewrite transportbtbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* The listing's value table: slot A_TEXT is the listing's base, the A_OBJ block the objects, the A_HI block the
   auipc values, all of lib/B/Prog/DgnDecodeBAddr.v. *)
Definition transportb_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then transportb_text else if (a <? A_HI 0)%nat then transportb_obj (a - A_OBJ 0) else transportb_hi (a - A_HI 0).
Lemma transportb_lib_check : pi_check tbsym (clookup transportbtbl) transportb_val transportb_sigma transportb_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma transportb_val_range : forall a, 0 <= transportb_val a < 2 ^ 64.
Proof.
intros a. unfold transportb_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold transportb_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 97 (destruct m as [|m]; [zlit|]). zlit.
- unfold transportb_hi. generalize (a - A_HI 0)%nat as m. intros m. do 275 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma transportb_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* Every loaded segment of image B lies inside the unit's computed image bounds (YImgTop.segs_in_asan_ubsan). *)
Lemma transportb_img_range : forall a, in_img tfibsegs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
assert (Hall : segs_in tfibsegs = true) by (vm_compute; reflexivity). unfold segs_in in Hall. rewrite forallb_forall in Hall.
pose proof (Hall sg Hin) as Hb. apply andb_true_iff in Hb as [Hlo Hhi].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold seg_lo, seg_hi in Hlo, Hhi. lia.
Qed.
Lemma transportb_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a Ha. pose proof (transportb_img_range a Ha) as [H1 H2].
pose proof IMG_LO_val as E1. pose proof IMG_TOP_val as E2. unfold kLowMemEnd. lia.
Qed.
(* No read-only-after-relocation range is used by this image's walks: the range is empty. *)
Lemma transportb_relro_img : forall a, 0 <= a < 0 -> in_img tfibsegs a.
Proof. intros a Ha. exfalso. lia. Qed.
Lemma transportb_xcalls_ok : forall s k, In (s, k) transportb_xcalls -> transportb_sigma s = transportb_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (transportb_sigma (fst p)) (transportb_val A_TEXT + snd p)) transportb_xcalls = true) by (vm_compute; reflexivity).
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
Lemma transportb_img_cover : forall ly S md, layout_ok ly -> ALedger tfibsegs ly S md ->
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
split; [rewrite J0, IMG_LO_val; unfold kImgLo; lia|].
assert (HTOPA : IMG_TOP = page_up (img_hi_of tfibsegs)) by (vm_compute; reflexivity).
rewrite HTOPA. apply page_up_le; [vm_compute; discriminate | exact HA | exact HTal].
Qed.
#[global] Instance PI_transportb : PAImg transportb_listing := {|
pa_segs := tfibsegs;
pa_tbl := transportbtbl;
pa_tbl_ok := transportbtbl_ok;
pa_val := transportb_val;
pa_sigma := transportb_sigma;
pa_cert := transportb_lib_check;
pa_B_ok := ltac:(unfold transportb_val, transportb_text; cbn; lia);
pa_val_range := transportb_val_range;
pa_wx := transportb_wx;
pa_segs_low := transportb_segs_low;
pa_img_range := transportb_img_range;
pa_img_cover := transportb_img_cover;
pa_obj_img := ltac:(intros i Hi; pose proof IMG_LO_val; pose proof IMG_TOP_val;
  do 97 (destruct i as [|i]; [unfold transportb_val, transportb_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0;
pa_relro_hi := 0;
pa_relro_img := transportb_relro_img;
pa_xcalls := transportb_xcalls_ok |}.
End c.
