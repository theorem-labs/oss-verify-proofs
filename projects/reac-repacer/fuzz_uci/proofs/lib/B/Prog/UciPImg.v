(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/UciPImg.v (commit 8c3eb0365c8c; itself from proofs/libreac/fuzz_decode/lib/A/Prog/DecodeImg.v, from proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v and proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v) for reac-repacer/fuzz_uci's image B, as fuzz_decode's released lib/B/Prog/DecodeBImg.v twins its lib/A/Prog/DecodeImg.v: the code table of fuzz_uci.asan-ubsan's program code (the listing's own base uci_text and its uci_nslots words, lib/B/Prog/UciPList.v), one value table over lib/B/Prog/UciPAddr.v's addresses, the listing's 10 objects and program-function addresses (uci_xcalls); the image is the B core's tfibsegs (lib/B/YB1v.v) and its bounds the notations of lib/B/YImgTop.v, each checked against the image by vm_compute; the image-generic Pa engine stays lib/A/Prog's. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaRun.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciPSyms UciPList UciPAddr UciPPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The page arithmetic of fuzz_decode's lib/Reusable/YImgTop.v, at this unit's image B: lib/B/YImgTop.v states
   IMG_LO and IMG_TOP as numerals, and the checks below decide by vm_compute that every loaded segment of
   fuzz_uci.asan-ubsan lies inside [IMG_LO, IMG_TOP) and that IMG_TOP is the page above its highest loaded byte. *)
Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).
Definition img_hi_of (l : list Segment) : Z := fold_right (fun s acc => Z.max (seg_hi s) acc) 0 l.
Definition page_up (x : Z) : Z := (x + 4095) / 4096 * 4096.
Definition uci_segs_in (l : list Segment) : bool :=
forallb (fun s => (IMG_LO <=? seg_lo s) && (seg_hi s <=? IMG_TOP)) l.
Lemma uci_segs_in_ok : uci_segs_in tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma uci_img_top : IMG_TOP = page_up (img_hi_of tfibsegs).
Proof. vm_compute. reflexivity. Qed.

(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition ucitbl : ctable :=
Eval vm_compute in (build_table tfibsegs uci_text uci_nslots TEmpty).
Lemma ucitbl_eq : ucitbl = build_table tfibsegs uci_text uci_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl ucitbl). Qed.
Lemma ucitbl_ok : table_ok tfibsegs ucitbl.
Proof. rewrite ucitbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* The listing's value table: slot A_TEXT is the listing's base, the A_OBJ block the objects, the A_HI block the
   auipc values, all of lib/B/Prog/UciPAddr.v. *)
Definition uci_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then uci_text else if (a <? A_HI 0)%nat then uci_obj (a - A_OBJ 0) else uci_hi (a - A_HI 0).
Lemma uci_lib_check : pi_check usym (clookup ucitbl) uci_val uci_sigma uci_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma uci_val_range : forall a, 0 <= uci_val a < 2 ^ 64.
Proof.
intros a. unfold uci_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold uci_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 20 (destruct m as [|m]; [zlit|]). zlit.
- unfold uci_hi. generalize (a - A_HI 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma uci_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* Every loaded segment of image B lies inside the unit's image bounds (uci_segs_in_ok). *)
Lemma uci_img_range : forall a, in_img tfibsegs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
pose proof uci_segs_in_ok as Hall. unfold uci_segs_in in Hall. rewrite forallb_forall in Hall.
pose proof (Hall sg Hin) as Hb. apply andb_true_iff in Hb as [Hlo Hhi].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold seg_lo, seg_hi in Hlo, Hhi. lia.
Qed.
Lemma uci_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a Ha. pose proof (uci_img_range a Ha) as [H1 H2]. unfold kLowMemEnd. lia.
Qed.
(* No read-only-after-relocation range is used by this image's walks: the range is empty. *)
Lemma uci_relro_img : forall a, 0 <= a < 0 -> in_img tfibsegs a.
Proof. intros a Ha. exfalso. lia. Qed.
Lemma uci_xcalls_ok : forall s k, In (s, k) uci_xcalls -> uci_sigma s = uci_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (uci_sigma (fst p)) (uci_val A_TEXT + snd p)) uci_xcalls = true) by (vm_compute; reflexivity).
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
Lemma uci_img_cover : forall ly S md, layout_ok ly -> ALedger tfibsegs ly S md ->
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
rewrite uci_img_top. apply page_up_le; [vm_compute; discriminate | exact HA | exact HTal].
Qed.
#[global] Instance PI_uci : PAImg uci_listing := {|
pa_segs := tfibsegs;
pa_tbl := ucitbl;
pa_tbl_ok := ucitbl_ok;
pa_val := uci_val;
pa_sigma := uci_sigma;
pa_cert := uci_lib_check;
pa_B_ok := ltac:(unfold uci_val, uci_text; cbn; lia);
pa_val_range := uci_val_range;
pa_wx := uci_wx;
pa_segs_low := uci_segs_low;
pa_img_range := uci_img_range;
pa_img_cover := uci_img_cover;
pa_obj_img := ltac:(intros i Hi;
  do 10 (destruct i as [|i]; [unfold uci_val, uci_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0;
pa_relro_hi := 0;
pa_relro_img := uci_relro_img;
pa_xcalls := uci_xcalls_ok |}.
End c.
