(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v, ACef.v, AI12.v and ACbj.v in one file for libreac/fuzz_boxreg's ASan+UBSan program walk (as fuzz_identity's lib/B/Prog/IdentBImg.v, ea5560a967b, carries them), as lib/A/Prog/BoxImg.v for the ASan build: module paths changed; the segments are fuzz_boxreg.asan-ubsan's (images.AsanUbsan, four PT_LOADs); the code table covers boxb_listing's 2283 words from boxb_text = 0x7ffac; the addresses are BoxBAddr.v's, so the value table runs over its 14 objects and 34 auipc highs; the read-only range is fuzz_boxreg.asan-ubsan's .data.rel.ro and .got, [0x98d78, 0x99fd0), cgif's convention (lib/A/AB1w.v tfib_data_rel_ro_lo .. tfib_got_hi; YCeg.v in_ro_tfa), inside segment 2 of the snapshot; the image range comes from Reusable/YImgTop.v (IMG_LO, IMG_TOP); and the instance is one PAImg, PI_boxb, for boxb_listing (no PAImg2). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.libreac.fuzz_boxreg.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBAddr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition boxb_segs : list Segment := AsanUbsan.M.loaded_segments.
Definition boxbtbl : ctable :=
Eval vm_compute in (build_table boxb_segs boxb_text boxb_nslots TEmpty).
Lemma boxbtbl_eq : boxbtbl = build_table boxb_segs boxb_text boxb_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl boxbtbl). Qed.
Lemma boxbtbl_ok : table_ok boxb_segs boxbtbl.
Proof. rewrite boxbtbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition boxb_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then boxb_text else if (a <? A_HI 0)%nat then boxb_obj (a - A_OBJ 0) else boxb_hi (a - A_HI 0).
Lemma boxb_check : pi_check bbsym (clookup boxbtbl) boxb_val boxb_sigma boxb_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma boxb_val_range : forall a, 0 <= boxb_val a < 2 ^ 64.
Proof.
intros a. unfold boxb_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold boxb_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 14 (destruct m as [|m]; [zlit|]). zlit.
- unfold boxb_hi. generalize (a - A_HI 0)%nat as m. intros m. do 34 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma boxb_wx : wx_segs_nowrap boxb_segs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma boxb_segs_low : forall a, in_img boxb_segs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) boxb_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) boxb_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma boxb_img_range : forall a, in_img boxb_segs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) boxb_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) boxb_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma boxb_img_cover : forall ly S md, ALedger boxb_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma boxb_relro_img : forall a, 0x98d78 <= a < 0x99fd0 -> in_img boxb_segs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma boxb_xcalls_ok : forall s k, In (s, k) boxb_xcalls -> boxb_sigma s = boxb_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (boxb_sigma (fst p)) (boxb_val A_TEXT + snd p)) boxb_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.
#[global] Instance PI_boxb : PAImg boxb_listing := {|
pa_segs := boxb_segs;
pa_tbl := boxbtbl;
pa_tbl_ok := boxbtbl_ok;
pa_val := boxb_val;
pa_sigma := boxb_sigma;
pa_cert := boxb_check;
pa_B_ok := ltac:(unfold boxb_val, boxb_text; cbn; lia);
pa_val_range := boxb_val_range;
pa_wx := boxb_wx;
pa_segs_low := boxb_segs_low;
pa_img_range := boxb_img_range;
pa_img_cover := boxb_img_cover;
pa_obj_img := ltac:(intros i Hi; do 14 (destruct i as [|i]; [unfold boxb_val, boxb_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0x98d78;
pa_relro_hi := 0x99fd0;
pa_relro_img := boxb_relro_img;
pa_xcalls := boxb_xcalls_ok |}.
End c.
