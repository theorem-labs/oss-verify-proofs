(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACbj.v, with its module paths, module names, addresses and numbers changed; 80 of its 120 lines of code are new or changed and 49 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YCef.
From OSSVerify.libreac.fuzz_disco.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YI0w YI0z YI12 YC4a YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma tfib_val0_range : forall a, 0 <= tfib_val0 a < 2 ^ 64.
Proof.
intros a. unfold tfib_val0. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold tfib_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 68 (destruct m as [|m]; [zlit|]). zlit.
- unfold tfib_hi. generalize (a - A_HI 0)%nat as m. intros m. do 108 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma tfib_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma tfib_seg_in : forall a, in_img tfibsegs a -> exists b z, In (b, z) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) /\ b <= a < b + z.
Proof.
intros a (sg & Hin & Hr). exists (Z.of_N (seg_base sg)), (Z.of_N (seg_size sg)). split; [|exact Hr].
exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin).
Qed.
Lemma tfib_segs_low0 : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a Ha. destruct (tfib_seg_in a Ha) as (b & z & H & Hr). unfold kLowMemEnd.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma tfib_img_range0 : forall a, in_img tfibsegs a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.
Proof.
intros a Ha. destruct (tfib_seg_in a Ha) as (b & z & H & Hr). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfib_img_cover0 : forall ly S md, ALedger tfibsegs ly S md -> fst (ly_img ly) <= YImgTop.IMG_LO /\ YImgTop.IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. split.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma tfib_relro_img : forall a, 0xa0280 <= a < 0xa15a8 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
#[global] Instance PB_tfib : PAImg lib_both3_0_listing := {|
pa_segs := tfibsegs;
pa_tbl := tfibtbl_lib;
pa_tbl_ok := tfibtbl_lib_ok;
pa_val := tfib_val0;
pa_sigma := tfib_sigma;
pa_cert := tfib_lib_check0;
pa_B_ok := ltac:(unfold tfib_val0, tfib_B0; cbn; lia);
pa_val_range := tfib_val0_range;
pa_wx := tfib_wx;
pa_segs_low := tfib_segs_low0;
pa_img_range := tfib_img_range0;
pa_img_cover := tfib_img_cover0;
pa_obj_img := ltac:(intros i Hi; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; do 13 (destruct i as [|i]; [unfold tfib_val0, tfib_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0xa0280;
pa_relro_hi := 0xa15a8;
pa_relro_img := tfib_relro_img |}.
Lemma both3_xcalls_ok : forall s k, In (s, k) both3_xcalls -> tfib_sigma s = tfib_val0 A_TEXT + k.
Proof.
intros s k H. cbn [both3_xcalls In] in H.
repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; reflexivity|]). destruct H.
Qed.
#[global] Instance PX_tfib : PAXcalls lib_both3_0_listing := both3_xcalls_ok.
Lemma tfib_obj_img_all : forall i, (i < tfib_nobj)%nat -> YImgTop.IMG_LO <= tfib_val0 (A_OBJ i) /\ tfib_val0 (A_OBJ i) + 8 <= YImgTop.IMG_TOP.
Proof.
intros i Hi. unfold tfib_nobj in Hi. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.
do 68 (destruct i as [|i]; [unfold tfib_val0, tfib_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.
Qed.
#[global] Instance PO_tfib : PAObjImg lib_both3_0_listing := tfib_obj_img_all.
Lemma tfib_hi_img_all : forall j, (j < tfib_nhi)%nat -> 0 <= tfib_val0 (A_HI j) /\ tfib_val0 (A_HI j) < YImgTop.IMG_TOP.
Proof.
intros j Hj. unfold tfib_nhi in Hj. unfold YImgTop.IMG_TOP.
do 108 (destruct j as [|j]; [unfold tfib_val0, tfib_hi, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.
Qed.
#[global] Instance PH_tfib : PAHiImg lib_both3_0_listing := tfib_hi_img_all.
Lemma tfib_val0_obj : forall i, (i < tfib_nobj)%nat -> tfib_val0 (A_OBJ i) = tfib_obj i.
Proof.
intros i Hi. unfold tfib_nobj in Hi. unfold tfib_val0, A_OBJ, A_TEXT, A_HI.
destruct (Nat.eqb_spec (241 + i) 240); [lia|]. destruct (Nat.ltb_spec (241 + i) (320 + 0)); [|lia].
f_equal. lia.
Qed.
#[global] Instance POV_tfib : PAObjVal lib_both3_0_listing := tfib_val0_obj.
Definition tfib_ro_present_b (q sz : Z) : bool :=
forallb (fun i => match seg_rom tfibsegs (Z_to_bv 64 (q + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 (Z.to_nat sz)).
Lemma tfib_glob_tails_present_b : forallb (fun r => tfib_ro_present_b (fst r) (snd r)) tfib_glob_tails = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_glob_tails_present : forall q sz x, In (q, sz) tfib_glob_tails -> q <= x < q + sz -> seg_rom tfibsegs (Z_to_bv 64 x) <> None.
Proof.
intros q sz x Hin Hx. pose proof (proj1 (forallb_forall _ _) tfib_glob_tails_present_b (q, sz) Hin) as H. cbn [fst snd] in H.
unfold tfib_ro_present_b in H. pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (x - q))) as H1.
assert (Hs : In (Z.to_nat (x - q)) (seq 0 (Z.to_nat sz))) by (apply in_seq; lia).
specialize (H1 Hs). cbv beta in H1. replace (q + Z.of_nat (Z.to_nat (x - q))) with x in H1 by lia.
intro HN. rewrite HN in H1. discriminate H1.
Qed.
#[global] Instance PRP_tfib : PARoPresent lib_both3_0_listing := tfib_glob_tails_present.
Lemma tfib_val0_hi : forall j, tfib_val0 (A_HI j) = tfib_hi j.
Proof.
intros j. unfold tfib_val0, A_OBJ, A_TEXT, A_HI.
destruct (Nat.eqb_spec (320 + j) 240); [lia|]. destruct (Nat.ltb_spec (320 + j) (320 + 0)); [lia|].
f_equal. lia.
Qed.
Lemma tfib_obj_win_all : forall i off k, (i < tfib_nobj)%nat -> 0 <= k < tfib_win (tfib_obj i + off) -> in_img tfibsegs (tfib_val0 (A_OBJ i) + off + k).
Proof. intros i off k Hi Hk. rewrite (tfib_val0_obj i Hi). exact (tfib_win_img _ _ Hk). Qed.
Lemma tfib_hi_win_all : forall j off k, (j < tfib_nhi)%nat -> 0 <= k < tfib_win (tfib_hi j + off) -> in_img tfibsegs (tfib_val0 (A_HI j) + off + k).
Proof. intros j off k Hj Hk. rewrite (tfib_val0_hi j). exact (tfib_win_img _ _ Hk). Qed.
#[global] Instance PW_tfib : PAWinImg lib_both3_0_listing := {| pa_obj_win := tfib_obj_win_all; pa_hi_win := tfib_hi_win_all |}.
End c.
