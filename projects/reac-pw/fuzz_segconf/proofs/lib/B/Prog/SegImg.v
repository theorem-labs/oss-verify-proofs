(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACbj.v with the parts of lib/A/AI12.v (the image's values and the listing check) and lib/A/ACef.v (the code table) it uses, for fuzz_command.asan: one listing (cmd_listing) instead of two, its code table from 0x864e4, the values of CmdAddr.v (list-indexed, so the range lemma is one check), the image's end 0x606000 and read-only range 0xa5740..0xa7108. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdImg.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; csym -> ssym, the listing modules and names Cmd*/cmd_* -> Seg*/seg_*, PB_cmd -> PB_seg; the image fuzz_segconf.asan (images/Asan.v, its four page-rounded segments 0x10000+0x21000, 0x31000+0x70000, 0xa1000+0x3000, 0xa4000+0x55d000); the image's end 0x606000 -> YG0f.kImgEnd (0x601000), unfolded where a step needs the number; the read-only range 0xa5740..0xa7108 -> 0xa14a0..0xa3748. *)
(* Modified by Theorem Labs, 2026-10: the image-B twin of lib/A/Prog/SegImg.v (commit 4f361f065164): module paths and image B's values. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YG00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun SegSyms SegList SegAddr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the code table of the program's words (cgif lib/A/ACef.v) *)
Definition segtbl_prog : ctable :=
Eval vm_compute in (build_table tfibsegs seg_text seg_nslots TEmpty).
Lemma segtbl_prog_eq : segtbl_prog = build_table tfibsegs seg_text seg_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl segtbl_prog). Qed.
Lemma segtbl_prog_ok : table_ok tfibsegs segtbl_prog.
Proof. rewrite segtbl_prog_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the values of the listing's atoms (cgif lib/A/AI12.v) *)
Definition seg_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then seg_text else if (a <? A_HI 0)%nat then seg_obj (a - A_OBJ 0) else seg_hi (a - A_HI 0).
Lemma seg_lib_check : pi_check ssym (clookup segtbl_prog) seg_val seg_sigma seg_listing = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nth_range64 : forall (l : list Z) i, forallb (fun z => (0 <=? z) && (z <? 2 ^ 64)) l = true -> 0 <= nth i l 0 < 2 ^ 64.
Proof.
intros l i H. destruct (nth_in_or_default i l 0) as [Hin | ->]; [|lia].
rewrite forallb_forall in H. specialize (H _ Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma seg_val_range : forall a, 0 <= seg_val a < 2 ^ 64.
Proof.
intros a. unfold seg_val. destruct (Nat.eqb a A_TEXT); [unfold seg_text; lia|].
destruct (Nat.ltb a (A_HI 0)); [unfold seg_obj | unfold seg_hi]; apply nth_range64; vm_compute; reflexivity.
Qed.
(* the image's segments (cgif lib/A/ACbj.v) *)
Lemma seg_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma seg_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma seg_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < kImgEnd.
Proof.
unfold kImgEnd.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma seg_img_cover : forall ly S md, ALedger tfibsegs ly S md -> fst (ly_img ly) <= 0x10000 /\ kImgEnd <= fst (ly_img ly) + snd (ly_img ly).
Proof.
unfold kImgEnd.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma seg_relro_img : forall a, 0xa1c60 <= a < 0xa3f08 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
#[global] Instance PB_seg : PAImg seg_listing := {|
pa_segs := tfibsegs;
pa_tbl := segtbl_prog;
pa_tbl_ok := segtbl_prog_ok;
pa_val := seg_val;
pa_sigma := seg_sigma;
pa_cert := seg_lib_check;
pa_B_ok := ltac:(unfold seg_val, seg_text; cbn; lia);
pa_val_range := seg_val_range;
pa_wx := seg_wx;
pa_segs_low := seg_segs_low;
pa_img_range := seg_img_range;
pa_img_cover := seg_img_cover;
pa_obj_img := ltac:(intros i Hi; do 13 (destruct i as [|i]; [vm_compute; split; discriminate|]); exfalso; lia);
pa_relro_lo := 0xa1c60;
pa_relro_hi := 0xa3f08;
pa_relro_img := seg_relro_img |}.
End c.
