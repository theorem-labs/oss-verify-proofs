(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v, ACef.v, AI12.v and ACbj.v in one file for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/IdentImg.v, ea5560a967b, carries them): module paths changed; the segments are fuzz_boxreg.asan's (images.Asan, four loaded segments), the code table covers the listing's 2042 words from 0x7ff4c, the addresses are BoxAddr.v's (14 objects, 32 auipc values), and the instance is one PAImg for box_listing (no PAImg2). The read-only range is fuzz_boxreg.asan's .data.rel.ro and .got, [0x98958, 0x99bb0), cgif's convention (lib/A/AB1w.v tfib_data_rel_ro_lo .. tfib_got_hi; ACed.v tfibX_relro0) and the in_ro_tfa range of lib/A/ACeg.v; its third loaded segment [0x98000, 0x9a000) holds it; lib/B/Prog/BoxBImg.v states the B image's the same way. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.libreac.fuzz_boxreg.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun BoxSyms BoxList BoxAddr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition box_segs : list Segment := Asan.M.loaded_segments.
Definition boxtbl : ctable :=
Eval vm_compute in (build_table box_segs box_text box_nslots TEmpty).
Lemma boxtbl_eq : boxtbl = build_table box_segs box_text box_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl boxtbl). Qed.
Lemma boxtbl_ok : table_ok box_segs boxtbl.
Proof. rewrite boxtbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition box_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then box_text else if (a <? A_HI 0)%nat then box_obj (a - A_OBJ 0) else box_hi (a - A_HI 0).
Lemma box_check : pi_check bsym (clookup boxtbl) box_val box_sigma box_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma box_val_range : forall a, 0 <= box_val a < 2 ^ 64.
Proof.
intros a. unfold box_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold box_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 14 (destruct m as [|m]; [zlit|]). zlit.
- unfold box_hi. generalize (a - A_HI 0)%nat as m. intros m. do 32 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma box_wx : wx_segs_nowrap box_segs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma box_segs_low : forall a, in_img box_segs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) box_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) box_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma box_img_range : forall a, in_img box_segs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) box_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) box_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_img_cover : forall ly S md, ALedger box_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma box_relro_img : forall a, 0x98958 <= a < 0x99bb0 -> in_img box_segs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma box_xcalls_ok : forall s k, In (s, k) box_xcalls -> box_sigma s = box_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (box_sigma (fst p)) (box_val A_TEXT + snd p)) box_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.
#[global] Instance PI_box : PAImg box_listing := {|
pa_segs := box_segs;
pa_tbl := boxtbl;
pa_tbl_ok := boxtbl_ok;
pa_val := box_val;
pa_sigma := box_sigma;
pa_cert := box_check;
pa_B_ok := ltac:(unfold box_val, box_text; cbn; lia);
pa_val_range := box_val_range;
pa_wx := box_wx;
pa_segs_low := box_segs_low;
pa_img_range := box_img_range;
pa_img_cover := box_img_cover;
pa_obj_img := ltac:(intros i Hi; do 14 (destruct i as [|i]; [unfold box_val, box_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0x98958;
pa_relro_hi := 0x99bb0;
pa_relro_img := box_relro_img;
pa_xcalls := box_xcalls_ok |}.
End c.
