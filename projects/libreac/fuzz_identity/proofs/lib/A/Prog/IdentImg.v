(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1v.v, ACef.v, AI12.v and ACbj.v in one file for libreac/fuzz_identity's program walk: module paths changed; the segments are fuzz_identity.asan's, the code table covers the listing's 3886 words from 0x8070c, the addresses are IdentAddr.v's, the read-only range is .data.rel.ro and .got [0x9ada0, 0x9d0a8), and the instance is one PAImg for ident_listing (no PAImg2). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun IdentSyms IdentList IdentAddr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition ident_segs : list Segment := Asan.M.loaded_segments.
Definition identtbl : ctable :=
Eval vm_compute in (build_table ident_segs ident_text ident_nslots TEmpty).
Lemma identtbl_eq : identtbl = build_table ident_segs ident_text ident_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl identtbl). Qed.
Lemma identtbl_ok : table_ok ident_segs identtbl.
Proof. rewrite identtbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition ident_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then ident_text else if (a <? A_HI 0)%nat then ident_obj (a - A_OBJ 0) else ident_hi (a - A_HI 0).
Lemma ident_check : pi_check isym (clookup identtbl) ident_val ident_sigma ident_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma ident_val_range : forall a, 0 <= ident_val a < 2 ^ 64.
Proof.
intros a. unfold ident_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold ident_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 31 (destruct m as [|m]; [zlit|]). zlit.
- unfold ident_hi. generalize (a - A_HI 0)%nat as m. intros m. do 50 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma ident_wx : wx_segs_nowrap ident_segs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma ident_segs_low : forall a, in_img ident_segs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) ident_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) ident_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma ident_img_range : forall a, in_img ident_segs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) ident_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) ident_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ident_img_cover : forall ly S md, ALedger ident_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma ident_relro_img : forall a, 0x9ada0 <= a < 0x9d0a8 -> in_img ident_segs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
#[global] Instance PI_ident : PAImg ident_listing := {|
pa_segs := ident_segs;
pa_tbl := identtbl;
pa_tbl_ok := identtbl_ok;
pa_val := ident_val;
pa_sigma := ident_sigma;
pa_cert := ident_check;
pa_B_ok := ltac:(unfold ident_val, ident_text; cbn; lia);
pa_val_range := ident_val_range;
pa_wx := ident_wx;
pa_segs_low := ident_segs_low;
pa_img_range := ident_img_range;
pa_img_cover := ident_img_cover;
pa_obj_img := ltac:(intros i Hi; do 31 (destruct i as [|i]; [unfold ident_val, ident_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0x9ada0;
pa_relro_hi := 0x9d0a8;
pa_relro_img := ident_relro_img |}.
End c.
