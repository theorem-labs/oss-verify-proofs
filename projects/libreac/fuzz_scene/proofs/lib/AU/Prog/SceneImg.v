(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied by path from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v (a working branch acae397d926) for libreac/fuzz_scene's program walk, as its second half and with GrantImg.v's own names: the PAImg instance of fuzz_scene.asan-ubsan (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f) for the listing scene_listing. SceneCode.v is the first half (scene_segs, scenetbl, scene_val, scene_lib_check) and this file requires it. The image range is 0x10000..0x5f9000, the page range of the four loaded segments of OSSVerify.libreac.fuzz_scene.images.AsanUbsan (the asan build's page range is the same); the relocation-read-only range is .data.rel.ro and .got of this image, 0x9b4e0..0x9c740 (.data.rel.ro 0x9b4e0..0x9b9e0 and .got 0x9b9e0..0x9c740, which are contiguous; the section headers of the unstripped twin unstripped/fuzz_scene/fuzz_scene.asan-ubsan measure them, and its loaded relocation-read-only bytes are this image's), the range the entry contract gives the walks arodata_okS over. Every read-only-after-relocation object the listing names is in it: the GOT words at 0x9ba40 (object 1, __asan_shadow_memory_dynamic_address), 0x9ba98 (object 0, __asan_option_detect_stack_use_after_return), 0x9c6b8 (object 4), 0x9c6c0 (object 9) and 0x9c6c8 (object 10); the object count is 18. This file is the asan-ubsan twin of lib/A/Prog/SceneImg.v and carries the same names; only the image module and these addresses differ. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun SceneSyms SceneList SceneAddr SceneCode ScenePa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma scene_wx : wx_segs_nowrap scene_segs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma scene_segs_low : forall a, in_img scene_segs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) scene_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) scene_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma scene_img_range : forall a, in_img scene_segs a -> 0x10000 <= a < 0x5f9000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) scene_segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) scene_segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma scene_relro_img : forall a, 0x9b4e0 <= a < 0x9c740 -> in_img scene_segs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma scene_xcalls_ok : forall s k, In (s, k) scene_xcalls -> scene_sigma s = scene_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (scene_sigma (fst p)) (scene_val A_TEXT + snd p)) scene_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma scene_img_cover : forall ly S md, ALedger scene_segs ly S md -> fst (ly_img ly) <= 0x10000 /\ 0x5f9000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
#[global] Instance PI_scene : PAImg scene_listing := {|
pa_segs := scene_segs;
pa_tbl := scenetbl;
pa_tbl_ok := scenetbl_ok;
pa_val := scene_val;
pa_sigma := scene_sigma;
pa_cert := scene_lib_check;
pa_B_ok := ltac:(unfold scene_val, scene_text; cbn; lia);
pa_val_range := scene_val_range;
pa_wx := scene_wx;
pa_segs_low := scene_segs_low;
pa_img_range := scene_img_range;
pa_img_cover := scene_img_cover;
pa_obj_img := ltac:(intros i Hi; do 18 (destruct i as [|i]; [unfold scene_val, scene_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0x9b4e0;
pa_relro_hi := 0x9c740;
pa_relro_img := scene_relro_img;
pa_xcalls := scene_xcalls_ok |}.
End c.
