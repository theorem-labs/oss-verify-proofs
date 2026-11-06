(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v for libreac/fuzz_grant: the code table of fuzz_grant.asan's program code (0x806b0, 5195 words), one listing's value table over GrantAddr.v's addresses, the image range 0x10000..0x5fa000, the read-only-after-relocation range 0x9c168..0x9e000, 34 objects, the listing's program-function addresses checked in place of asan3_xcalls, and one PAImg instance in place of PAImg2; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v of a working branch ca2ec2ecd18 and re-keyed to fuzz_ctrl.asan: the code table starts at 0x80edc and holds 6840 words, the value table is CtrlAddr.v's, the image range is 0x10000..0x5fe000 (the pin's lowest PT_LOAD vaddr and the page-rounded end of its highest PT_LOAD), the read-only-after-relocation range is the core's in_ro_tfa range 0x9e380..0xa07c8 (.data.rel.ro + .got of the pin's PT_GNU_RELRO), and there are 32 objects. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.libreac.fuzz_ctrl.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaRun CtrlSyms CtrlList CtrlAddr CtrlPa.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition ctrl_lib_start : Z := 0x80edc.
Definition ctrl_lib_count : nat := 6840.
Definition ctrltbl : ctable :=
Eval vm_compute in (build_table tfibsegs ctrl_lib_start ctrl_lib_count TEmpty).
Lemma ctrltbl_eq : ctrltbl = build_table tfibsegs ctrl_lib_start ctrl_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl ctrltbl). Qed.
Lemma ctrltbl_ok : table_ok tfibsegs ctrltbl.
Proof. rewrite ctrltbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition ctrl_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then ctrl_text else if (a <? A_HI 0)%nat then ctrl_obj (a - A_OBJ 0) else ctrl_hi (a - A_HI 0).
Lemma ctrl_lib_check : pi_check gsym (clookup ctrltbl) ctrl_val ctrl_sigma ctrl_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma ctrl_val_range : forall a, 0 <= ctrl_val a < 2 ^ 64.
Proof.
intros a. unfold ctrl_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold ctrl_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
- unfold ctrl_hi. generalize (a - A_HI 0)%nat as m. intros m. do 70 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma ctrl_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma ctrl_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma ctrl_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x5fe000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
(* The read-only-after-relocation range is the core's (lib/A/ACeg.v:44, in_ro_tfa's second disjunct): [0x9e380,
   0xa07c8) = .data.rel.ro + .got, the file-backed part of the pin's PT_GNU_RELRO [0x9e348, 0xa07c8) without its
   56 bytes of init / fini / preinit arrays (a Theorem Labs lane, 10-29 00:10Z; a Theorem Labs lane's review). *)
Lemma ctrl_relro_img : forall a, 0x9e380 <= a < 0xa07c8 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma ctrl_xcalls_ok : forall s k, In (s, k) ctrl_xcalls -> ctrl_sigma s = ctrl_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (ctrl_sigma (fst p)) (ctrl_val A_TEXT + snd p)) ctrl_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ctrl_img_cover : forall ly S md, ALedger tfibsegs ly S md -> fst (ly_img ly) <= 0x10000 /\ 0x5fe000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
#[global] Instance PI_ctrl : PAImg ctrl_listing := {|
pa_segs := tfibsegs;
pa_tbl := ctrltbl;
pa_tbl_ok := ctrltbl_ok;
pa_val := ctrl_val;
pa_sigma := ctrl_sigma;
pa_cert := ctrl_lib_check;
pa_B_ok := ltac:(unfold ctrl_val, ctrl_text; cbn; lia);
pa_val_range := ctrl_val_range;
pa_wx := ctrl_wx;
pa_segs_low := ctrl_segs_low;
pa_img_range := ctrl_img_range;
pa_img_cover := ctrl_img_cover;
pa_obj_img := ltac:(intros i Hi; do 32 (destruct i as [|i]; [unfold ctrl_val, ctrl_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0x9e380;
pa_relro_hi := 0xa07c8;
pa_relro_img := ctrl_relro_img;
pa_xcalls := ctrl_xcalls_ok |}.
End c.
