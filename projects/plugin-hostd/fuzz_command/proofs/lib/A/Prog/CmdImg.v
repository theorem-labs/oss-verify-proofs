(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACbj.v with the parts of lib/A/AI12.v (the image's values and the listing check) and lib/A/ACef.v (the code table) it uses, for fuzz_command.asan: one listing (cmd_listing) instead of two, its code table from 0x864e4, the values of CmdAddr.v (list-indexed, so the range lemma is one check), the image's end 0x606000 and read-only range 0xa5740..0xa7108. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun CmdSyms CmdList CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the code table of the program's words (cgif lib/A/ACef.v) *)
Definition cmdtbl_prog : ctable :=
Eval vm_compute in (build_table tfibsegs cmd_text cmd_nslots TEmpty).
Lemma cmdtbl_prog_eq : cmdtbl_prog = build_table tfibsegs cmd_text cmd_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl cmdtbl_prog). Qed.
Lemma cmdtbl_prog_ok : table_ok tfibsegs cmdtbl_prog.
Proof. rewrite cmdtbl_prog_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the values of the listing's atoms (cgif lib/A/AI12.v) *)
Definition cmd_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then cmd_text else if (a <? A_HI 0)%nat then cmd_obj (a - A_OBJ 0) else cmd_hi (a - A_HI 0).
Lemma cmd_lib_check : pi_check csym (clookup cmdtbl_prog) cmd_val cmd_sigma cmd_listing = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nth_range64 : forall (l : list Z) i, forallb (fun z => (0 <=? z) && (z <? 2 ^ 64)) l = true -> 0 <= nth i l 0 < 2 ^ 64.
Proof.
intros l i H. destruct (nth_in_or_default i l 0) as [Hin | ->]; [|lia].
rewrite forallb_forall in H. specialize (H _ Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma cmd_val_range : forall a, 0 <= cmd_val a < 2 ^ 64.
Proof.
intros a. unfold cmd_val. destruct (Nat.eqb a A_TEXT); [unfold cmd_text; lia|].
destruct (Nat.ltb a (A_HI 0)); [unfold cmd_obj | unfold cmd_hi]; apply nth_range64; vm_compute; reflexivity.
Qed.
(* the image's segments (cgif lib/A/ACbj.v) *)
Lemma cmd_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma cmd_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma cmd_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x606000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cmd_img_cover : forall ly S md, ALedger tfibsegs ly S md -> fst (ly_img ly) <= 0x10000 /\ 0x606000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma cmd_relro_img : forall a, 0xa5740 <= a < 0xa7108 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
#[global] Instance PB_cmd : PAImg cmd_listing := {|
pa_segs := tfibsegs;
pa_tbl := cmdtbl_prog;
pa_tbl_ok := cmdtbl_prog_ok;
pa_val := cmd_val;
pa_sigma := cmd_sigma;
pa_cert := cmd_lib_check;
pa_B_ok := ltac:(unfold cmd_val, cmd_text; cbn; lia);
pa_val_range := cmd_val_range;
pa_wx := cmd_wx;
pa_segs_low := cmd_segs_low;
pa_img_range := cmd_img_range;
pa_img_cover := cmd_img_cover;
pa_obj_img := ltac:(intros i Hi; do 13 (destruct i as [|i]; [vm_compute; split; discriminate|]); exfalso; lia);
pa_relro_lo := 0xa5740;
pa_relro_hi := 0xa7108;
pa_relro_img := cmd_relro_img |}.
End c.
