(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/DecodeImg.v (itself from proofs/libreac/fuzz_grant/lib/A/Prog/GrantImg.v, from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v) for reac-repacer/fuzz_uci's image A: the code table of fuzz_uci.asan's program code (the listing's own base uci_text and its uci_nslots words), one value table over lib/A/Prog/UciPAddr.v's addresses, the listing's 10 objects and program-function addresses (uci_xcalls); the image is the core's tfibsegs (lib/A/AB1v.v) and its bounds the notations of lib/Reusable/YImgTop.v, so the page arithmetic (seg_lo .. page_up) that fuzz_decode's YImgTop defines is stated here and checked against the image by vm_compute; module paths changed. *)
(* WirePPaImg: the Pa part of reac-repacer/fuzz_uci's lib/A/Prog/UciPImg.v (recipes commit 0295462466b2) for reac-repacer/fuzz_wire's image A, as this unit's lib/B/Prog/WirePImg.v carries it for image B: the code table of fuzz_wire.asan's program code (the listing's own base wire_text and its wire_nslots words, lib/A/Prog/WirePList.v), one value table over lib/A/Prog/WirePAddr.v's addresses, the listing's 14 objects and program-function addresses (wire_xcalls of lib/A/Prog/WirePPa.v), and the PAImg instance PI_wire; the image facts the instance reads (wire_segs_low, wire_img_range, wire_img_cover, wire_relro_img) are lib/A/Prog/WirePImg.v's, which this file imports and does not change; names changed (usym -> wsym, uci_ -> wire_, ucitbl -> wiretbl, PI_uci -> PI_wire); module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun WirePSyms WirePList WirePAddr WirePPa WirePImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The code table: every word of the program code the listing covers, from the entry function up. *)
Definition wiretbl : ctable :=
Eval vm_compute in (build_table tfibsegs wire_text wire_nslots TEmpty).
Lemma wiretbl_eq : wiretbl = build_table tfibsegs wire_text wire_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl wiretbl). Qed.
Lemma wiretbl_ok : table_ok tfibsegs wiretbl.
Proof. rewrite wiretbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* The listing's value table: slot A_TEXT is the listing's base, the A_OBJ block the objects, the A_HI block the
   auipc values, all of lib/A/Prog/WirePAddr.v. *)
Definition wire_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then wire_text else if (a <? A_HI 0)%nat then wire_obj (a - A_OBJ 0) else wire_hi (a - A_HI 0).
Lemma wire_lib_check : pi_check wsym (clookup wiretbl) wire_val wire_sigma wire_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma wire_val_range : forall a, 0 <= wire_val a < 2 ^ 64.
Proof.
intros a. unfold wire_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold wire_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 20 (destruct m as [|m]; [zlit|]). zlit.
- unfold wire_hi. generalize (a - A_HI 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma wire_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma wire_xcalls_ok : forall s k, In (s, k) wire_xcalls -> wire_sigma s = wire_val A_TEXT + k.
Proof.
intros s k H.
assert (Hb : forallb (fun p => Z.eqb (wire_sigma (fst p)) (wire_val A_TEXT + snd p)) wire_xcalls = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[global] Instance PI_wire : PAImg wire_listing := {|
pa_segs := tfibsegs;
pa_tbl := wiretbl;
pa_tbl_ok := wiretbl_ok;
pa_val := wire_val;
pa_sigma := wire_sigma;
pa_cert := wire_lib_check;
pa_B_ok := ltac:(unfold wire_val, wire_text; cbn; lia);
pa_val_range := wire_val_range;
pa_wx := wire_wx;
pa_segs_low := wire_segs_low;
pa_img_range := wire_img_range;
pa_img_cover := wire_img_cover;
pa_obj_img := ltac:(intros i Hi;
  do 14 (destruct i as [|i]; [unfold wire_val, wire_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa_relro_lo := 0;
pa_relro_hi := 0;
pa_relro_img := wire_relro_img;
pa_xcalls := wire_xcalls_ok |}.
End c.
