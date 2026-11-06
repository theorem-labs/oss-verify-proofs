(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row A-SL_x of a Theorem Labs lane's FREE-PIECES): the AR-free static and image
   hypotheses of W_send_line_x.v's pb_send_line_x, decided at the A top's instance (PI := PB_fr, B := TfibB,
   RG := fr_RG, CTX_R := ACk0.CTX_AREALLOC), so that W_LLVMFuzzerTestOneInput_top_x.v only cites them when it plugs
   SL_x (top_x.v:316).  Each lemma is named slx_<the Section hypothesis>; the placements are vm_compute facts, the
   G_SL cell facts follow top_x's own HGSL / HROMO_SL proofs (top_x.v:996-1000) over _G.v's c_* lemmas. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YP09 YP0b YI00 YC5d YG00 YG0f YG0d YCbq YM05 YA0q YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_kit W_pl W_img W_journal W_rep W_contract W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_pro AD2l ACk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_addI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/A/W_LLVMFuzzerTestOneInput_top_x.v's sink head (its line `#[local] Existing Instance AE2k.tfib_sink_head.`) *)
#[local] Existing Instance AE2k.tfib_sink_head.
Section topx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- placement: the objects' and kept auipc values' addresses against fr_RG (W_send_line_cx_x.v HV9 .. HH24) ---- *)
Lemma slx_HV9 : VAL (A_OBJ 9) = rg_client fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HV10 : VAL (A_OBJ 10) = rg_client_broken fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HV11 : VAL (A_OBJ 11) = rg_send_eintr fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HV12 : VAL (A_OBJ 12) = rg_send_dead fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HV13 : VAL (A_OBJ 13) = rg_nout fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HV14 : VAL (A_OBJ 14) = rg_capout fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HV15 : VAL (A_OBJ 15) = rg_out fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HH17 : VAL (A_HI 17) + 92 = rg_client_broken fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HH19 : VAL (A_HI 19) + 248 = rg_send_eintr fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HH21 : VAL (A_HI 21) + 140 = rg_send_max fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HH22 : VAL (A_HI 22) + 260 = rg_nout fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HH23 : VAL (A_HI 23) + 864 = rg_capout fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HH24 : VAL (A_HI 24) + 892 = rg_out fr_RG. Proof. vm_compute. reflexivity. Qed.
Lemma slx_HSM : 0x10000 <= rg_send_max fr_RG /\ rg_send_max fr_RG + 8 <= 0x5fb000.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma slx_HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client fr_RG, rg_client fr_RG + 4); (rg_client_broken fr_RG, rg_client_broken fr_RG + 1);
 (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1); (rg_send_dead fr_RG, rg_send_dead fr_RG + 1);
 (rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_nout fr_RG, rg_nout fr_RG + 8);
 (rg_capout fr_RG, rg_capout fr_RG + 8); (rg_out fr_RG, rg_out fr_RG + 8);
 (as_errno TfibB, as_errno TfibB + 4)].
Proof.
vm_compute; repeat split; first [left; discriminate | right; discriminate |
  left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H].
Qed.
(* errno is tp - 164 (W_sites.v aerrno_realizes) *)
Lemma slx_HERRNO : as_errno TfibB = as_tp TfibB - 164. Proof. vm_compute. reflexivity. Qed.

(* ---- the realloc rule's caller context: send_line's realloc returns to 0x82844, CTX_AREALLOC's first row ---- *)
Lemma slx_HCTX_slr : In [BASE + AF_fr_send_line + 0x110] CTX_AREALLOC.
Proof. unfold CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). Qed.

(* ---- send_line's globals G_SL and the three entry cells: image, not owned, not read-only (top_x.v:996-1000) ---- *)
Lemma slx_HG : gx_ok segs TfibB (G_SL TfibB fr_RG).
Proof.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms) as HEV.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms) as HOWN.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms) as HKEPT.
intros a Ha. pose proof (c_HG_SL TfibB a Ha) as Hg.
exact (conj (c_img TfibB HEV a Hg) (conj (HOWN a Hg) (HKEPT a Hg))).
Qed.
Lemma slx_HGR : forall a, inG (G_SL TfibB fr_RG) a -> ~ in_rom segs a.
Proof.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms) as HEV.
intros a Hg Hr. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)).
Qed.
Lemma slx_HROMO : rom_out segs TfibB (G_SL TfibB fr_RG).
Proof.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms) as HEV.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_ROMPIN TfibB TfibB_syms) as ROMPIN.
apply (W_LLVMFuzzerTestOneInput_pro.pro_rom_out TfibB HEV ROMPIN).
intros a Hr Hg. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)).
Qed.
Lemma slx_HGO : gx_ok segs TfibB [(rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_send_max fr_RG, 8)].
Proof.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms) as HEV.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms) as HOWN.
pose proof (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms) as HKEPT.
intros a Ha.
assert (Hg : inG (G_fr_c TfibB) a).
{ unfold inG in Ha.
  apply Exists_cons in Ha as [Ha | Ha];
    [unfold YG0n.in_zr in Ha; cbn [fst snd] in Ha; exact (c_HG_client TfibB a Ha)|].
  apply Exists_cons in Ha as [Ha | Ha];
    [unfold YG0n.in_zr in Ha; cbn [fst snd] in Ha; exact (c_HG_sdead TfibB a Ha)|].
  apply Exists_cons in Ha as [Ha | Ha];
    [unfold YG0n.in_zr in Ha; cbn [fst snd] in Ha; exact (c_HG_smax TfibB a Ha)|].
  apply Exists_nil in Ha. destruct Ha. }
exact (conj (c_img TfibB HEV a Hg) (conj (HOWN a Hg) (HKEPT a Hg))).
Qed.
End topx.
