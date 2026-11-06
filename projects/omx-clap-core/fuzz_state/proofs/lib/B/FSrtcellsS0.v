(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths, module names, addresses and numbers changed; 144 of its 230 lines of code are new or changed and 657 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSmemchr.v; 55 of its 79 lines of code are new or changed and 206 lines of the source are left out. *)
(* fs.asan-ubsan's (image B) start-up runtime cells as S0-native facts (no Bz tree in the Require closure); the B twin of
   S0's lib/A/FSrtcellsS0.v. rule 24: no function proved (kind: start-up facts - lemmas reading the certified start-up
   table; no walk).
   - fs_shadow_syms_of: lib/B/FSH_Base.v FsShadowSyms B (:112-114) from image B's relocated core lib/B/YCeg.v TfibLib B
     (tl_got_shadow, tl_shadow_cell): YCeg's A_GOT_shadow 0x9fc10 / A_shadow_glob 0xa8438 are FSH_Base's FS_GOT_shadow /
     FS_shadow_cell.
   - fs_rt_vals: at every ASan state (AR) the restricted memory holds, as val_mem facts, the cells of lib/B/FSstrlen.v
     fs_rt_rest, read from AR's ARm and TfibSyms' ts_const through lib/B/YF0x.v tfib_const_lookup on lib/B/YF0m.v's rows:
     z8 0x9fc00 0x139f68, z8 0x9fc18 0xa9128, z8 0x9fc20 0xa9130, z8 0x9fc28 0xa9120, z8 0xa1928 0x9958c,
     z8 0xa1950 0x98e40, z1 0xa9118 0x1, z8 0xa9120 0x7fffffffffff, z8 0xa9128 0x0, z8 0xa9130 0x0; the flag byte
     0x13a063 (= 1) is the little-endian byte 3 of the word z8 0x13a060 0x101010101010101 (val_mem_byte_at), as A's
     0x139b63 is of 0x139b60.
   Changes from A's file (a Theorem Labs lane, 2026-10-29): B's names (YB1v, YF0m, YF0x, YCeg, lib/B/FSH_Base) and B's rows; the
   two strcmp flag bytes (A's 0x139b5d, 0x139b62) are not read here.
   lib/B/FSrtcells.v turns fs_rt_vals into the Bz tree's ro_cells (FSstrlen.FsRtCells). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YF0x.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m FSH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Module AFx := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YF0x.
Module ACg := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YCeg.

(* ---- FsShadowSyms from TfibLib ---- *)
Lemma ACeg_shadow_vals : ACg.A_GOT_shadow = FS_GOT_shadow /\ ACg.A_shadow_glob = FS_shadow_cell.
Proof. split; vm_compute; reflexivity. Qed.

Lemma fs_shadow_syms_of : forall B, ACg.TfibLib B -> FsShadowSyms B.
Proof.
  intros B TL. destruct ACeg_shadow_vals as (V1 & V2). split.
  - rewrite (ACg.tl_got_shadow B TL). exact V1.
  - rewrite (ACg.tl_shadow_cell B TL). exact V2.
Qed.

(* ---- one byte of a val_mem value (little-endian) is a 1-byte val_mem value ---- *)
Lemma le_byte_range : forall z (w k : nat), 0 <= YO0f.le_byte z w k < 256.
Proof. intros z w k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma le_byte_1_0 : forall z, 0 <= z < 256 -> YO0f.le_byte z 1 0 = z.
Proof.
  intros z Hz. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small z 256 Hz). exact (Z.mod_small z 256 Hz).
Qed.

Lemma val_mem_byte : forall m A n v k, (k < n)%nat -> val_mem tfibsegs m A n v ->
  val_mem tfibsegs m (A + Z.of_nat k) 1 (YO0f.le_byte v n k).
Proof.
  intros m A n v k Hk HV j Hj. destruct j as [|j]; [|exfalso; lia].
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite (HV k Hk).
  exact (f_equal (fun z => Some (Z_to_bv 8 z)) (eq_sym (le_byte_1_0 _ (le_byte_range v n k)))).
Qed.

Lemma val_mem_byte_at : forall m A n v k a b, (k < n)%nat -> a = A + Z.of_nat k -> YO0f.le_byte v n k = b ->
  val_mem tfibsegs m A n v -> val_mem tfibsegs m a 1 b.
Proof. intros m A n v k a b Hk -> <- HV. exact (val_mem_byte m A n v k Hk HV). Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the start-up cells fs's interceptor walks read, at every ASan state ---- *)
Lemma fs_rt_vals : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9fc00 8 0x139f68 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9fc18 8 0xa9128 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9fc20 8 0xa9130 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9fc28 8 0xa9120 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1928 8 0x9958c /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1950 8 0x98e40 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa9118 1 1 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa9120 8 0x7fffffffffff /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa9128 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa9130 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x13a063 1 1.
Proof.
  intros B _ TB ly S W mem md HAR.
  pose proof (proj1 HAR) as M.
  assert (V : forall a (w : nat) v,
    AFx.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
    val_mem tfibsegs (mrestrict (w_H W) mem) a w v)
    by (intros a w v E; exact (AFx.tfib_const_lookup B TB ly S (w_H W) mem a w v M E)).
  pose proof (V 0x13a060 8%nat 0x101010101010101 ltac:(vm_compute; reflexivity)) as W60.
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  apply (val_mem_byte_at _ 0x13a060 8 0x101010101010101 3);
    [lia | reflexivity | vm_compute; reflexivity | exact W60].
Qed.

End core.
