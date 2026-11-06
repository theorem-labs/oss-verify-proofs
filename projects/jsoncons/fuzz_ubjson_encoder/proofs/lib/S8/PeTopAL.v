(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIface HeapIfaceA LibIface LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PnStatics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTAL.

Section LAYOUT.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).

Definition ATEXIT_a : Z := 0x695ad0.
Definition foot_a : list (Z * Z) := pm_foot ADDR_A.
Definition init_cells_a : list (Z * Z * Z) :=
  [(6904528, 1, 0); (6904532, 4, 0); (6904536, 4, 2); (6904544, 8, 6904552); (6904552, 8, 0); (6904560, 8, 1156008); (6904816, 8, 622312);
   (6905107, 1, 0); (6905328, 4, 0); (6904568, 8, 1156008); (6904824, 8, 690352)].
Definition TopLayA_a (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa8928;
  lla_gp := 0x10800;
  lla_empty := 0x674060;
  lla_initc := [(0x6759b8, 0x675a80); (0x695ac0, 0x695ac8); (0x695d18, 0x695d20); (0x695d48, 0x695d78); (0x695d13, 0x695d14); (0x695df0, 0x695df4)];
  lla_init_img := [(0x10000, 0x13a000); (0x13d8f0, 0x13d998); (0x674055, 0x6759b0)];
  lla_td_self := 0x6759b8; lla_td_tid := 0x6759d8; lla_td_locale := 0x675a50; lla_locale := 0x695d48; lla_td_canary := 0x675a70;
  lla_guard := 0x695ac0; lla_auxvp := 0x695d18;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x13a000;
  lla_stack := STK;
  lla_frames := FRAMES;
  lla_leak := LEAK;
  lla_credit := CREDIT;
  lla_foot := foot_a;
  lla_junk := [];
  lla_init_cells := init_cells_a |}.

Definition ATEXIT_b : Z := 0x69a1d0.
Definition foot_b : list (Z * Z) := pm_foot ADDR_B.
Definition init_cells_b : list (Z * Z * Z) :=
  [(6922704, 1, 0); (6922708, 4, 0); (6922712, 4, 2); (6922720, 8, 6922728); (6922728, 8, 0); (6922736, 8, 1174352); (6922992, 8, 624400);
   (6923283, 1, 0); (6923504, 4, 0); (6922744, 8, 1174352); (6923000, 8, 692440)].
Definition TopLayA_b (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa9150;
  lla_gp := 0x10800;
  lla_empty := 0x678760;
  lla_initc := [(0x67a0b8, 0x67a180); (0x69a1c0, 0x69a1c8); (0x69a418, 0x69a420); (0x69a448, 0x69a478); (0x69a413, 0x69a414); (0x69a4f0, 0x69a4f4)];
  lla_init_img := [(0x10000, 0x13f040); (0x142000, 0x1420a8); (0x678755, 0x67a0b0)];
  lla_td_self := 0x67a0b8; lla_td_tid := 0x67a0d8; lla_td_locale := 0x67a150; lla_locale := 0x69a448; lla_td_canary := 0x67a170;
  lla_guard := 0x69a1c0; lla_auxvp := 0x69a418;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x13f000;
  lla_stack := STK;
  lla_frames := FRAMES;
  lla_leak := LEAK;
  lla_credit := CREDIT;
  lla_foot := foot_b;
  lla_junk := [];
  lla_init_cells := init_cells_b |}.
End LAYOUT.

Lemma foot_a_eq : foot_a = [(0x674080, 0x674082); (0x6742b0, 0x6742b2); (0x6742b2, 0x6749f0); (0x675118, 0x675170); (0x695ad0, 0x695cf0)].
Proof. reflexivity. Qed.
Lemma foot_b_eq : foot_b = [(0x678780, 0x678782); (0x6789b0, 0x6789b2); (0x6789b2, 0x6790f0); (0x679818, 0x679870); (0x69a1d0, 0x69a3f0)].
Proof. reflexivity. Qed.

End PNTAL.
