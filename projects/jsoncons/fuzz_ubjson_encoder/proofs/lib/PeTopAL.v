(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface HeapIfaceA LibIface LibIfaceAB PmLayout PnLayout PeLayoutA PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeTopAL () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTAL.

Section LAYOUT.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).

(* [comment removed for export] *)
Definition ATEXIT_a : Z := 0x695ad0.      (* [comment removed for export] *)
Definition foot_a : list (Z * Z) := pm_foot ADDR_A.      (* [comment removed for export] *)
Definition init_cells_a : list (Z * Z * Z) :=
  [(6904528, 1, 0); (6904532, 4, 0); (6904536, 4, 2); (6904544, 8, 6904552); (6904552, 8, 0); (6904560, 8, 1156008); (6904816, 8, 622312);
   (6905107, 1, 0); (6905328, 4, 0); (6904568, 8, 1156008); (6904824, 8, 690352)].      (* [comment removed for export] *)
Definition TopLayA_a (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa8928;                                          (* [comment removed for export] *)
  lla_gp := 0x10800;
  lla_empty := 0x674060;                                         (* [comment removed for export] *)
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
  lla_junk := [];                                                 (* [comment removed for export] *)
  lla_init_cells := init_cells_a |}.

(* [comment removed for export] *)
Definition ATEXIT_b : Z := 0x69a1d0.
Definition foot_b : list (Z * Z) := pm_foot ADDR_B.      (* [comment removed for export] *)
Definition init_cells_b : list (Z * Z * Z) :=
  [(6922704, 1, 0); (6922708, 4, 0); (6922712, 4, 2); (6922720, 8, 6922728); (6922728, 8, 0); (6922736, 8, 1174352); (6922992, 8, 624400);
   (6923283, 1, 0); (6923504, 4, 0); (6922744, 8, 1174352); (6923000, 8, 692440)].      (* [comment removed for export] *)
Definition TopLayA_b (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa9150;
  lla_gp := 0x10800;
  lla_empty := 0x678760;
  lla_initc := [(0x67a0b8, 0x67a180); (0x69a1c0, 0x69a1c8); (0x69a418, 0x69a420); (0x69a448, 0x69a478); (0x69a413, 0x69a414); (0x69a4f0, 0x69a4f4)];
  lla_init_img := [(0x10000, 0x13f000); (0x142000, 0x1420a8); (0x678755, 0x67a0b0)];
  lla_td_self := 0x67a0b8; lla_td_tid := 0x67a0d8; lla_td_locale := 0x67a150; lla_locale := 0x69a448; lla_td_canary := 0x67a170;
  lla_guard := 0x69a1c0; lla_auxvp := 0x69a418;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x13f000;
  lla_stack := STK;
  lla_frames := FRAMES;
  lla_leak := LEAK;
  lla_credit := CREDIT;
  lla_foot := foot_b;
  lla_junk := [];                                                 (* [comment removed for export] *)
  lla_init_cells := init_cells_b |}.
End LAYOUT.

(* [comment removed for export] *)
Lemma foot_a_eq : foot_a = [(0x674080, 0x674082); (0x6742b0, 0x6742b2); (0x6742b2, 0x6749f0); (0x675118, 0x675170); (0x695ad0, 0x695cf0)].
Proof.
ltac2:(KReplay.run1 (kr_t_PeTopAL ()) [] "p;2p;1p;3p;4g0000j2>Tg000Pj1=Tg0010j12Tg001Uj14Tg002:j19Tg002Zj37Tg003:j2:Tg003Tj1<Tg0042j4;Tf0R0#4#2p=0%40#4p=5%20#2p=1%20#<p=3g004RR1P1f1P0C;p=6%20#4p=81>11R1#=g0050#0R0#2#5#0#0R2#2R3#1R4#1#0#1#1R5#2#3%45#3'6%04#0#5#1R4#2#3%44#3R4'6%43#1#5#5#0#1#3,64%02#1#0R2#1#5#1#3%52#0#1#3'6%40#1#0#0#5R0#8#8#0#0#1#3%00#8#5#0#1#3'6%91571571571571571':o"). Qed.
Lemma foot_b_eq : foot_b = [(0x678780, 0x678782); (0x6789b0, 0x6789b2); (0x6789b2, 0x6790f0); (0x679818, 0x679870); (0x69a1d0, 0x69a3f0)].
Proof.
ltac2:(KReplay.run1 (kr_t_PeTopAL ()) [] "p;2p;1p;3p;4g0000j2>Tg000Pj1=Tg0010j12Tg001Uj15Tg002:j19Tg002Zj37Tg003:j2:Tg003Tj1<Tg0042j4;Tf0R0#5#2p=1%50#5p=3%20#2p=0%20#5p=8%20#<p=4g004RR1P1f1P0C;p=61>11R1#=g0050#1R0#2#3#3#0R2#2R3#8#3#1#0#0R4#2#4%54#4'6%13#8#1#3#0R3#2#4%53#4R3'6%52R2#2#0#8#3#1#0#4,63%52#0#0R2#0#3#0#4%32#1#0#4'6%10#8#1#1#0R0#2#3#1#1#0#4%50#3#3#1#0#4'6%91571571571571571':o"). Qed.

End PNTAL.
