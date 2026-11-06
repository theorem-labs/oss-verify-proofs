(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA LibIface LibIfaceAB PmLayout PnLayout PnLayoutA PnStatics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTAL.

Section LAYOUT.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).

(* [comment removed for export] *)
Definition ATEXIT_a : Z := 0x6918d0.      (* [comment removed for export] *)
Definition foot_a : list (Z * Z) := PNST.pn_foot ADDR_A NADDR_A.
Definition init_cells_a : list (Z * Z * Z) :=
  [(6887632, 1, 0); (6887636, 4, 0); (6887640, 4, 2); (6887648, 8, 6887656); (6887656, 8, 0); (6887664, 8, 1139320); (6887920, 8, 618908);
   (6888211, 1, 0); (6888432, 4, 0); (6887672, 8, 1139320); (6887928, 8, 686948)].      (* [comment removed for export] *)
Definition TopLayA_a (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa7bdc;                                          (* [comment removed for export] *)
  lla_gp := 0x10800;
  lla_empty := 0x66fe20;                                         (* [comment removed for export] *)
  lla_initc := [(0x6717b8, 0x671880); (0x6918c0, 0x6918c8); (0x691b18, 0x691b20); (0x691b48, 0x691b78); (0x691b13, 0x691b14); (0x691bf0, 0x691bf4)];
  lla_init_img := [(0x10000, 0x136000); (0x139710, 0x1397b8); (0x66fe15, 0x6717b0)];
  lla_td_self := 0x6717b8; lla_td_tid := 0x6717d8; lla_td_locale := 0x671850; lla_locale := 0x691b48; lla_td_canary := 0x671870;
  lla_guard := 0x6918c0; lla_auxvp := 0x691b18;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x136000;
  lla_stack := STK;
  lla_frames := FRAMES;
  lla_leak := LEAK;
  lla_credit := CREDIT;
  lla_foot := foot_a;
  lla_junk := [];
  lla_init_cells := init_cells_a |}.

(* [comment removed for export] *)
Definition ATEXIT_b : Z := 0x673d90.
Definition foot_b : list (Z * Z) := PNST.pn_foot ADDR_B NADDR_B.
Definition init_cells_b : list (Z * Z * Z) :=
  [(6765968, 1, 0); (6765972, 4, 0); (6765976, 4, 2); (6765984, 8, 6765992); (6765992, 8, 0); (6766000, 8, 1148904); (6766256, 8, 619804);
   (6766547, 1, 0); (6766768, 4, 0); (6766008, 8, 1148904); (6766264, 8, 687844)].      (* [comment removed for export] *)
Definition TopLayA_b (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa7f5c;
  lla_gp := 0x10800;
  lla_empty := 0x672260;
  lla_initc := [(0x673c30, 0x673cf8); (0x673d80, 0x673d88); (0x673fd8, 0x673fe0); (0x674008, 0x674038); (0x673fd3, 0x673fd4); (0x6740b0, 0x6740b4)];
  lla_init_img := [(0x10000, 0x139000); (0x13bbb8, 0x13bc60); (0x672255, 0x673bf0)];
  lla_td_self := 0x673c30; lla_td_tid := 0x673c50; lla_td_locale := 0x673cc8; lla_locale := 0x674008; lla_td_canary := 0x673ce8;
  lla_guard := 0x673d80; lla_auxvp := 0x673fd8;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x139000;
  lla_stack := STK;
  lla_frames := FRAMES;
  lla_leak := LEAK;
  lla_credit := CREDIT;
  lla_foot := foot_b;
  lla_junk := [];
  lla_init_cells := init_cells_b |}.
End LAYOUT.

(* [comment removed for export] *)
Lemma foot_a_eq : foot_a = [(0x66fe40, 0x66fe42); (0x6700b0, 0x6700b2); (0x6700b2, 0x6707f0); (0x670f18, 0x670f70); (0x6918d0, 0x691af0);
                            (0x66fe60, 0x66fe68); (0x66fe48, 0x66fe60); (0x66fe80, 0x66fe88); (0x66fe68, 0x66fe80)].
Proof. reflexivity. Qed.
Lemma foot_b_eq : foot_b = [(0x672280, 0x672282); (0x6724f0, 0x6724f2); (0x6724f2, 0x672c30); (0x673358, 0x6733b0); (0x673d90, 0x673fb0);
                            (0x6722a0, 0x6722a8); (0x672288, 0x6722a0); (0x6722c0, 0x6722c8); (0x6722a8, 0x6722c0)].
Proof. reflexivity. Qed.

End PNTAL.
