(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA LibIface LibIfaceAB PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTAL.

Section LAYOUT.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).

(* [comment removed for export] *)
Definition ATEXIT_a : Z := 0x693d50.      (* [comment removed for export] *)
Definition foot_a : list (Z * Z) := PNST.pn_foot ADDR_A NADDR_A.
Definition init_cells_a : list (Z * Z * Z) :=
  [(6896976, 1, 0); (6896980, 4, 0); (6896984, 4, 2); (6896992, 8, 6897000); (6897000, 8, 0); (6897008, 8, 1148964); (6897264, 8, 619876);
   (6897555, 1, 0); (6897776, 4, 0); (6897016, 8, 1148964); (6897272, 8, 687916)].      (* [comment removed for export] *)
Definition TopLayA_a (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0xa7fa4;                                          (* [comment removed for export] *)
  lla_gp := 0x10800;
  lla_empty := 0x6722a0;                                         (* [comment removed for export] *)
  lla_initc := [(0x673c38, 0x673d00); (0x693d40, 0x693d48); (0x693f98, 0x693fa0); (0x693fc8, 0x693ff8); (0x693f93, 0x693f94); (0x694070, 0x694074)];
  lla_init_img := [(0x10000, 0x139000); (0x13bbf8, 0x13bca0); (0x672295, 0x673c30)];
  lla_td_self := 0x673c38; lla_td_tid := 0x673c58; lla_td_locale := 0x673cd0; lla_locale := 0x693fc8; lla_td_canary := 0x673cf0;
  lla_guard := 0x693d40; lla_auxvp := 0x693f98;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x139000;
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
Lemma foot_a_eq : foot_a = [(0x6722c0, 0x6722c2); (0x672530, 0x672532); (0x672532, 0x672c70); (0x673398, 0x6733f0); (0x693d50, 0x693f70);
                            (0x6722e0, 0x6722e8); (0x6722c8, 0x6722e0); (0x672300, 0x672308); (0x6722e8, 0x672300)].
Proof. reflexivity. Qed.
Lemma foot_b_eq : foot_b = [(0x672280, 0x672282); (0x6724f0, 0x6724f2); (0x6724f2, 0x672c30); (0x673358, 0x6733b0); (0x673d90, 0x673fb0);
                            (0x6722a0, 0x6722a8); (0x672288, 0x6722a0); (0x6722c0, 0x6722c8); (0x6722a8, 0x6722c0)].
Proof. reflexivity. Qed.

End PNTAL.
