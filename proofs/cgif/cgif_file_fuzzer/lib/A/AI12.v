(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP02 YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACef.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope. Open Scope Z_scope.
Definition tfib_B0 : Z := 0x81404.
Definition tfib_B1 : Z := 0x84178.
Definition tfib_sigma (s : asym) : Z :=
match s with
| AS_asan_stack_malloc_A => 0x3c8a4
| AS_asan_memset => 0x51a78
| AS_fopen => 0x41950
| AS_malloc => 0x52930
| AS_asan_memcpy => 0x515dc
| AS_cgif_raw_newgif => 0x84178
| AS_fclose => 0x41958
| AS_free => 0x5292c
| AS_asan_report_load2 => 0x58794
| AS_asan_report_store4 => 0x58b54
| AS_asan_report_load4 => 0x58834
| AS_asan_report_load8 => 0x588d4
| AS_asan_report_store8 => 0x58bf4
| AS_fwrite => 0x41914
| AS_asan_report_load1 => 0x586f4
| AS_memcmp_2 => 0x41904
| AS_asan_report_store2 => 0x58ab4
| AS_asan_report_store1 => 0x58a14
| AS_memcmp => 0x41900
| AS_asan_stack_malloc_B => 0x3ca34
| AS_cgif_raw_addframe => 0x84894
| AS_cgif_raw_close => 0x86684
end.
Definition tfib_obj (i : nat) : Z :=
match i with
| 0%nat => 0x9df98
| 1%nat => 0x9dff0
| 2%nat => 0x2007e
| 3%nat => 0x9ec10
| 4%nat => 0x20e60
| 5%nat => 0x1b8a0
| 6%nat => 0x1d02c
| 7%nat => 0x9ec18
| 8%nat => 0x11b37
| 9%nat => 0x9ec20
| 10%nat => 0x103b0
| 11%nat => 0x20ea0
| 12%nat => 0xa5ff8
| _ => 0
end.
Definition tfib_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9e44c
| 1%nat => 0x9e450
| 2%nat => 0x204b0
| 3%nat => 0x9e4b4
| 4%nat => 0x21584
| 5%nat => 0x81780
| 6%nat => 0x9da28
| 7%nat => 0x9daf4
| 8%nat => 0x9dba0
| 9%nat => 0x9d924
| 10%nat => 0x9db50
| 11%nat => 0x9db54
| 12%nat => 0x1bbb4
| 13%nat => 0x82bb8
| 14%nat => 0x9deac
| 15%nat => 0x9df7c
| 16%nat => 0x9e1c0
| 17%nat => 0x9e1c4
| 18%nat => 0x1d21c
| 19%nat => 0x9f220
| 20%nat => 0x9d8e0
| 21%nat => 0x9d8e4
| 22%nat => 0x1193c
| 23%nat => 0x9e940
| 24%nat => 0x9e604
| 25%nat => 0x101d0
| 26%nat => 0x9e694
| 27%nat => 0x206d0
| 28%nat => 0x9e78c
| 29%nat => 0x9da68
| _ => 0
end.
Definition tfib_val0 (a : nat) : Z :=
if (a =? A_TEXT)%nat then tfib_B0 else if (a <? A_HI 0)%nat then tfib_obj (a - A_OBJ 0) else tfib_hi (a - A_HI 0).
Definition tfib_val1 (a : nat) : Z :=
if (a =? A_TEXT)%nat then tfib_B1 else if (a <? A_HI 0)%nat then tfib_obj (a - A_OBJ 0) else tfib_hi (a - A_HI 0).
Lemma tfib_lib_check0 : pi_check asym (clookup tfibtbl_lib) tfib_val0 tfib_sigma lib_asan3_0_listing = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_lib_check1 : pi_check asym (clookup tfibtbl_lib) tfib_val1 tfib_sigma lib_asan3_1_listing = true.
Proof. vm_compute. reflexivity. Qed.
