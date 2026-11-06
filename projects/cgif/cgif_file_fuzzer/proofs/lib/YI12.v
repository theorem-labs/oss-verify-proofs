(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP02 YP0b YCef.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope. Open Scope Z_scope.
Definition tfib_B0 : Z := 0x80cf0.
Definition tfib_B1 : Z := 0x83dcc.
Definition tfib_sigma (s : asym) : Z :=
match s with
| AS_asan_stack_malloc_A => 0x3c8d4
| AS_asan_memset => 0x51aa8
| AS_fopen => 0x41980
| AS_malloc => 0x52960
| AS_asan_memcpy => 0x5160c
| AS_cgif_raw_newgif => 0x83dcc
| AS_fclose => 0x41988
| AS_free => 0x5295c
| AS_asan_report_load2 => 0x587c4
| AS_asan_report_store4 => 0x58b84
| AS_asan_report_load4 => 0x58864
| AS_asan_report_load8 => 0x58904
| AS_asan_report_store8 => 0x58c24
| AS_fwrite => 0x41944
| AS_asan_report_load1 => 0x58724
| AS_memcmp_2 => 0x41934
| AS_asan_report_store2 => 0x58ae4
| AS_asan_report_store1 => 0x58a44
| AS_memcmp => 0x41930
| AS_asan_stack_malloc_B => 0x3ca64
| AS_cgif_raw_addframe => 0x845d8
| AS_cgif_raw_close => 0x8656c
end.
Definition tfib_obj (i : nat) : Z :=
match i with
| 0%nat => 0x9e208
| 1%nat => 0x9e260
| 2%nat => 0x20040
| 3%nat => 0x9ee80
| 4%nat => 0x20e20
| 5%nat => 0x1a4a7
| 6%nat => 0x1cfee
| 7%nat => 0x9ee88
| 8%nat => 0x11b37
| 9%nat => 0x9ee90
| 10%nat => 0x103b0
| 11%nat => 0x20e60
| 12%nat => 0xa6278
| _ => 0
end.
Definition tfib_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9dd38
| 1%nat => 0x9dd3c
| 2%nat => 0x1fd9c
| 3%nat => 0x9eda0
| 4%nat => 0x20e7c
| 5%nat => 0x81080
| 6%nat => 0x9e33c
| 7%nat => 0x9e414
| 8%nat => 0x9e4d4
| 9%nat => 0x9e4c0
| 10%nat => 0x9e744
| 11%nat => 0x9e748
| 12%nat => 0x1a7c4
| 13%nat => 0x827c8
| 14%nat => 0x9dae4
| 15%nat => 0x9dbcc
| 16%nat => 0x9de14
| 17%nat => 0x9de18
| 18%nat => 0x1ce74
| 19%nat => 0x9ee78
| 20%nat => 0x9e624
| 21%nat => 0x9e628
| 22%nat => 0x11684
| 23%nat => 0x9f688
| 24%nat => 0x9e4c8
| 25%nat => 0x10128
| 26%nat => 0x9e58c
| 27%nat => 0x215c4
| 28%nat => 0x9e694
| 29%nat => 0x9daa8
| 30%nat => 0x9dc74
| _ => 0
end.
Definition tfib_val0 (a : nat) : Z :=
if (a =? A_TEXT)%nat then tfib_B0 else if (a <? A_HI 0)%nat then tfib_obj (a - A_OBJ 0) else tfib_hi (a - A_HI 0).
Definition tfib_val1 (a : nat) : Z :=
if (a =? A_TEXT)%nat then tfib_B1 else if (a <? A_HI 0)%nat then tfib_obj (a - A_OBJ 0) else tfib_hi (a - A_HI 0).
Lemma tfib_lib_check0 : pi_check asym (clookup tfibtbl_lib) tfib_val0 tfib_sigma lib_both3_0_listing = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_lib_check1 : pi_check asym (clookup tfibtbl_lib) tfib_val1 tfib_sigma lib_both3_1_listing = true.
Proof. vm_compute. reflexivity. Qed.
