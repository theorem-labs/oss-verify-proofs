(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_dcef8 : bv 32 := 0xfff2f197.
Lemma F_dcef8 : fetch_word Ubsan.M.loaded_segments (0xe1830 : word) = Some W_dcef8.
Proof. vm_refl. Qed.
Lemma D_dcef8 : decode_any W_dcef8 = Some (Auipc 3 1048367, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcefc : bv 32 := 0xfd018193.
Lemma F_dcefc : fetch_word Ubsan.M.loaded_segments (0xe1834 : word) = Some W_dcefc.
Proof. vm_refl. Qed.
Lemma D_dcefc : decode_any W_dcefc = Some (OpImm ALU_ADD 3 3 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf00 : bv 32 := 0x00010513.
Lemma F_dcf00 : fetch_word Ubsan.M.loaded_segments (0xe1838 : word) = Some W_dcf00.
Proof. vm_refl. Qed.
Lemma D_dcf00 : decode_any W_dcf00 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf04 : bv 32 := 0xfff1e597.
Lemma F_dcf04 : fetch_word Ubsan.M.loaded_segments (0xe183c : word) = Some W_dcf04.
Proof. vm_refl. Qed.
Lemma D_dcf04 : decode_any W_dcf04 = Some (Auipc 11 1048350, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf08 : bv 32 := 0x7c458593.
Lemma F_dcf08 : fetch_word Ubsan.M.loaded_segments (0xe1840 : word) = Some W_dcf08.
Proof. vm_refl. Qed.
Lemma D_dcf08 : decode_any W_dcf08 = Some (OpImm ALU_ADD 11 11 1988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf0c : bv 32 := 0xff017113.
Lemma F_dcf0c : fetch_word Ubsan.M.loaded_segments (0xe1844 : word) = Some W_dcf0c.
Proof. vm_refl. Qed.
Lemma D_dcf0c : decode_any W_dcf0c = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf10 : bv 32 := 0x0040006f.
Lemma F_dcf10 : fetch_word Ubsan.M.loaded_segments (0xe1848 : word) = Some W_dcf10.
Proof. vm_refl. Qed.
Lemma D_dcf10 : decode_any W_dcf10 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf14 : bv 32 := 0x00052583.
Lemma F_dcf14 : fetch_word Ubsan.M.loaded_segments (0xe184c : word) = Some W_dcf14.
Proof. vm_refl. Qed.
Lemma D_dcf14 : decode_any W_dcf14 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf18 : bv 32 := 0x0023b617.
Lemma F_dcf18 : fetch_word Ubsan.M.loaded_segments (0xe1850 : word) = Some W_dcf18.
Proof. vm_refl. Qed.
Lemma D_dcf18 : decode_any W_dcf18 = Some (Auipc 12 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf1c : bv 32 := 0x0023b697.
Lemma F_dcf1c : fetch_word Ubsan.M.loaded_segments (0xe1854 : word) = Some W_dcf1c.
Proof. vm_refl. Qed.
Lemma D_dcf1c : decode_any W_dcf1c = Some (Auipc 13 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf20 : bv 32 := 0x0023b717.
Lemma F_dcf20 : fetch_word Ubsan.M.loaded_segments (0xe1858 : word) = Some W_dcf20.
Proof. vm_refl. Qed.
Lemma D_dcf20 : decode_any W_dcf20 = Some (Auipc 14 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf24 : bv 32 := 0x77063783.
Lemma F_dcf24 : fetch_word Ubsan.M.loaded_segments (0xe185c : word) = Some W_dcf24.
Proof. vm_refl. Qed.
Lemma D_dcf24 : decode_any W_dcf24 = Some (Load SZ8 true 15 12 1904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf28 : bv 32 := 0x7746b683.
Lemma F_dcf28 : fetch_word Ubsan.M.loaded_segments (0xe1860 : word) = Some W_dcf28.
Proof. vm_refl. Qed.
Lemma D_dcf28 : decode_any W_dcf28 = Some (Load SZ8 true 13 13 1908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf2c : bv 32 := 0x77873703.
Lemma F_dcf2c : fetch_word Ubsan.M.loaded_segments (0xe1864 : word) = Some W_dcf2c.
Proof. vm_refl. Qed.
Lemma D_dcf2c : decode_any W_dcf2c = Some (Load SZ8 true 14 14 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf30 : bv 32 := 0x00850613.
Lemma F_dcf30 : fetch_word Ubsan.M.loaded_segments (0xe1868 : word) = Some W_dcf30.
Proof. vm_refl. Qed.
Lemma D_dcf30 : decode_any W_dcf30 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf34 : bv 32 := 0x00078513.
Lemma F_dcf34 : fetch_word Ubsan.M.loaded_segments (0xe186c : word) = Some W_dcf34.
Proof. vm_refl. Qed.
Lemma D_dcf34 : decode_any W_dcf34 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf38 : bv 32 := 0x00000793.
Lemma F_dcf38 : fetch_word Ubsan.M.loaded_segments (0xe1870 : word) = Some W_dcf38.
Proof. vm_refl. Qed.
Lemma D_dcf38 : decode_any W_dcf38 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf3c : bv 32 := 0x001d0317.
Lemma F_dcf3c : fetch_word Ubsan.M.loaded_segments (0xe1874 : word) = Some W_dcf3c.
Proof. vm_refl. Qed.
Lemma D_dcf3c : decode_any W_dcf3c = Some (Auipc 6 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf40 : bv 32 := 0x84030067.
Lemma F_dcf40 : fetch_word Ubsan.M.loaded_segments (0xe1878 : word) = Some W_dcf40.
Proof. vm_refl. Qed.
Lemma D_dcf40 : decode_any W_dcf40 = Some (Jalr 0 6 2112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf44 : bv 32 := 0xff010113.
Lemma F_dcf44 : fetch_word Ubsan.M.loaded_segments (0xe187c : word) = Some W_dcf44.
Proof. vm_refl. Qed.
Lemma D_dcf44 : decode_any W_dcf44 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf48 : bv 32 := 0x00113423.
Lemma F_dcf48 : fetch_word Ubsan.M.loaded_segments (0xe1880 : word) = Some W_dcf48.
Proof. vm_refl. Qed.
Lemma D_dcf48 : decode_any W_dcf48 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf4c : bv 32 := 0x00813023.
Lemma F_dcf4c : fetch_word Ubsan.M.loaded_segments (0xe1884 : word) = Some W_dcf4c.
Proof. vm_refl. Qed.
Lemma D_dcf4c : decode_any W_dcf4c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf50 : bv 32 := 0x01010413.
Lemma F_dcf50 : fetch_word Ubsan.M.loaded_segments (0xe1888 : word) = Some W_dcf50.
Proof. vm_refl. Qed.
Lemma D_dcf50 : decode_any W_dcf50 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf54 : bv 32 := 0x0023d517.
Lemma F_dcf54 : fetch_word Ubsan.M.loaded_segments (0xe188c : word) = Some W_dcf54.
Proof. vm_refl. Qed.
Lemma D_dcf54 : decode_any W_dcf54 = Some (Auipc 10 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf58 : bv 32 := 0x63450513.
Lemma F_dcf58 : fetch_word Ubsan.M.loaded_segments (0xe1890 : word) = Some W_dcf58.
Proof. vm_refl. Qed.
Lemma D_dcf58 : decode_any W_dcf58 = Some (OpImm ALU_ADD 10 10 1588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf5c : bv 32 := 0x00054503.
Lemma F_dcf5c : fetch_word Ubsan.M.loaded_segments (0xe1894 : word) = Some W_dcf5c.
Proof. vm_refl. Qed.
Lemma D_dcf5c : decode_any W_dcf5c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf60 : bv 32 := 0x00157513.
Lemma F_dcf60 : fetch_word Ubsan.M.loaded_segments (0xe1898 : word) = Some W_dcf60.
Proof. vm_refl. Qed.
Lemma D_dcf60 : decode_any W_dcf60 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf64 : bv 32 := 0x00050663.
Lemma F_dcf64 : fetch_word Ubsan.M.loaded_segments (0xe189c : word) = Some W_dcf64.
Proof. vm_refl. Qed.
Lemma D_dcf64 : decode_any W_dcf64 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf68 : bv 32 := 0x0040006f.
Lemma F_dcf68 : fetch_word Ubsan.M.loaded_segments (0xe18a0 : word) = Some W_dcf68.
Proof. vm_refl. Qed.
Lemma D_dcf68 : decode_any W_dcf68 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf6c : bv 32 := 0x03c0006f.
Lemma F_dcf6c : fetch_word Ubsan.M.loaded_segments (0xe18a4 : word) = Some W_dcf6c.
Proof. vm_refl. Qed.
Lemma D_dcf6c : decode_any W_dcf6c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf70 : bv 32 := 0x0023d517.
Lemma F_dcf70 : fetch_word Ubsan.M.loaded_segments (0xe18a8 : word) = Some W_dcf70.
Proof. vm_refl. Qed.
Lemma D_dcf70 : decode_any W_dcf70 = Some (Auipc 10 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf74 : bv 32 := 0x61850593.
Lemma F_dcf74 : fetch_word Ubsan.M.loaded_segments (0xe18ac : word) = Some W_dcf74.
Proof. vm_refl. Qed.
Lemma D_dcf74 : decode_any W_dcf74 = Some (OpImm ALU_ADD 11 10 1560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf78 : bv 32 := 0x00100513.
Lemma F_dcf78 : fetch_word Ubsan.M.loaded_segments (0xe18b0 : word) = Some W_dcf78.
Proof. vm_refl. Qed.
Lemma D_dcf78 : decode_any W_dcf78 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf7c : bv 32 := 0x00a58023.
Lemma F_dcf7c : fetch_word Ubsan.M.loaded_segments (0xe18b4 : word) = Some W_dcf7c.
Proof. vm_refl. Qed.
Lemma D_dcf7c : decode_any W_dcf7c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf80 : bv 32 := 0x0023b517.
Lemma F_dcf80 : fetch_word Ubsan.M.loaded_segments (0xe18b8 : word) = Some W_dcf80.
Proof. vm_refl. Qed.
Lemma D_dcf80 : decode_any W_dcf80 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf84 : bv 32 := 0x72053503.
Lemma F_dcf84 : fetch_word Ubsan.M.loaded_segments (0xe18bc : word) = Some W_dcf84.
Proof. vm_refl. Qed.
Lemma D_dcf84 : decode_any W_dcf84 = Some (Load SZ8 true 10 10 1824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf88 : bv 32 := 0x02050063.
Lemma F_dcf88 : fetch_word Ubsan.M.loaded_segments (0xe18c0 : word) = Some W_dcf88.
Proof. vm_refl. Qed.
Lemma D_dcf88 : decode_any W_dcf88 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf8c : bv 32 := 0x0040006f.
Lemma F_dcf8c : fetch_word Ubsan.M.loaded_segments (0xe18c4 : word) = Some W_dcf8c.
Proof. vm_refl. Qed.
Lemma D_dcf8c : decode_any W_dcf8c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf90 : bv 32 := 0xfffa0517.
Lemma F_dcf90 : fetch_word Ubsan.M.loaded_segments (0xe18c8 : word) = Some W_dcf90.
Proof. vm_refl. Qed.
Lemma D_dcf90 : decode_any W_dcf90 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf94 : bv 32 := 0x2c050513.
Lemma F_dcf94 : fetch_word Ubsan.M.loaded_segments (0xe18cc : word) = Some W_dcf94.
Proof. vm_refl. Qed.
Lemma D_dcf94 : decode_any W_dcf94 = Some (OpImm ALU_ADD 10 10 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf98 : bv 32 := 0x0023d597.
Lemma F_dcf98 : fetch_word Ubsan.M.loaded_segments (0xe18d0 : word) = Some W_dcf98.
Proof. vm_refl. Qed.
Lemma D_dcf98 : decode_any W_dcf98 = Some (Auipc 11 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcf9c : bv 32 := 0x5f858593.
Lemma F_dcf9c : fetch_word Ubsan.M.loaded_segments (0xe18d4 : word) = Some W_dcf9c.
Proof. vm_refl. Qed.
Lemma D_dcf9c : decode_any W_dcf9c = Some (OpImm ALU_ADD 11 11 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfa0 : bv 32 := 0x000000ef.
Lemma F_dcfa0 : fetch_word Ubsan.M.loaded_segments (0xe18d8 : word) = Some W_dcfa0.
Proof. vm_refl. Qed.
Lemma D_dcfa0 : decode_any W_dcfa0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfa4 : bv 32 := 0x0040006f.
Lemma F_dcfa4 : fetch_word Ubsan.M.loaded_segments (0xe18dc : word) = Some W_dcfa4.
Proof. vm_refl. Qed.
Lemma D_dcfa4 : decode_any W_dcfa4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfa8 : bv 32 := 0x00813083.
Lemma F_dcfa8 : fetch_word Ubsan.M.loaded_segments (0xe18e0 : word) = Some W_dcfa8.
Proof. vm_refl. Qed.
Lemma D_dcfa8 : decode_any W_dcfa8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfac : bv 32 := 0x00013403.
Lemma F_dcfac : fetch_word Ubsan.M.loaded_segments (0xe18e4 : word) = Some W_dcfac.
Proof. vm_refl. Qed.
Lemma D_dcfac : decode_any W_dcfac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfb0 : bv 32 := 0x01010113.
Lemma F_dcfb0 : fetch_word Ubsan.M.loaded_segments (0xe18e8 : word) = Some W_dcfb0.
Proof. vm_refl. Qed.
Lemma D_dcfb0 : decode_any W_dcfb0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfb4 : bv 32 := 0x00008067.
Lemma F_dcfb4 : fetch_word Ubsan.M.loaded_segments (0xe18ec : word) = Some W_dcfb4.
Proof. vm_refl. Qed.
Lemma D_dcfb4 : decode_any W_dcfb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfb8 : bv 32 := 0xff010113.
Lemma F_dcfb8 : fetch_word Ubsan.M.loaded_segments (0xe18f0 : word) = Some W_dcfb8.
Proof. vm_refl. Qed.
Lemma D_dcfb8 : decode_any W_dcfb8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfbc : bv 32 := 0x00113423.
Lemma F_dcfbc : fetch_word Ubsan.M.loaded_segments (0xe18f4 : word) = Some W_dcfbc.
Proof. vm_refl. Qed.
Lemma D_dcfbc : decode_any W_dcfbc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfc0 : bv 32 := 0x00813023.
Lemma F_dcfc0 : fetch_word Ubsan.M.loaded_segments (0xe18f8 : word) = Some W_dcfc0.
Proof. vm_refl. Qed.
Lemma D_dcfc0 : decode_any W_dcfc0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfc4 : bv 32 := 0x01010413.
Lemma F_dcfc4 : fetch_word Ubsan.M.loaded_segments (0xe18fc : word) = Some W_dcfc4.
Proof. vm_refl. Qed.
Lemma D_dcfc4 : decode_any W_dcfc4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfc8 : bv 32 := 0x0023d517.
Lemma F_dcfc8 : fetch_word Ubsan.M.loaded_segments (0xe1900 : word) = Some W_dcfc8.
Proof. vm_refl. Qed.
Lemma D_dcfc8 : decode_any W_dcfc8 = Some (Auipc 10 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfcc : bv 32 := 0x60850513.
Lemma F_dcfcc : fetch_word Ubsan.M.loaded_segments (0xe1904 : word) = Some W_dcfcc.
Proof. vm_refl. Qed.
Lemma D_dcfcc : decode_any W_dcfcc = Some (OpImm ALU_ADD 10 10 1544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfd0 : bv 32 := 0x00054503.
Lemma F_dcfd0 : fetch_word Ubsan.M.loaded_segments (0xe1908 : word) = Some W_dcfd0.
Proof. vm_refl. Qed.
Lemma D_dcfd0 : decode_any W_dcfd0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfd4 : bv 32 := 0x00157513.
Lemma F_dcfd4 : fetch_word Ubsan.M.loaded_segments (0xe190c : word) = Some W_dcfd4.
Proof. vm_refl. Qed.
Lemma D_dcfd4 : decode_any W_dcfd4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfd8 : bv 32 := 0x00050663.
Lemma F_dcfd8 : fetch_word Ubsan.M.loaded_segments (0xe1910 : word) = Some W_dcfd8.
Proof. vm_refl. Qed.
Lemma D_dcfd8 : decode_any W_dcfd8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfdc : bv 32 := 0x0040006f.
Lemma F_dcfdc : fetch_word Ubsan.M.loaded_segments (0xe1914 : word) = Some W_dcfdc.
Proof. vm_refl. Qed.
Lemma D_dcfdc : decode_any W_dcfdc = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfe0 : bv 32 := 0x05c0006f.
Lemma F_dcfe0 : fetch_word Ubsan.M.loaded_segments (0xe1918 : word) = Some W_dcfe0.
Proof. vm_refl. Qed.
Lemma D_dcfe0 : decode_any W_dcfe0 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfe4 : bv 32 := 0x0023d517.
Lemma F_dcfe4 : fetch_word Ubsan.M.loaded_segments (0xe191c : word) = Some W_dcfe4.
Proof. vm_refl. Qed.
Lemma D_dcfe4 : decode_any W_dcfe4 = Some (Auipc 10 573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfe8 : bv 32 := 0x5ec50593.
Lemma F_dcfe8 : fetch_word Ubsan.M.loaded_segments (0xe1920 : word) = Some W_dcfe8.
Proof. vm_refl. Qed.
Lemma D_dcfe8 : decode_any W_dcfe8 = Some (OpImm ALU_ADD 11 10 1516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcfec : bv 32 := 0x00100513.
Lemma F_dcfec : fetch_word Ubsan.M.loaded_segments (0xe1924 : word) = Some W_dcfec.
Proof. vm_refl. Qed.
Lemma D_dcfec : decode_any W_dcfec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcff0 : bv 32 := 0x00a58023.
Lemma F_dcff0 : fetch_word Ubsan.M.loaded_segments (0xe1928 : word) = Some W_dcff0.
Proof. vm_refl. Qed.
Lemma D_dcff0 : decode_any W_dcff0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcff4 : bv 32 := 0x0023b517.
Lemma F_dcff4 : fetch_word Ubsan.M.loaded_segments (0xe192c : word) = Some W_dcff4.
Proof. vm_refl. Qed.
Lemma D_dcff4 : decode_any W_dcff4 = Some (Auipc 10 571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcff8 : bv 32 := 0x6b453503.
Lemma F_dcff8 : fetch_word Ubsan.M.loaded_segments (0xe1930 : word) = Some W_dcff8.
Proof. vm_refl. Qed.
Lemma D_dcff8 : decode_any W_dcff8 = Some (Load SZ8 true 10 10 1716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dcffc : bv 32 := 0x02050063.
Lemma F_dcffc : fetch_word Ubsan.M.loaded_segments (0xe1934 : word) = Some W_dcffc.
Proof. vm_refl. Qed.
Lemma D_dcffc : decode_any W_dcffc = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.
