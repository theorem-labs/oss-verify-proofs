(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition Wx_15295c : bv 32 := 0xf8d1806f.
Lemma Fx_15295c : fetch_word Asan.M.loaded_segments (0x1529a0 : word) = Some Wx_15295c.
Proof. vm_refl. Qed.
Lemma Dx_15295c : decode_any Wx_15295c = Some (Jal 0 1150860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a2c : bv 32 := 0x02060063.
Lemma Fx_152a2c : fetch_word Asan.M.loaded_segments (0x152a70 : word) = Some Wx_152a2c.
Proof. vm_refl. Qed.
Lemma Dx_152a2c : decode_any Wx_152a2c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a30 : bv 32 := 0x00054683.
Lemma Fx_152a30 : fetch_word Asan.M.loaded_segments (0x152a74 : word) = Some Wx_152a30.
Proof. vm_refl. Qed.
Lemma Dx_152a30 : decode_any Wx_152a30 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a34 : bv 32 := 0x0005c703.
Lemma Fx_152a34 : fetch_word Asan.M.loaded_segments (0x152a78 : word) = Some Wx_152a34.
Proof. vm_refl. Qed.
Lemma Dx_152a34 : decode_any Wx_152a34 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a38 : bv 32 := 0x00e69e63.
Lemma Fx_152a38 : fetch_word Asan.M.loaded_segments (0x152a7c : word) = Some Wx_152a38.
Proof. vm_refl. Qed.
Lemma Dx_152a38 : decode_any Wx_152a38 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a3c : bv 32 := 0xfff60613.
Lemma Fx_152a3c : fetch_word Asan.M.loaded_segments (0x152a80 : word) = Some Wx_152a3c.
Proof. vm_refl. Qed.
Lemma Dx_152a3c : decode_any Wx_152a3c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a40 : bv 32 := 0x00150513.
Lemma Fx_152a40 : fetch_word Asan.M.loaded_segments (0x152a84 : word) = Some Wx_152a40.
Proof. vm_refl. Qed.
Lemma Dx_152a40 : decode_any Wx_152a40 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a44 : bv 32 := 0x00158593.
Lemma Fx_152a44 : fetch_word Asan.M.loaded_segments (0x152a88 : word) = Some Wx_152a44.
Proof. vm_refl. Qed.
Lemma Dx_152a44 : decode_any Wx_152a44 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a48 : bv 32 := 0xfe0614e3.
Lemma Fx_152a48 : fetch_word Asan.M.loaded_segments (0x152a8c : word) = Some Wx_152a48.
Proof. vm_refl. Qed.
Lemma Dx_152a48 : decode_any Wx_152a48 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a4c : bv 32 := 0x00000513.
Lemma Fx_152a4c : fetch_word Asan.M.loaded_segments (0x152a90 : word) = Some Wx_152a4c.
Proof. vm_refl. Qed.
Lemma Dx_152a4c : decode_any Wx_152a4c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a50 : bv 32 := 0x00008067.
Lemma Fx_152a50 : fetch_word Asan.M.loaded_segments (0x152a94 : word) = Some Wx_152a50.
Proof. vm_refl. Qed.
Lemma Dx_152a50 : decode_any Wx_152a50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a54 : bv 32 := 0x40e68533.
Lemma Fx_152a54 : fetch_word Asan.M.loaded_segments (0x152a98 : word) = Some Wx_152a54.
Proof. vm_refl. Qed.
Lemma Dx_152a54 : decode_any Wx_152a54 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_152a58 : bv 32 := 0x00008067.
Lemma Fx_152a58 : fetch_word Asan.M.loaded_segments (0x152a9c : word) = Some Wx_152a58.
Proof. vm_refl. Qed.
Lemma Dx_152a58 : decode_any Wx_152a58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6b8dc : bv 32 := 0x32d0106f.
Lemma Fx_6b8dc : fetch_word Asan.M.loaded_segments (0x6b92c : word) = Some Wx_6b8dc.
Proof. vm_refl. Qed.
Lemma Dx_6b8dc : decode_any Wx_6b8dc = Some (Jal 0 6956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6b8e0 : bv 32 := 0x3e50106f.
Lemma Fx_6b8e0 : fetch_word Asan.M.loaded_segments (0x6b930 : word) = Some Wx_6b8e0.
Proof. vm_refl. Qed.
Lemma Dx_6b8e0 : decode_any Wx_6b8e0 = Some (Jal 0 7140, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6cb70 : bv 32 := 0x00008067.
Lemma Fx_6cb70 : fetch_word Asan.M.loaded_segments (0x6cbc0 : word) = Some Wx_6cb70.
Proof. vm_refl. Qed.
Lemma Dx_6cb70 : decode_any Wx_6cb70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb74 : bv 32 := 0x81010113.
Lemma Fx_6cb74 : fetch_word Asan.M.loaded_segments (0x6cbc4 : word) = Some Wx_6cb74.
Proof. vm_refl. Qed.
Lemma Dx_6cb74 : decode_any Wx_6cb74 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb78 : bv 32 := 0x7e113423.
Lemma Fx_6cb78 : fetch_word Asan.M.loaded_segments (0x6cbc8 : word) = Some Wx_6cb78.
Proof. vm_refl. Qed.
Lemma Dx_6cb78 : decode_any Wx_6cb78 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb7c : bv 32 := 0x7e813023.
Lemma Fx_6cb7c : fetch_word Asan.M.loaded_segments (0x6cbcc : word) = Some Wx_6cb7c.
Proof. vm_refl. Qed.
Lemma Dx_6cb7c : decode_any Wx_6cb7c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb80 : bv 32 := 0x7c913c23.
Lemma Fx_6cb80 : fetch_word Asan.M.loaded_segments (0x6cbd0 : word) = Some Wx_6cb80.
Proof. vm_refl. Qed.
Lemma Dx_6cb80 : decode_any Wx_6cb80 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb84 : bv 32 := 0x7d213823.
Lemma Fx_6cb84 : fetch_word Asan.M.loaded_segments (0x6cbd4 : word) = Some Wx_6cb84.
Proof. vm_refl. Qed.
Lemma Dx_6cb84 : decode_any Wx_6cb84 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb88 : bv 32 := 0x7d313423.
Lemma Fx_6cb88 : fetch_word Asan.M.loaded_segments (0x6cbd8 : word) = Some Wx_6cb88.
Proof. vm_refl. Qed.
Lemma Dx_6cb88 : decode_any Wx_6cb88 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb8c : bv 32 := 0x7d413023.
Lemma Fx_6cb8c : fetch_word Asan.M.loaded_segments (0x6cbdc : word) = Some Wx_6cb8c.
Proof. vm_refl. Qed.
Lemma Dx_6cb8c : decode_any Wx_6cb8c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb90 : bv 32 := 0x7b513c23.
Lemma Fx_6cb90 : fetch_word Asan.M.loaded_segments (0x6cbe0 : word) = Some Wx_6cb90.
Proof. vm_refl. Qed.
Lemma Dx_6cb90 : decode_any Wx_6cb90 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb94 : bv 32 := 0x7b613823.
Lemma Fx_6cb94 : fetch_word Asan.M.loaded_segments (0x6cbe4 : word) = Some Wx_6cb94.
Proof. vm_refl. Qed.
Lemma Dx_6cb94 : decode_any Wx_6cb94 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb98 : bv 32 := 0x7b713423.
Lemma Fx_6cb98 : fetch_word Asan.M.loaded_segments (0x6cbe8 : word) = Some Wx_6cb98.
Proof. vm_refl. Qed.
Lemma Dx_6cb98 : decode_any Wx_6cb98 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cb9c : bv 32 := 0x7b813023.
Lemma Fx_6cb9c : fetch_word Asan.M.loaded_segments (0x6cbec : word) = Some Wx_6cb9c.
Proof. vm_refl. Qed.
Lemma Dx_6cb9c : decode_any Wx_6cb9c = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cba0 : bv 32 := 0x79913c23.
Lemma Fx_6cba0 : fetch_word Asan.M.loaded_segments (0x6cbf0 : word) = Some Wx_6cba0.
Proof. vm_refl. Qed.
Lemma Dx_6cba0 : decode_any Wx_6cba0 = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cba4 : bv 32 := 0x79a13823.
Lemma Fx_6cba4 : fetch_word Asan.M.loaded_segments (0x6cbf4 : word) = Some Wx_6cba4.
Proof. vm_refl. Qed.
Lemma Dx_6cba4 : decode_any Wx_6cba4 = Some (Store SZ8 2 26 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cba8 : bv 32 := 0x79b13423.
Lemma Fx_6cba8 : fetch_word Asan.M.loaded_segments (0x6cbf8 : word) = Some Wx_6cba8.
Proof. vm_refl. Qed.
Lemma Dx_6cba8 : decode_any Wx_6cba8 = Some (Store SZ8 2 27 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbac : bv 32 := 0x7f010413.
Lemma Fx_6cbac : fetch_word Asan.M.loaded_segments (0x6cbfc : word) = Some Wx_6cbac.
Proof. vm_refl. Qed.
Lemma Dx_6cbac : decode_any Wx_6cbac = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbb0 : bv 32 := 0xf6010113.
Lemma Fx_6cbb0 : fetch_word Asan.M.loaded_segments (0x6cc00 : word) = Some Wx_6cbb0.
Proof. vm_refl. Qed.
Lemma Dx_6cbb0 : decode_any Wx_6cbb0 = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbb4 : bv 32 := 0x00008993.
Lemma Fx_6cbb4 : fetch_word Asan.M.loaded_segments (0x6cc04 : word) = Some Wx_6cbb4.
Proof. vm_refl. Qed.
Lemma Dx_6cbb4 : decode_any Wx_6cbb4 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbb8 : bv 32 := 0x00070493.
Lemma Fx_6cbb8 : fetch_word Asan.M.loaded_segments (0x6cc08 : word) = Some Wx_6cbb8.
Proof. vm_refl. Qed.
Lemma Dx_6cbb8 : decode_any Wx_6cbb8 = Some (OpImm ALU_ADD 9 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbbc : bv 32 := 0x00068913.
Lemma Fx_6cbbc : fetch_word Asan.M.loaded_segments (0x6cc0c : word) = Some Wx_6cbbc.
Proof. vm_refl. Qed.
Lemma Dx_6cbbc : decode_any Wx_6cbbc = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbc0 : bv 32 := 0x00060a13.
Lemma Fx_6cbc0 : fetch_word Asan.M.loaded_segments (0x6cc10 : word) = Some Wx_6cbc0.
Proof. vm_refl. Qed.
Lemma Dx_6cbc0 : decode_any Wx_6cbc0 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbc4 : bv 32 := 0x00058a93.
Lemma Fx_6cbc4 : fetch_word Asan.M.loaded_segments (0x6cc14 : word) = Some Wx_6cbc4.
Proof. vm_refl. Qed.
Lemma Dx_6cbc4 : decode_any Wx_6cbc4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbc8 : bv 32 := 0x000f4597.
Lemma Fx_6cbc8 : fetch_word Asan.M.loaded_segments (0x6cc18 : word) = Some Wx_6cbc8.
Proof. vm_refl. Qed.
Lemma Dx_6cbc8 : decode_any Wx_6cbc8 = Some (Auipc 11 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbcc : bv 32 := 0xff05bc03.
Lemma Fx_6cbcc : fetch_word Asan.M.loaded_segments (0x6cc1c : word) = Some Wx_6cbcc.
Proof. vm_refl. Qed.
Lemma Dx_6cbcc : decode_any Wx_6cbcc = Some (Load SZ8 true 24 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbd0 : bv 32 := 0x0fec4583.
Lemma Fx_6cbd0 : fetch_word Asan.M.loaded_segments (0x6cc20 : word) = Some Wx_6cbd0.
Proof. vm_refl. Qed.
Lemma Dx_6cbd0 : decode_any Wx_6cbd0 = Some (Load SZ1 false 11 24 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbd4 : bv 32 := 0x0a058863.
Lemma Fx_6cbd4 : fetch_word Asan.M.loaded_segments (0x6cc24 : word) = Some Wx_6cbd4.
Proof. vm_refl. Qed.
Lemma Dx_6cbd4 : decode_any Wx_6cbd4 = Some (Branch BC_EQ 11 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbd8 : bv 32 := 0x0ffc4583.
Lemma Fx_6cbd8 : fetch_word Asan.M.loaded_segments (0x6cc28 : word) = Some Wx_6cbd8.
Proof. vm_refl. Qed.
Lemma Dx_6cbd8 : decode_any Wx_6cbd8 = Some (Load SZ1 false 11 24 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbdc : bv 32 := 0x80040b93.
Lemma Fx_6cbdc : fetch_word Asan.M.loaded_segments (0x6cc2c : word) = Some Wx_6cbdc.
Proof. vm_refl. Qed.
Lemma Dx_6cbdc : decode_any Wx_6cbdc = Some (OpImm ALU_ADD 23 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbe0 : bv 32 := 0xf80b8b93.
Lemma Fx_6cbe0 : fetch_word Asan.M.loaded_segments (0x6cc30 : word) = Some Wx_6cbe0.
Proof. vm_refl. Qed.
Lemma Dx_6cbe0 : decode_any Wx_6cbe0 = Some (OpImm ALU_ADD 23 23 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbe4 : bv 32 := 0x0a058c63.
Lemma Fx_6cbe4 : fetch_word Asan.M.loaded_segments (0x6cc34 : word) = Some Wx_6cbe4.
Proof. vm_refl. Qed.
Lemma Dx_6cbe4 : decode_any Wx_6cbe4 = Some (Branch BC_EQ 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbe8 : bv 32 := 0xfffa4593.
Lemma Fx_6cbe8 : fetch_word Asan.M.loaded_segments (0x6cc38 : word) = Some Wx_6cbe8.
Proof. vm_refl. Qed.
Lemma Dx_6cbe8 : decode_any Wx_6cbe8 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbec : bv 32 := 0x2095e063.
Lemma Fx_6cbec : fetch_word Asan.M.loaded_segments (0x6cc3c : word) = Some Wx_6cbec.
Proof. vm_refl. Qed.
Lemma Dx_6cbec : decode_any Wx_6cbec = Some (Branch BC_LTU 11 9 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbf0 : bv 32 := 0xfbf48c93.
Lemma Fx_6cbf0 : fetch_word Asan.M.loaded_segments (0x6cc40 : word) = Some Wx_6cbf0.
Proof. vm_refl. Qed.
Lemma Dx_6cbf0 : decode_any Wx_6cbf0 = Some (OpImm ALU_ADD 25 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbf4 : bv 32 := 0xfbf00593.
Lemma Fx_6cbf4 : fetch_word Asan.M.loaded_segments (0x6cc44 : word) = Some Wx_6cbf4.
Proof. vm_refl. Qed.
Lemma Dx_6cbf4 : decode_any Wx_6cbf4 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbf8 : bv 32 := 0x2795f263.
Lemma Fx_6cbf8 : fetch_word Asan.M.loaded_segments (0x6cc48 : word) = Some Wx_6cbf8.
Proof. vm_refl. Qed.
Lemma Dx_6cbf8 : decode_any Wx_6cbf8 = Some (Branch BC_GEU 11 25 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cbfc : bv 32 := 0x000f4597.
Lemma Fx_6cbfc : fetch_word Asan.M.loaded_segments (0x6cc4c : word) = Some Wx_6cbfc.
Proof. vm_refl. Qed.
Lemma Dx_6cbfc : decode_any Wx_6cbfc = Some (Auipc 11 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc00 : bv 32 := 0xfcc5b583.
Lemma Fx_6cc00 : fetch_word Asan.M.loaded_segments (0x6cc50 : word) = Some Wx_6cc00.
Proof. vm_refl. Qed.
Lemma Dx_6cc00 : decode_any Wx_6cc00 = Some (Load SZ8 true 11 11 4044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc04 : bv 32 := 0x009a06b3.
Lemma Fx_6cc04 : fetch_word Asan.M.loaded_segments (0x6cc54 : word) = Some Wx_6cc04.
Proof. vm_refl. Qed.
Lemma Dx_6cc04 : decode_any Wx_6cc04 = Some (Op ALU_ADD 13 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc08 : bv 32 := 0x0005b603.
Lemma Fx_6cc08 : fetch_word Asan.M.loaded_segments (0x6cc58 : word) = Some Wx_6cc08.
Proof. vm_refl. Qed.
Lemma Dx_6cc08 : decode_any Wx_6cc08 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc0c : bv 32 := 0x003a5593.
Lemma Fx_6cc0c : fetch_word Asan.M.loaded_segments (0x6cc5c : word) = Some Wx_6cc0c.
Proof. vm_refl. Qed.
Lemma Dx_6cc0c : decode_any Wx_6cc0c = Some (ShiftImm ALU_SRL 11 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc10 : bv 32 := 0xfff68693.
Lemma Fx_6cc10 : fetch_word Asan.M.loaded_segments (0x6cc60 : word) = Some Wx_6cc10.
Proof. vm_refl. Qed.
Lemma Dx_6cc10 : decode_any Wx_6cc10 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc14 : bv 32 := 0x0036d713.
Lemma Fx_6cc14 : fetch_word Asan.M.loaded_segments (0x6cc64 : word) = Some Wx_6cc14.
Proof. vm_refl. Qed.
Lemma Dx_6cc14 : decode_any Wx_6cc14 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc18 : bv 32 := 0x00b605b3.
Lemma Fx_6cc18 : fetch_word Asan.M.loaded_segments (0x6cc68 : word) = Some Wx_6cc18.
Proof. vm_refl. Qed.
Lemma Dx_6cc18 : decode_any Wx_6cc18 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc1c : bv 32 := 0x00e60633.
Lemma Fx_6cc1c : fetch_word Asan.M.loaded_segments (0x6cc6c : word) = Some Wx_6cc1c.
Proof. vm_refl. Qed.
Lemma Dx_6cc1c : decode_any Wx_6cc1c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc20 : bv 32 := 0xff85f713.
Lemma Fx_6cc20 : fetch_word Asan.M.loaded_segments (0x6cc70 : word) = Some Wx_6cc20.
Proof. vm_refl. Qed.
Lemma Dx_6cc20 : decode_any Wx_6cc20 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc24 : bv 32 := 0xff867793.
Lemma Fx_6cc24 : fetch_word Asan.M.loaded_segments (0x6cc74 : word) = Some Wx_6cc24.
Proof. vm_refl. Qed.
Lemma Dx_6cc24 : decode_any Wx_6cc24 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc28 : bv 32 := 0x00073703.
Lemma Fx_6cc28 : fetch_word Asan.M.loaded_segments (0x6cc78 : word) = Some Wx_6cc28.
Proof. vm_refl. Qed.
Lemma Dx_6cc28 : decode_any Wx_6cc28 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc2c : bv 32 := 0x0007b783.
Lemma Fx_6cc2c : fetch_word Asan.M.loaded_segments (0x6cc7c : word) = Some Wx_6cc2c.
Proof. vm_refl. Qed.
Lemma Dx_6cc2c : decode_any Wx_6cc2c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc30 : bv 32 := 0x00e7e733.
Lemma Fx_6cc30 : fetch_word Asan.M.loaded_segments (0x6cc80 : word) = Some Wx_6cc30.
Proof. vm_refl. Qed.
Lemma Dx_6cc30 : decode_any Wx_6cc30 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc34 : bv 32 := 0x3a071063.
Lemma Fx_6cc34 : fetch_word Asan.M.loaded_segments (0x6cc84 : word) = Some Wx_6cc34.
Proof. vm_refl. Qed.
Lemma Dx_6cc34 : decode_any Wx_6cc34 = Some (Branch BC_NE 14 0 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc38 : bv 32 := 0xfff94593.
Lemma Fx_6cc38 : fetch_word Asan.M.loaded_segments (0x6cc88 : word) = Some Wx_6cc38.
Proof. vm_refl. Qed.
Lemma Dx_6cc38 : decode_any Wx_6cc38 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc3c : bv 32 := 0x2295e463.
Lemma Fx_6cc3c : fetch_word Asan.M.loaded_segments (0x6cc8c : word) = Some Wx_6cc3c.
Proof. vm_refl. Qed.
Lemma Dx_6cc3c : decode_any Wx_6cc3c = Some (Branch BC_LTU 11 9 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc40 : bv 32 := 0xfbf00593.
Lemma Fx_6cc40 : fetch_word Asan.M.loaded_segments (0x6cc90 : word) = Some Wx_6cc40.
Proof. vm_refl. Qed.
Lemma Dx_6cc40 : decode_any Wx_6cc40 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc44 : bv 32 := 0x2995f663.
Lemma Fx_6cc44 : fetch_word Asan.M.loaded_segments (0x6cc94 : word) = Some Wx_6cc44.
Proof. vm_refl. Qed.
Lemma Dx_6cc44 : decode_any Wx_6cc44 = Some (Branch BC_GEU 11 25 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc48 : bv 32 := 0x000f4597.
Lemma Fx_6cc48 : fetch_word Asan.M.loaded_segments (0x6cc98 : word) = Some Wx_6cc48.
Proof. vm_refl. Qed.
Lemma Dx_6cc48 : decode_any Wx_6cc48 = Some (Auipc 11 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc4c : bv 32 := 0xf805b583.
Lemma Fx_6cc4c : fetch_word Asan.M.loaded_segments (0x6cc9c : word) = Some Wx_6cc4c.
Proof. vm_refl. Qed.
Lemma Dx_6cc4c : decode_any Wx_6cc4c = Some (Load SZ8 true 11 11 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc50 : bv 32 := 0x009906b3.
Lemma Fx_6cc50 : fetch_word Asan.M.loaded_segments (0x6cca0 : word) = Some Wx_6cc50.
Proof. vm_refl. Qed.
Lemma Dx_6cc50 : decode_any Wx_6cc50 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc54 : bv 32 := 0x0005b603.
Lemma Fx_6cc54 : fetch_word Asan.M.loaded_segments (0x6cca4 : word) = Some Wx_6cc54.
Proof. vm_refl. Qed.
Lemma Dx_6cc54 : decode_any Wx_6cc54 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc58 : bv 32 := 0x00395593.
Lemma Fx_6cc58 : fetch_word Asan.M.loaded_segments (0x6cca8 : word) = Some Wx_6cc58.
Proof. vm_refl. Qed.
Lemma Dx_6cc58 : decode_any Wx_6cc58 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc5c : bv 32 := 0xfff68693.
Lemma Fx_6cc5c : fetch_word Asan.M.loaded_segments (0x6ccac : word) = Some Wx_6cc5c.
Proof. vm_refl. Qed.
Lemma Dx_6cc5c : decode_any Wx_6cc5c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc60 : bv 32 := 0x0036d713.
Lemma Fx_6cc60 : fetch_word Asan.M.loaded_segments (0x6ccb0 : word) = Some Wx_6cc60.
Proof. vm_refl. Qed.
Lemma Dx_6cc60 : decode_any Wx_6cc60 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc64 : bv 32 := 0x00b605b3.
Lemma Fx_6cc64 : fetch_word Asan.M.loaded_segments (0x6ccb4 : word) = Some Wx_6cc64.
Proof. vm_refl. Qed.
Lemma Dx_6cc64 : decode_any Wx_6cc64 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc68 : bv 32 := 0x00e60633.
Lemma Fx_6cc68 : fetch_word Asan.M.loaded_segments (0x6ccb8 : word) = Some Wx_6cc68.
Proof. vm_refl. Qed.
Lemma Dx_6cc68 : decode_any Wx_6cc68 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc6c : bv 32 := 0xff85f713.
Lemma Fx_6cc6c : fetch_word Asan.M.loaded_segments (0x6ccbc : word) = Some Wx_6cc6c.
Proof. vm_refl. Qed.
Lemma Dx_6cc6c : decode_any Wx_6cc6c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc70 : bv 32 := 0xff867793.
Lemma Fx_6cc70 : fetch_word Asan.M.loaded_segments (0x6ccc0 : word) = Some Wx_6cc70.
Proof. vm_refl. Qed.
Lemma Dx_6cc70 : decode_any Wx_6cc70 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc74 : bv 32 := 0x00073703.
Lemma Fx_6cc74 : fetch_word Asan.M.loaded_segments (0x6ccc4 : word) = Some Wx_6cc74.
Proof. vm_refl. Qed.
Lemma Dx_6cc74 : decode_any Wx_6cc74 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc78 : bv 32 := 0x0007b783.
Lemma Fx_6cc78 : fetch_word Asan.M.loaded_segments (0x6ccc8 : word) = Some Wx_6cc78.
Proof. vm_refl. Qed.
Lemma Dx_6cc78 : decode_any Wx_6cc78 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc7c : bv 32 := 0x00e7e733.
Lemma Fx_6cc7c : fetch_word Asan.M.loaded_segments (0x6cccc : word) = Some Wx_6cc7c.
Proof. vm_refl. Qed.
Lemma Dx_6cc7c : decode_any Wx_6cc7c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc80 : bv 32 := 0x46071063.
Lemma Fx_6cc80 : fetch_word Asan.M.loaded_segments (0x6ccd0 : word) = Some Wx_6cc80.
Proof. vm_refl. Qed.
Lemma Dx_6cc80 : decode_any Wx_6cc80 = Some (Branch BC_NE 14 0 1120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc84 : bv 32 := 0x000a0513.
Lemma Fx_6cc84 : fetch_word Asan.M.loaded_segments (0x6ccd4 : word) = Some Wx_6cc84.
Proof. vm_refl. Qed.
Lemma Dx_6cc84 : decode_any Wx_6cc84 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc88 : bv 32 := 0x00090593.
Lemma Fx_6cc88 : fetch_word Asan.M.loaded_segments (0x6ccd8 : word) = Some Wx_6cc88.
Proof. vm_refl. Qed.
Lemma Dx_6cc88 : decode_any Wx_6cc88 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc8c : bv 32 := 0x00048613.
Lemma Fx_6cc8c : fetch_word Asan.M.loaded_segments (0x6ccdc : word) = Some Wx_6cc8c.
Proof. vm_refl. Qed.
Lemma Dx_6cc8c : decode_any Wx_6cc8c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc90 : bv 32 := 0x000a80e7.
Lemma Fx_6cc90 : fetch_word Asan.M.loaded_segments (0x6cce0 : word) = Some Wx_6cc90.
Proof. vm_refl. Qed.
Lemma Dx_6cc90 : decode_any Wx_6cc90 = Some (Jalr 1 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc94 : bv 32 := 0x00050a93.
Lemma Fx_6cc94 : fetch_word Asan.M.loaded_segments (0x6cce4 : word) = Some Wx_6cc94.
Proof. vm_refl. Qed.
Lemma Dx_6cc94 : decode_any Wx_6cc94 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cc98 : bv 32 := 0x0e40006f.
Lemma Fx_6cc98 : fetch_word Asan.M.loaded_segments (0x6cce8 : word) = Some Wx_6cc98.
Proof. vm_refl. Qed.
Lemma Dx_6cc98 : decode_any Wx_6cc98 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd7c : bv 32 := 0x00098513.
Lemma Fx_6cd7c : fetch_word Asan.M.loaded_segments (0x6cdcc : word) = Some Wx_6cd7c.
Proof. vm_refl. Qed.
Lemma Dx_6cd7c : decode_any Wx_6cd7c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd80 : bv 32 := 0x000a0593.
Lemma Fx_6cd80 : fetch_word Asan.M.loaded_segments (0x6cdd0 : word) = Some Wx_6cd80.
Proof. vm_refl. Qed.
Lemma Dx_6cd80 : decode_any Wx_6cd80 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd84 : bv 32 := 0x00090613.
Lemma Fx_6cd84 : fetch_word Asan.M.loaded_segments (0x6cdd4 : word) = Some Wx_6cd84.
Proof. vm_refl. Qed.
Lemma Dx_6cd84 : decode_any Wx_6cd84 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd88 : bv 32 := 0x00048693.
Lemma Fx_6cd88 : fetch_word Asan.M.loaded_segments (0x6cdd8 : word) = Some Wx_6cd88.
Proof. vm_refl. Qed.
Lemma Dx_6cd88 : decode_any Wx_6cd88 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd8c : bv 32 := 0x000a8713.
Lemma Fx_6cd8c : fetch_word Asan.M.loaded_segments (0x6cddc : word) = Some Wx_6cd8c.
Proof. vm_refl. Qed.
Lemma Dx_6cd8c : decode_any Wx_6cd8c = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd90 : bv 32 := 0xde1ff0ef.
Lemma Fx_6cd90 : fetch_word Asan.M.loaded_segments (0x6cde0 : word) = Some Wx_6cd90.
Proof. vm_refl. Qed.
Lemma Dx_6cd90 : decode_any Wx_6cd90 = Some (Jal 1 2096608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd94 : bv 32 := 0x000a8513.
Lemma Fx_6cd94 : fetch_word Asan.M.loaded_segments (0x6cde4 : word) = Some Wx_6cd94.
Proof. vm_refl. Qed.
Lemma Dx_6cd94 : decode_any Wx_6cd94 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd98 : bv 32 := 0x0a010113.
Lemma Fx_6cd98 : fetch_word Asan.M.loaded_segments (0x6cde8 : word) = Some Wx_6cd98.
Proof. vm_refl. Qed.
Lemma Dx_6cd98 : decode_any Wx_6cd98 = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cd9c : bv 32 := 0x7e813083.
Lemma Fx_6cd9c : fetch_word Asan.M.loaded_segments (0x6cdec : word) = Some Wx_6cd9c.
Proof. vm_refl. Qed.
Lemma Dx_6cd9c : decode_any Wx_6cd9c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cda0 : bv 32 := 0x7e013403.
Lemma Fx_6cda0 : fetch_word Asan.M.loaded_segments (0x6cdf0 : word) = Some Wx_6cda0.
Proof. vm_refl. Qed.
Lemma Dx_6cda0 : decode_any Wx_6cda0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cda4 : bv 32 := 0x7d813483.
Lemma Fx_6cda4 : fetch_word Asan.M.loaded_segments (0x6cdf4 : word) = Some Wx_6cda4.
Proof. vm_refl. Qed.
Lemma Dx_6cda4 : decode_any Wx_6cda4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cda8 : bv 32 := 0x7d013903.
Lemma Fx_6cda8 : fetch_word Asan.M.loaded_segments (0x6cdf8 : word) = Some Wx_6cda8.
Proof. vm_refl. Qed.
Lemma Dx_6cda8 : decode_any Wx_6cda8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdac : bv 32 := 0x7c813983.
Lemma Fx_6cdac : fetch_word Asan.M.loaded_segments (0x6cdfc : word) = Some Wx_6cdac.
Proof. vm_refl. Qed.
Lemma Dx_6cdac : decode_any Wx_6cdac = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdb0 : bv 32 := 0x7c013a03.
Lemma Fx_6cdb0 : fetch_word Asan.M.loaded_segments (0x6ce00 : word) = Some Wx_6cdb0.
Proof. vm_refl. Qed.
Lemma Dx_6cdb0 : decode_any Wx_6cdb0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdb4 : bv 32 := 0x7b813a83.
Lemma Fx_6cdb4 : fetch_word Asan.M.loaded_segments (0x6ce04 : word) = Some Wx_6cdb4.
Proof. vm_refl. Qed.
Lemma Dx_6cdb4 : decode_any Wx_6cdb4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdb8 : bv 32 := 0x7b013b03.
Lemma Fx_6cdb8 : fetch_word Asan.M.loaded_segments (0x6ce08 : word) = Some Wx_6cdb8.
Proof. vm_refl. Qed.
Lemma Dx_6cdb8 : decode_any Wx_6cdb8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdbc : bv 32 := 0x7a813b83.
Lemma Fx_6cdbc : fetch_word Asan.M.loaded_segments (0x6ce0c : word) = Some Wx_6cdbc.
Proof. vm_refl. Qed.
Lemma Dx_6cdbc : decode_any Wx_6cdbc = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdc0 : bv 32 := 0x7a013c03.
Lemma Fx_6cdc0 : fetch_word Asan.M.loaded_segments (0x6ce10 : word) = Some Wx_6cdc0.
Proof. vm_refl. Qed.
Lemma Dx_6cdc0 : decode_any Wx_6cdc0 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdc4 : bv 32 := 0x79813c83.
Lemma Fx_6cdc4 : fetch_word Asan.M.loaded_segments (0x6ce14 : word) = Some Wx_6cdc4.
Proof. vm_refl. Qed.
Lemma Dx_6cdc4 : decode_any Wx_6cdc4 = Some (Load SZ8 true 25 2 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdc8 : bv 32 := 0x79013d03.
Lemma Fx_6cdc8 : fetch_word Asan.M.loaded_segments (0x6ce18 : word) = Some Wx_6cdc8.
Proof. vm_refl. Qed.
Lemma Dx_6cdc8 : decode_any Wx_6cdc8 = Some (Load SZ8 true 26 2 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdcc : bv 32 := 0x78813d83.
Lemma Fx_6cdcc : fetch_word Asan.M.loaded_segments (0x6ce1c : word) = Some Wx_6cdcc.
Proof. vm_refl. Qed.
Lemma Dx_6cdcc : decode_any Wx_6cdcc = Some (Load SZ8 true 27 2 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdd0 : bv 32 := 0x7f010113.
Lemma Fx_6cdd0 : fetch_word Asan.M.loaded_segments (0x6ce20 : word) = Some Wx_6cdd0.
Proof. vm_refl. Qed.
Lemma Dx_6cdd0 : decode_any Wx_6cdd0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cdd4 : bv 32 := 0x00008067.
Lemma Fx_6cdd4 : fetch_word Asan.M.loaded_segments (0x6ce24 : word) = Some Wx_6cdd4.
Proof. vm_refl. Qed.
Lemma Dx_6cdd4 : decode_any Wx_6cdd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ce5c : bv 32 := 0x1a049663.
Lemma Fx_6ce5c : fetch_word Asan.M.loaded_segments (0x6ceac : word) = Some Wx_6ce5c.
Proof. vm_refl. Qed.
Lemma Dx_6ce5c : decode_any Wx_6ce5c = Some (Branch BC_NE 9 0 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ce60 : bv 32 := 0xdd9ff06f.
Lemma Fx_6ce60 : fetch_word Asan.M.loaded_segments (0x6ceb0 : word) = Some Wx_6ce60.
Proof. vm_refl. Qed.
Lemma Dx_6ce60 : decode_any Wx_6ce60 = Some (Jal 0 2096600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ced0 : bv 32 := 0x24049263.
Lemma Fx_6ced0 : fetch_word Asan.M.loaded_segments (0x6cf20 : word) = Some Wx_6ced0.
Proof. vm_refl. Qed.
Lemma Dx_6ced0 : decode_any Wx_6ced0 = Some (Branch BC_NE 9 0 580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ced4 : bv 32 := 0xdb1ff06f.
Lemma Fx_6ced4 : fetch_word Asan.M.loaded_segments (0x6cf24 : word) = Some Wx_6ced4.
Proof. vm_refl. Qed.
Lemma Dx_6ced4 : decode_any Wx_6ced4 = Some (Jal 0 2096560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfd4 : bv 32 := 0x00060703.
Lemma Fx_6cfd4 : fetch_word Asan.M.loaded_segments (0x6d024 : word) = Some Wx_6cfd4.
Proof. vm_refl. Qed.
Lemma Dx_6cfd4 : decode_any Wx_6cfd4 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfd8 : bv 32 := 0x0076f693.
Lemma Fx_6cfd8 : fetch_word Asan.M.loaded_segments (0x6d028 : word) = Some Wx_6cfd8.
Proof. vm_refl. Qed.
Lemma Dx_6cfd8 : decode_any Wx_6cfd8 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfdc : bv 32 := 0x00e037b3.
Lemma Fx_6cfdc : fetch_word Asan.M.loaded_segments (0x6d02c : word) = Some Wx_6cfdc.
Proof. vm_refl. Qed.
Lemma Dx_6cfdc : decode_any Wx_6cfdc = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfe0 : bv 32 := 0x00e6a6b3.
Lemma Fx_6cfe0 : fetch_word Asan.M.loaded_segments (0x6d030 : word) = Some Wx_6cfe0.
Proof. vm_refl. Qed.
Lemma Dx_6cfe0 : decode_any Wx_6cfe0 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfe4 : bv 32 := 0x0016c693.
Lemma Fx_6cfe4 : fetch_word Asan.M.loaded_segments (0x6d034 : word) = Some Wx_6cfe4.
Proof. vm_refl. Qed.
Lemma Dx_6cfe4 : decode_any Wx_6cfe4 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfe8 : bv 32 := 0x00d7f6b3.
Lemma Fx_6cfe8 : fetch_word Asan.M.loaded_segments (0x6d038 : word) = Some Wx_6cfe8.
Proof. vm_refl. Qed.
Lemma Dx_6cfe8 : decode_any Wx_6cfe8 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cfec : bv 32 := 0x00c5fa63.
Lemma Fx_6cfec : fetch_word Asan.M.loaded_segments (0x6d03c : word) = Some Wx_6cfec.
Proof. vm_refl. Qed.
Lemma Dx_6cfec : decode_any Wx_6cfec = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cff0 : bv 32 := 0x0005c703.
Lemma Fx_6cff0 : fetch_word Asan.M.loaded_segments (0x6d040 : word) = Some Wx_6cff0.
Proof. vm_refl. Qed.
Lemma Dx_6cff0 : decode_any Wx_6cff0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cff4 : bv 32 := 0x00158593.
Lemma Fx_6cff4 : fetch_word Asan.M.loaded_segments (0x6d044 : word) = Some Wx_6cff4.
Proof. vm_refl. Qed.
Lemma Dx_6cff4 : decode_any Wx_6cff4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cff8 : bv 32 := 0x00d766b3.
Lemma Fx_6cff8 : fetch_word Asan.M.loaded_segments (0x6d048 : word) = Some Wx_6cff8.
Proof. vm_refl. Qed.
Lemma Dx_6cff8 : decode_any Wx_6cff8 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6cffc : bv 32 := 0xfec59ae3.
Lemma Fx_6cffc : fetch_word Asan.M.loaded_segments (0x6d04c : word) = Some Wx_6cffc.
Proof. vm_refl. Qed.
Lemma Dx_6cffc : decode_any Wx_6cffc = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6d000 : bv 32 := 0x0ff6f593.
Lemma Fx_6d000 : fetch_word Asan.M.loaded_segments (0x6d050 : word) = Some Wx_6d000.
Proof. vm_refl. Qed.
Lemma Dx_6d000 : decode_any Wx_6d000 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d004 : bv 32 := 0xc2058ae3.
Lemma Fx_6d004 : fetch_word Asan.M.loaded_segments (0x6d054 : word) = Some Wx_6d004.
Proof. vm_refl. Qed.
Lemma Dx_6d004 : decode_any Wx_6d004 = Some (Branch BC_EQ 11 0 7220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d008 : bv 32 := 0x00050d13.
Lemma Fx_6d008 : fetch_word Asan.M.loaded_segments (0x6d058 : word) = Some Wx_6d008.
Proof. vm_refl. Qed.
Lemma Dx_6d008 : decode_any Wx_6d008 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d00c : bv 32 := 0x000a0513.
Lemma Fx_6d00c : fetch_word Asan.M.loaded_segments (0x6d05c : word) = Some Wx_6d00c.
Proof. vm_refl. Qed.
Lemma Dx_6d00c : decode_any Wx_6d00c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d010 : bv 32 := 0x00048593.
Lemma Fx_6d010 : fetch_word Asan.M.loaded_segments (0x6d060 : word) = Some Wx_6d010.
Proof. vm_refl. Qed.
Lemma Dx_6d010 : decode_any Wx_6d010 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d014 : bv 32 := 0x209160ef.
Lemma Fx_6d014 : fetch_word Asan.M.loaded_segments (0x6d064 : word) = Some Wx_6d014.
Proof. vm_refl. Qed.
Lemma Dx_6d014 : decode_any Wx_6d014 = Some (Jal 1 92680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d018 : bv 32 := 0x00050b13.
Lemma Fx_6d018 : fetch_word Asan.M.loaded_segments (0x6d068 : word) = Some Wx_6d018.
Proof. vm_refl. Qed.
Lemma Dx_6d018 : decode_any Wx_6d018 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d01c : bv 32 := 0x000d0513.
Lemma Fx_6d01c : fetch_word Asan.M.loaded_segments (0x6d06c : word) = Some Wx_6d01c.
Proof. vm_refl. Qed.
Lemma Dx_6d01c : decode_any Wx_6d01c = Some (OpImm ALU_ADD 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d020 : bv 32 := 0xc00b0ce3.
Lemma Fx_6d020 : fetch_word Asan.M.loaded_segments (0x6d070 : word) = Some Wx_6d020.
Proof. vm_refl. Qed.
Lemma Dx_6d020 : decode_any Wx_6d020 = Some (Branch BC_EQ 22 0 7192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0e0 : bv 32 := 0x00060703.
Lemma Fx_6d0e0 : fetch_word Asan.M.loaded_segments (0x6d130 : word) = Some Wx_6d0e0.
Proof. vm_refl. Qed.
Lemma Dx_6d0e0 : decode_any Wx_6d0e0 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0e4 : bv 32 := 0x0076f693.
Lemma Fx_6d0e4 : fetch_word Asan.M.loaded_segments (0x6d134 : word) = Some Wx_6d0e4.
Proof. vm_refl. Qed.
Lemma Dx_6d0e4 : decode_any Wx_6d0e4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0e8 : bv 32 := 0x00e037b3.
Lemma Fx_6d0e8 : fetch_word Asan.M.loaded_segments (0x6d138 : word) = Some Wx_6d0e8.
Proof. vm_refl. Qed.
Lemma Dx_6d0e8 : decode_any Wx_6d0e8 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0ec : bv 32 := 0x00e6a6b3.
Lemma Fx_6d0ec : fetch_word Asan.M.loaded_segments (0x6d13c : word) = Some Wx_6d0ec.
Proof. vm_refl. Qed.
Lemma Dx_6d0ec : decode_any Wx_6d0ec = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0f0 : bv 32 := 0x0016c693.
Lemma Fx_6d0f0 : fetch_word Asan.M.loaded_segments (0x6d140 : word) = Some Wx_6d0f0.
Proof. vm_refl. Qed.
Lemma Dx_6d0f0 : decode_any Wx_6d0f0 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0f4 : bv 32 := 0x00d7f6b3.
Lemma Fx_6d0f4 : fetch_word Asan.M.loaded_segments (0x6d144 : word) = Some Wx_6d0f4.
Proof. vm_refl. Qed.
Lemma Dx_6d0f4 : decode_any Wx_6d0f4 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0f8 : bv 32 := 0x00c5fa63.
Lemma Fx_6d0f8 : fetch_word Asan.M.loaded_segments (0x6d148 : word) = Some Wx_6d0f8.
Proof. vm_refl. Qed.
Lemma Dx_6d0f8 : decode_any Wx_6d0f8 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d0fc : bv 32 := 0x0005c703.
Lemma Fx_6d0fc : fetch_word Asan.M.loaded_segments (0x6d14c : word) = Some Wx_6d0fc.
Proof. vm_refl. Qed.
Lemma Dx_6d0fc : decode_any Wx_6d0fc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d100 : bv 32 := 0x00158593.
Lemma Fx_6d100 : fetch_word Asan.M.loaded_segments (0x6d150 : word) = Some Wx_6d100.
Proof. vm_refl. Qed.
Lemma Dx_6d100 : decode_any Wx_6d100 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d104 : bv 32 := 0x00d766b3.
Lemma Fx_6d104 : fetch_word Asan.M.loaded_segments (0x6d154 : word) = Some Wx_6d104.
Proof. vm_refl. Qed.
Lemma Dx_6d104 : decode_any Wx_6d104 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d108 : bv 32 := 0xfec59ae3.
Lemma Fx_6d108 : fetch_word Asan.M.loaded_segments (0x6d158 : word) = Some Wx_6d108.
Proof. vm_refl. Qed.
Lemma Dx_6d108 : decode_any Wx_6d108 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d10c : bv 32 := 0x0ff6f593.
Lemma Fx_6d10c : fetch_word Asan.M.loaded_segments (0x6d15c : word) = Some Wx_6d10c.
Proof. vm_refl. Qed.
Lemma Dx_6d10c : decode_any Wx_6d10c = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d110 : bv 32 := 0xb6058ae3.
Lemma Fx_6d110 : fetch_word Asan.M.loaded_segments (0x6d160 : word) = Some Wx_6d110.
Proof. vm_refl. Qed.
Lemma Dx_6d110 : decode_any Wx_6d110 = Some (Branch BC_EQ 11 0 7028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d114 : bv 32 := 0x00050c93.
Lemma Fx_6d114 : fetch_word Asan.M.loaded_segments (0x6d164 : word) = Some Wx_6d114.
Proof. vm_refl. Qed.
Lemma Dx_6d114 : decode_any Wx_6d114 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d118 : bv 32 := 0x00090513.
Lemma Fx_6d118 : fetch_word Asan.M.loaded_segments (0x6d168 : word) = Some Wx_6d118.
Proof. vm_refl. Qed.
Lemma Dx_6d118 : decode_any Wx_6d118 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d11c : bv 32 := 0x00048593.
Lemma Fx_6d11c : fetch_word Asan.M.loaded_segments (0x6d16c : word) = Some Wx_6d11c.
Proof. vm_refl. Qed.
Lemma Dx_6d11c : decode_any Wx_6d11c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d120 : bv 32 := 0x0fd160ef.
Lemma Fx_6d120 : fetch_word Asan.M.loaded_segments (0x6d170 : word) = Some Wx_6d120.
Proof. vm_refl. Qed.
Lemma Dx_6d120 : decode_any Wx_6d120 = Some (Jal 1 92412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d124 : bv 32 := 0x00050b13.
Lemma Fx_6d124 : fetch_word Asan.M.loaded_segments (0x6d174 : word) = Some Wx_6d124.
Proof. vm_refl. Qed.
Lemma Dx_6d124 : decode_any Wx_6d124 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d128 : bv 32 := 0xb4050ee3.
Lemma Fx_6d128 : fetch_word Asan.M.loaded_segments (0x6d178 : word) = Some Wx_6d128.
Proof. vm_refl. Qed.
Lemma Dx_6d128 : decode_any Wx_6d128 = Some (Branch BC_EQ 10 0 7004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d408 : bv 32 := 0xfd010113.
Lemma Fx_6d408 : fetch_word Asan.M.loaded_segments (0x6d458 : word) = Some Wx_6d408.
Proof. vm_refl. Qed.
Lemma Dx_6d408 : decode_any Wx_6d408 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d40c : bv 32 := 0x02113423.
Lemma Fx_6d40c : fetch_word Asan.M.loaded_segments (0x6d45c : word) = Some Wx_6d40c.
Proof. vm_refl. Qed.
Lemma Dx_6d40c : decode_any Wx_6d40c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d410 : bv 32 := 0x02813023.
Lemma Fx_6d410 : fetch_word Asan.M.loaded_segments (0x6d460 : word) = Some Wx_6d410.
Proof. vm_refl. Qed.
Lemma Dx_6d410 : decode_any Wx_6d410 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d414 : bv 32 := 0x00913c23.
Lemma Fx_6d414 : fetch_word Asan.M.loaded_segments (0x6d464 : word) = Some Wx_6d414.
Proof. vm_refl. Qed.
Lemma Dx_6d414 : decode_any Wx_6d414 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d418 : bv 32 := 0x01213823.
Lemma Fx_6d418 : fetch_word Asan.M.loaded_segments (0x6d468 : word) = Some Wx_6d418.
Proof. vm_refl. Qed.
Lemma Dx_6d418 : decode_any Wx_6d418 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d41c : bv 32 := 0x00060413.
Lemma Fx_6d41c : fetch_word Asan.M.loaded_segments (0x6d46c : word) = Some Wx_6d41c.
Proof. vm_refl. Qed.
Lemma Dx_6d41c : decode_any Wx_6d41c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d420 : bv 32 := 0x00058493.
Lemma Fx_6d420 : fetch_word Asan.M.loaded_segments (0x6d470 : word) = Some Wx_6d420.
Proof. vm_refl. Qed.
Lemma Dx_6d420 : decode_any Wx_6d420 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d424 : bv 32 := 0x00050913.
Lemma Fx_6d424 : fetch_word Asan.M.loaded_segments (0x6d474 : word) = Some Wx_6d424.
Proof. vm_refl. Qed.
Lemma Dx_6d424 : decode_any Wx_6d424 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d428 : bv 32 := 0x3081b0ef.
Lemma Fx_6d428 : fetch_word Asan.M.loaded_segments (0x6d478 : word) = Some Wx_6d428.
Proof. vm_refl. Qed.
Lemma Dx_6d428 : decode_any Wx_6d428 = Some (Jal 1 111368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d42c : bv 32 := 0x04050863.
Lemma Fx_6d42c : fetch_word Asan.M.loaded_segments (0x6d47c : word) = Some Wx_6d42c.
Proof. vm_refl. Qed.
Lemma Dx_6d42c : decode_any Wx_6d42c = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d430 : bv 32 := 0xfffae517.
Lemma Fx_6d430 : fetch_word Asan.M.loaded_segments (0x6d480 : word) = Some Wx_6d430.
Proof. vm_refl. Qed.
Lemma Dx_6d430 : decode_any Wx_6d430 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d434 : bv 32 := 0x11f50513.
Lemma Fx_6d434 : fetch_word Asan.M.loaded_segments (0x6d484 : word) = Some Wx_6d434.
Proof. vm_refl. Qed.
Lemma Dx_6d434 : decode_any Wx_6d434 = Some (OpImm ALU_ADD 10 10 287, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d438 : bv 32 := 0x00a13423.
Lemma Fx_6d438 : fetch_word Asan.M.loaded_segments (0x6d488 : word) = Some Wx_6d438.
Proof. vm_refl. Qed.
Lemma Dx_6d438 : decode_any Wx_6d438 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d43c : bv 32 := 0x2041c0ef.
Lemma Fx_6d43c : fetch_word Asan.M.loaded_segments (0x6d48c : word) = Some Wx_6d43c.
Proof. vm_refl. Qed.
Lemma Dx_6d43c : decode_any Wx_6d43c = Some (Jal 1 115204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d440 : bv 32 := 0x000f5597.
Lemma Fx_6d440 : fetch_word Asan.M.loaded_segments (0x6d490 : word) = Some Wx_6d440.
Proof. vm_refl. Qed.
Lemma Dx_6d440 : decode_any Wx_6d440 = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d444 : bv 32 := 0x5e85b303.
Lemma Fx_6d444 : fetch_word Asan.M.loaded_segments (0x6d494 : word) = Some Wx_6d444.
Proof. vm_refl. Qed.
Lemma Dx_6d444 : decode_any Wx_6d444 = Some (Load SZ8 true 6 11 1512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d448 : bv 32 := 0x04050c63.
Lemma Fx_6d448 : fetch_word Asan.M.loaded_segments (0x6d498 : word) = Some Wx_6d448.
Proof. vm_refl. Qed.
Lemma Dx_6d448 : decode_any Wx_6d448 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d44c : bv 32 := 0x00810513.
Lemma Fx_6d44c : fetch_word Asan.M.loaded_segments (0x6d49c : word) = Some Wx_6d44c.
Proof. vm_refl. Qed.
Lemma Dx_6d44c : decode_any Wx_6d44c = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d450 : bv 32 := 0x00030593.
Lemma Fx_6d450 : fetch_word Asan.M.loaded_segments (0x6d4a0 : word) = Some Wx_6d450.
Proof. vm_refl. Qed.
Lemma Dx_6d450 : decode_any Wx_6d450 = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d454 : bv 32 := 0x00090613.
Lemma Fx_6d454 : fetch_word Asan.M.loaded_segments (0x6d4a4 : word) = Some Wx_6d454.
Proof. vm_refl. Qed.
Lemma Dx_6d454 : decode_any Wx_6d454 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d458 : bv 32 := 0x00048693.
Lemma Fx_6d458 : fetch_word Asan.M.loaded_segments (0x6d4a8 : word) = Some Wx_6d458.
Proof. vm_refl. Qed.
Lemma Dx_6d458 : decode_any Wx_6d458 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d45c : bv 32 := 0x00040713.
Lemma Fx_6d45c : fetch_word Asan.M.loaded_segments (0x6d4ac : word) = Some Wx_6d45c.
Proof. vm_refl. Qed.
Lemma Dx_6d45c : decode_any Wx_6d45c = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d460 : bv 32 := 0xf14ff0ef.
Lemma Fx_6d460 : fetch_word Asan.M.loaded_segments (0x6d4b0 : word) = Some Wx_6d460.
Proof. vm_refl. Qed.
Lemma Dx_6d460 : decode_any Wx_6d460 = Some (Jal 1 2094868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d464 : bv 32 := 0x02813083.
Lemma Fx_6d464 : fetch_word Asan.M.loaded_segments (0x6d4b4 : word) = Some Wx_6d464.
Proof. vm_refl. Qed.
Lemma Dx_6d464 : decode_any Wx_6d464 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d468 : bv 32 := 0x02013403.
Lemma Fx_6d468 : fetch_word Asan.M.loaded_segments (0x6d4b8 : word) = Some Wx_6d468.
Proof. vm_refl. Qed.
Lemma Dx_6d468 : decode_any Wx_6d468 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d46c : bv 32 := 0x01813483.
Lemma Fx_6d46c : fetch_word Asan.M.loaded_segments (0x6d4bc : word) = Some Wx_6d46c.
Proof. vm_refl. Qed.
Lemma Dx_6d46c : decode_any Wx_6d46c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d470 : bv 32 := 0x01013903.
Lemma Fx_6d470 : fetch_word Asan.M.loaded_segments (0x6d4c0 : word) = Some Wx_6d470.
Proof. vm_refl. Qed.
Lemma Dx_6d470 : decode_any Wx_6d470 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d474 : bv 32 := 0x03010113.
Lemma Fx_6d474 : fetch_word Asan.M.loaded_segments (0x6d4c4 : word) = Some Wx_6d474.
Proof. vm_refl. Qed.
Lemma Dx_6d474 : decode_any Wx_6d474 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d478 : bv 32 := 0x00008067.
Lemma Fx_6d478 : fetch_word Asan.M.loaded_segments (0x6d4c8 : word) = Some Wx_6d478.
Proof. vm_refl. Qed.
Lemma Dx_6d478 : decode_any Wx_6d478 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4c4 : bv 32 := 0xfd010113.
Lemma Fx_6d4c4 : fetch_word Asan.M.loaded_segments (0x6d514 : word) = Some Wx_6d4c4.
Proof. vm_refl. Qed.
Lemma Dx_6d4c4 : decode_any Wx_6d4c4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4c8 : bv 32 := 0x02113423.
Lemma Fx_6d4c8 : fetch_word Asan.M.loaded_segments (0x6d518 : word) = Some Wx_6d4c8.
Proof. vm_refl. Qed.
Lemma Dx_6d4c8 : decode_any Wx_6d4c8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4cc : bv 32 := 0x02813023.
Lemma Fx_6d4cc : fetch_word Asan.M.loaded_segments (0x6d51c : word) = Some Wx_6d4cc.
Proof. vm_refl. Qed.
Lemma Dx_6d4cc : decode_any Wx_6d4cc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4d0 : bv 32 := 0x00913c23.
Lemma Fx_6d4d0 : fetch_word Asan.M.loaded_segments (0x6d520 : word) = Some Wx_6d4d0.
Proof. vm_refl. Qed.
Lemma Dx_6d4d0 : decode_any Wx_6d4d0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4d4 : bv 32 := 0x01213823.
Lemma Fx_6d4d4 : fetch_word Asan.M.loaded_segments (0x6d524 : word) = Some Wx_6d4d4.
Proof. vm_refl. Qed.
Lemma Dx_6d4d4 : decode_any Wx_6d4d4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4d8 : bv 32 := 0x00060413.
Lemma Fx_6d4d8 : fetch_word Asan.M.loaded_segments (0x6d528 : word) = Some Wx_6d4d8.
Proof. vm_refl. Qed.
Lemma Dx_6d4d8 : decode_any Wx_6d4d8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4dc : bv 32 := 0x00058493.
Lemma Fx_6d4dc : fetch_word Asan.M.loaded_segments (0x6d52c : word) = Some Wx_6d4dc.
Proof. vm_refl. Qed.
Lemma Dx_6d4dc : decode_any Wx_6d4dc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4e0 : bv 32 := 0x00050913.
Lemma Fx_6d4e0 : fetch_word Asan.M.loaded_segments (0x6d530 : word) = Some Wx_6d4e0.
Proof. vm_refl. Qed.
Lemma Dx_6d4e0 : decode_any Wx_6d4e0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4e4 : bv 32 := 0x24c1b0ef.
Lemma Fx_6d4e4 : fetch_word Asan.M.loaded_segments (0x6d534 : word) = Some Wx_6d4e4.
Proof. vm_refl. Qed.
Lemma Dx_6d4e4 : decode_any Wx_6d4e4 = Some (Jal 1 111180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4e8 : bv 32 := 0x04050863.
Lemma Fx_6d4e8 : fetch_word Asan.M.loaded_segments (0x6d538 : word) = Some Wx_6d4e8.
Proof. vm_refl. Qed.
Lemma Dx_6d4e8 : decode_any Wx_6d4e8 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4ec : bv 32 := 0xfffa9517.
Lemma Fx_6d4ec : fetch_word Asan.M.loaded_segments (0x6d53c : word) = Some Wx_6d4ec.
Proof. vm_refl. Qed.
Lemma Dx_6d4ec : decode_any Wx_6d4ec = Some (Auipc 10 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4f0 : bv 32 := 0xbc350513.
Lemma Fx_6d4f0 : fetch_word Asan.M.loaded_segments (0x6d540 : word) = Some Wx_6d4f0.
Proof. vm_refl. Qed.
Lemma Dx_6d4f0 : decode_any Wx_6d4f0 = Some (OpImm ALU_ADD 10 10 3011, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4f4 : bv 32 := 0x00a13423.
Lemma Fx_6d4f4 : fetch_word Asan.M.loaded_segments (0x6d544 : word) = Some Wx_6d4f4.
Proof. vm_refl. Qed.
Lemma Dx_6d4f4 : decode_any Wx_6d4f4 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4f8 : bv 32 := 0x1481c0ef.
Lemma Fx_6d4f8 : fetch_word Asan.M.loaded_segments (0x6d548 : word) = Some Wx_6d4f8.
Proof. vm_refl. Qed.
Lemma Dx_6d4f8 : decode_any Wx_6d4f8 = Some (Jal 1 115016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4fc : bv 32 := 0x000f5597.
Lemma Fx_6d4fc : fetch_word Asan.M.loaded_segments (0x6d54c : word) = Some Wx_6d4fc.
Proof. vm_refl. Qed.
Lemma Dx_6d4fc : decode_any Wx_6d4fc = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d500 : bv 32 := 0x5345b303.
Lemma Fx_6d500 : fetch_word Asan.M.loaded_segments (0x6d550 : word) = Some Wx_6d500.
Proof. vm_refl. Qed.
Lemma Dx_6d500 : decode_any Wx_6d500 = Some (Load SZ8 true 6 11 1332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d504 : bv 32 := 0x04050c63.
Lemma Fx_6d504 : fetch_word Asan.M.loaded_segments (0x6d554 : word) = Some Wx_6d504.
Proof. vm_refl. Qed.
Lemma Dx_6d504 : decode_any Wx_6d504 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d508 : bv 32 := 0x00810513.
Lemma Fx_6d508 : fetch_word Asan.M.loaded_segments (0x6d558 : word) = Some Wx_6d508.
Proof. vm_refl. Qed.
Lemma Dx_6d508 : decode_any Wx_6d508 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d50c : bv 32 := 0x00030593.
Lemma Fx_6d50c : fetch_word Asan.M.loaded_segments (0x6d55c : word) = Some Wx_6d50c.
Proof. vm_refl. Qed.
Lemma Dx_6d50c : decode_any Wx_6d50c = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d510 : bv 32 := 0x00090613.
Lemma Fx_6d510 : fetch_word Asan.M.loaded_segments (0x6d560 : word) = Some Wx_6d510.
Proof. vm_refl. Qed.
Lemma Dx_6d510 : decode_any Wx_6d510 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d514 : bv 32 := 0x00048693.
Lemma Fx_6d514 : fetch_word Asan.M.loaded_segments (0x6d564 : word) = Some Wx_6d514.
Proof. vm_refl. Qed.
Lemma Dx_6d514 : decode_any Wx_6d514 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d518 : bv 32 := 0x00040713.
Lemma Fx_6d518 : fetch_word Asan.M.loaded_segments (0x6d568 : word) = Some Wx_6d518.
Proof. vm_refl. Qed.
Lemma Dx_6d518 : decode_any Wx_6d518 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d51c : bv 32 := 0xe58ff0ef.
Lemma Fx_6d51c : fetch_word Asan.M.loaded_segments (0x6d56c : word) = Some Wx_6d51c.
Proof. vm_refl. Qed.
Lemma Dx_6d51c : decode_any Wx_6d51c = Some (Jal 1 2094680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d520 : bv 32 := 0x02813083.
Lemma Fx_6d520 : fetch_word Asan.M.loaded_segments (0x6d570 : word) = Some Wx_6d520.
Proof. vm_refl. Qed.
Lemma Dx_6d520 : decode_any Wx_6d520 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d524 : bv 32 := 0x02013403.
Lemma Fx_6d524 : fetch_word Asan.M.loaded_segments (0x6d574 : word) = Some Wx_6d524.
Proof. vm_refl. Qed.
Lemma Dx_6d524 : decode_any Wx_6d524 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d528 : bv 32 := 0x01813483.
Lemma Fx_6d528 : fetch_word Asan.M.loaded_segments (0x6d578 : word) = Some Wx_6d528.
Proof. vm_refl. Qed.
Lemma Dx_6d528 : decode_any Wx_6d528 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d52c : bv 32 := 0x01013903.
Lemma Fx_6d52c : fetch_word Asan.M.loaded_segments (0x6d57c : word) = Some Wx_6d52c.
Proof. vm_refl. Qed.
Lemma Dx_6d52c : decode_any Wx_6d52c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d530 : bv 32 := 0x03010113.
Lemma Fx_6d530 : fetch_word Asan.M.loaded_segments (0x6d580 : word) = Some Wx_6d530.
Proof. vm_refl. Qed.
Lemma Dx_6d530 : decode_any Wx_6d530 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d534 : bv 32 := 0x00008067.
Lemma Fx_6d534 : fetch_word Asan.M.loaded_segments (0x6d584 : word) = Some Wx_6d534.
Proof. vm_refl. Qed.
Lemma Dx_6d534 : decode_any Wx_6d534 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_88730 : bv 32 := 0x000e2517.
Lemma Fx_88730 : fetch_word Asan.M.loaded_segments (0x88780 : word) = Some Wx_88730.
Proof. vm_refl. Qed.
Lemma Dx_88730 : decode_any Wx_88730 = Some (Auipc 10 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_88734 : bv 32 := 0x45850503.
Lemma Fx_88734 : fetch_word Asan.M.loaded_segments (0x88784 : word) = Some Wx_88734.
Proof. vm_refl. Qed.
Lemma Dx_88734 : decode_any Wx_88734 = Some (Load SZ1 true 10 10 1112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_88738 : bv 32 := 0x0230000f.
Lemma Fx_88738 : fetch_word Asan.M.loaded_segments (0x88788 : word) = Some Wx_88738.
Proof. vm_refl. Qed.
Lemma Dx_88738 : decode_any Wx_88738 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8873c : bv 32 := 0xfff50513.
Lemma Fx_8873c : fetch_word Asan.M.loaded_segments (0x8878c : word) = Some Wx_8873c.
Proof. vm_refl. Qed.
Lemma Dx_8873c : decode_any Wx_8873c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_88740 : bv 32 := 0x00153513.
Lemma Fx_88740 : fetch_word Asan.M.loaded_segments (0x88790 : word) = Some Wx_88740.
Proof. vm_refl. Qed.
Lemma Dx_88740 : decode_any Wx_88740 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_88744 : bv 32 := 0x00008067.
Lemma Fx_88744 : fetch_word Asan.M.loaded_segments (0x88794 : word) = Some Wx_88744.
Proof. vm_refl. Qed.
Lemma Dx_88744 : decode_any Wx_88744 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

