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
Definition Wx_801e4 : bv 32 := 0x2590006f.
Lemma Fx_801e4 : fetch_word Asan.M.loaded_segments (0x80234 : word) = Some Wx_801e4.
Proof. vm_refl. Qed.
Lemma Dx_801e4 : decode_any Wx_801e4 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c3c : bv 32 := 0x81010113.
Lemma Fx_80c3c : fetch_word Asan.M.loaded_segments (0x80c8c : word) = Some Wx_80c3c.
Proof. vm_refl. Qed.
Lemma Dx_80c3c : decode_any Wx_80c3c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c40 : bv 32 := 0x7e113423.
Lemma Fx_80c40 : fetch_word Asan.M.loaded_segments (0x80c90 : word) = Some Wx_80c40.
Proof. vm_refl. Qed.
Lemma Dx_80c40 : decode_any Wx_80c40 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c44 : bv 32 := 0x7e813023.
Lemma Fx_80c44 : fetch_word Asan.M.loaded_segments (0x80c94 : word) = Some Wx_80c44.
Proof. vm_refl. Qed.
Lemma Dx_80c44 : decode_any Wx_80c44 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c48 : bv 32 := 0x7c913c23.
Lemma Fx_80c48 : fetch_word Asan.M.loaded_segments (0x80c98 : word) = Some Wx_80c48.
Proof. vm_refl. Qed.
Lemma Dx_80c48 : decode_any Wx_80c48 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c4c : bv 32 := 0x7d213823.
Lemma Fx_80c4c : fetch_word Asan.M.loaded_segments (0x80c9c : word) = Some Wx_80c4c.
Proof. vm_refl. Qed.
Lemma Dx_80c4c : decode_any Wx_80c4c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c50 : bv 32 := 0x7d313423.
Lemma Fx_80c50 : fetch_word Asan.M.loaded_segments (0x80ca0 : word) = Some Wx_80c50.
Proof. vm_refl. Qed.
Lemma Dx_80c50 : decode_any Wx_80c50 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c54 : bv 32 := 0x7d413023.
Lemma Fx_80c54 : fetch_word Asan.M.loaded_segments (0x80ca4 : word) = Some Wx_80c54.
Proof. vm_refl. Qed.
Lemma Dx_80c54 : decode_any Wx_80c54 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c58 : bv 32 := 0x7b513c23.
Lemma Fx_80c58 : fetch_word Asan.M.loaded_segments (0x80ca8 : word) = Some Wx_80c58.
Proof. vm_refl. Qed.
Lemma Dx_80c58 : decode_any Wx_80c58 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c5c : bv 32 := 0x7b613823.
Lemma Fx_80c5c : fetch_word Asan.M.loaded_segments (0x80cac : word) = Some Wx_80c5c.
Proof. vm_refl. Qed.
Lemma Dx_80c5c : decode_any Wx_80c5c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c60 : bv 32 := 0x7f010413.
Lemma Fx_80c60 : fetch_word Asan.M.loaded_segments (0x80cb0 : word) = Some Wx_80c60.
Proof. vm_refl. Qed.
Lemma Dx_80c60 : decode_any Wx_80c60 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c64 : bv 32 := 0xf9010113.
Lemma Fx_80c64 : fetch_word Asan.M.loaded_segments (0x80cb4 : word) = Some Wx_80c64.
Proof. vm_refl. Qed.
Lemma Dx_80c64 : decode_any Wx_80c64 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c68 : bv 32 := 0x000e1697.
Lemma Fx_80c68 : fetch_word Asan.M.loaded_segments (0x80cb8 : word) = Some Wx_80c68.
Proof. vm_refl. Qed.
Lemma Dx_80c68 : decode_any Wx_80c68 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c6c : bv 32 := 0xac86b683.
Lemma Fx_80c6c : fetch_word Asan.M.loaded_segments (0x80cbc : word) = Some Wx_80c6c.
Proof. vm_refl. Qed.
Lemma Dx_80c6c : decode_any Wx_80c6c = Some (Load SZ8 true 13 13 2760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c70 : bv 32 := 0x0006c683.
Lemma Fx_80c70 : fetch_word Asan.M.loaded_segments (0x80cc0 : word) = Some Wx_80c70.
Proof. vm_refl. Qed.
Lemma Dx_80c70 : decode_any Wx_80c70 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c74 : bv 32 := 0x08068a63.
Lemma Fx_80c74 : fetch_word Asan.M.loaded_segments (0x80cc4 : word) = Some Wx_80c74.
Proof. vm_refl. Qed.
Lemma Dx_80c74 : decode_any Wx_80c74 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c78 : bv 32 := 0xfff54693.
Lemma Fx_80c78 : fetch_word Asan.M.loaded_segments (0x80cc8 : word) = Some Wx_80c78.
Proof. vm_refl. Qed.
Lemma Dx_80c78 : decode_any Wx_80c78 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c7c : bv 32 := 0x80040a93.
Lemma Fx_80c7c : fetch_word Asan.M.loaded_segments (0x80ccc : word) = Some Wx_80c7c.
Proof. vm_refl. Qed.
Lemma Dx_80c7c : decode_any Wx_80c7c = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c80 : bv 32 := 0xfa8a8a93.
Lemma Fx_80c80 : fetch_word Asan.M.loaded_segments (0x80cd0 : word) = Some Wx_80c80.
Proof. vm_refl. Qed.
Lemma Dx_80c80 : decode_any Wx_80c80 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c84 : bv 32 := 0x0cc6ea63.
Lemma Fx_80c84 : fetch_word Asan.M.loaded_segments (0x80cd4 : word) = Some Wx_80c84.
Proof. vm_refl. Qed.
Lemma Dx_80c84 : decode_any Wx_80c84 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c88 : bv 32 := 0xfbf60693.
Lemma Fx_80c88 : fetch_word Asan.M.loaded_segments (0x80cd8 : word) = Some Wx_80c88.
Proof. vm_refl. Qed.
Lemma Dx_80c88 : decode_any Wx_80c88 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c8c : bv 32 := 0xfbf00713.
Lemma Fx_80c8c : fetch_word Asan.M.loaded_segments (0x80cdc : word) = Some Wx_80c8c.
Proof. vm_refl. Qed.
Lemma Dx_80c8c : decode_any Wx_80c8c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c90 : bv 32 := 0x14d77863.
Lemma Fx_80c90 : fetch_word Asan.M.loaded_segments (0x80ce0 : word) = Some Wx_80c90.
Proof. vm_refl. Qed.
Lemma Dx_80c90 : decode_any Wx_80c90 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c94 : bv 32 := 0x000e0697.
Lemma Fx_80c94 : fetch_word Asan.M.loaded_segments (0x80ce4 : word) = Some Wx_80c94.
Proof. vm_refl. Qed.
Lemma Dx_80c94 : decode_any Wx_80c94 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c98 : bv 32 := 0xf346b683.
Lemma Fx_80c98 : fetch_word Asan.M.loaded_segments (0x80ce8 : word) = Some Wx_80c98.
Proof. vm_refl. Qed.
Lemma Dx_80c98 : decode_any Wx_80c98 = Some (Load SZ8 true 13 13 3892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80c9c : bv 32 := 0x00c507b3.
Lemma Fx_80c9c : fetch_word Asan.M.loaded_segments (0x80cec : word) = Some Wx_80c9c.
Proof. vm_refl. Qed.
Lemma Dx_80c9c : decode_any Wx_80c9c = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ca0 : bv 32 := 0x0006b703.
Lemma Fx_80ca0 : fetch_word Asan.M.loaded_segments (0x80cf0 : word) = Some Wx_80ca0.
Proof. vm_refl. Qed.
Lemma Dx_80ca0 : decode_any Wx_80ca0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ca4 : bv 32 := 0x00355693.
Lemma Fx_80ca4 : fetch_word Asan.M.loaded_segments (0x80cf4 : word) = Some Wx_80ca4.
Proof. vm_refl. Qed.
Lemma Dx_80ca4 : decode_any Wx_80ca4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ca8 : bv 32 := 0xfff78793.
Lemma Fx_80ca8 : fetch_word Asan.M.loaded_segments (0x80cf8 : word) = Some Wx_80ca8.
Proof. vm_refl. Qed.
Lemma Dx_80ca8 : decode_any Wx_80ca8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cac : bv 32 := 0x0037d813.
Lemma Fx_80cac : fetch_word Asan.M.loaded_segments (0x80cfc : word) = Some Wx_80cac.
Proof. vm_refl. Qed.
Lemma Dx_80cac : decode_any Wx_80cac = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cb0 : bv 32 := 0x00d706b3.
Lemma Fx_80cb0 : fetch_word Asan.M.loaded_segments (0x80d00 : word) = Some Wx_80cb0.
Proof. vm_refl. Qed.
Lemma Dx_80cb0 : decode_any Wx_80cb0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cb4 : bv 32 := 0x01070733.
Lemma Fx_80cb4 : fetch_word Asan.M.loaded_segments (0x80d04 : word) = Some Wx_80cb4.
Proof. vm_refl. Qed.
Lemma Dx_80cb4 : decode_any Wx_80cb4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cb8 : bv 32 := 0xff86f813.
Lemma Fx_80cb8 : fetch_word Asan.M.loaded_segments (0x80d08 : word) = Some Wx_80cb8.
Proof. vm_refl. Qed.
Lemma Dx_80cb8 : decode_any Wx_80cb8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cbc : bv 32 := 0xff877893.
Lemma Fx_80cbc : fetch_word Asan.M.loaded_segments (0x80d0c : word) = Some Wx_80cbc.
Proof. vm_refl. Qed.
Lemma Dx_80cbc : decode_any Wx_80cbc = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cc0 : bv 32 := 0x00083803.
Lemma Fx_80cc0 : fetch_word Asan.M.loaded_segments (0x80d10 : word) = Some Wx_80cc0.
Proof. vm_refl. Qed.
Lemma Dx_80cc0 : decode_any Wx_80cc0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cc4 : bv 32 := 0x0008b883.
Lemma Fx_80cc4 : fetch_word Asan.M.loaded_segments (0x80d14 : word) = Some Wx_80cc4.
Proof. vm_refl. Qed.
Lemma Dx_80cc4 : decode_any Wx_80cc4 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cc8 : bv 32 := 0x0108e833.
Lemma Fx_80cc8 : fetch_word Asan.M.loaded_segments (0x80d18 : word) = Some Wx_80cc8.
Proof. vm_refl. Qed.
Lemma Dx_80cc8 : decode_any Wx_80cc8 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ccc : bv 32 := 0x10081e63.
Lemma Fx_80ccc : fetch_word Asan.M.loaded_segments (0x80d1c : word) = Some Wx_80ccc.
Proof. vm_refl. Qed.
Lemma Dx_80ccc : decode_any Wx_80ccc = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cd0 : bv 32 := 0x000e2697.
Lemma Fx_80cd0 : fetch_word Asan.M.loaded_segments (0x80d20 : word) = Some Wx_80cd0.
Proof. vm_refl. Qed.
Lemma Dx_80cd0 : decode_any Wx_80cd0 = Some (Auipc 13 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cd4 : bv 32 := 0xf306b683.
Lemma Fx_80cd4 : fetch_word Asan.M.loaded_segments (0x80d24 : word) = Some Wx_80cd4.
Proof. vm_refl. Qed.
Lemma Dx_80cd4 : decode_any Wx_80cd4 = Some (Load SZ8 true 13 13 3888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cd8 : bv 32 := 0x000680e7.
Lemma Fx_80cd8 : fetch_word Asan.M.loaded_segments (0x80d28 : word) = Some Wx_80cd8.
Proof. vm_refl. Qed.
Lemma Dx_80cd8 : decode_any Wx_80cd8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cdc : bv 32 := 0x07010113.
Lemma Fx_80cdc : fetch_word Asan.M.loaded_segments (0x80d2c : word) = Some Wx_80cdc.
Proof. vm_refl. Qed.
Lemma Dx_80cdc : decode_any Wx_80cdc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ce0 : bv 32 := 0x7e813083.
Lemma Fx_80ce0 : fetch_word Asan.M.loaded_segments (0x80d30 : word) = Some Wx_80ce0.
Proof. vm_refl. Qed.
Lemma Dx_80ce0 : decode_any Wx_80ce0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ce4 : bv 32 := 0x7e013403.
Lemma Fx_80ce4 : fetch_word Asan.M.loaded_segments (0x80d34 : word) = Some Wx_80ce4.
Proof. vm_refl. Qed.
Lemma Dx_80ce4 : decode_any Wx_80ce4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80ce8 : bv 32 := 0x7d813483.
Lemma Fx_80ce8 : fetch_word Asan.M.loaded_segments (0x80d38 : word) = Some Wx_80ce8.
Proof. vm_refl. Qed.
Lemma Dx_80ce8 : decode_any Wx_80ce8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cec : bv 32 := 0x7d013903.
Lemma Fx_80cec : fetch_word Asan.M.loaded_segments (0x80d3c : word) = Some Wx_80cec.
Proof. vm_refl. Qed.
Lemma Dx_80cec : decode_any Wx_80cec = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cf0 : bv 32 := 0x7c813983.
Lemma Fx_80cf0 : fetch_word Asan.M.loaded_segments (0x80d40 : word) = Some Wx_80cf0.
Proof. vm_refl. Qed.
Lemma Dx_80cf0 : decode_any Wx_80cf0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cf4 : bv 32 := 0x7c013a03.
Lemma Fx_80cf4 : fetch_word Asan.M.loaded_segments (0x80d44 : word) = Some Wx_80cf4.
Proof. vm_refl. Qed.
Lemma Dx_80cf4 : decode_any Wx_80cf4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cf8 : bv 32 := 0x7b813a83.
Lemma Fx_80cf8 : fetch_word Asan.M.loaded_segments (0x80d48 : word) = Some Wx_80cf8.
Proof. vm_refl. Qed.
Lemma Dx_80cf8 : decode_any Wx_80cf8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80cfc : bv 32 := 0x7b013b03.
Lemma Fx_80cfc : fetch_word Asan.M.loaded_segments (0x80d4c : word) = Some Wx_80cfc.
Proof. vm_refl. Qed.
Lemma Dx_80cfc : decode_any Wx_80cfc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80d00 : bv 32 := 0x7f010113.
Lemma Fx_80d00 : fetch_word Asan.M.loaded_segments (0x80d50 : word) = Some Wx_80d00.
Proof. vm_refl. Qed.
Lemma Dx_80d00 : decode_any Wx_80d00 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80d04 : bv 32 := 0x00008067.
Lemma Fx_80d04 : fetch_word Asan.M.loaded_segments (0x80d54 : word) = Some Wx_80d04.
Proof. vm_refl. Qed.
Lemma Dx_80d04 : decode_any Wx_80d04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80de0 : bv 32 := 0x02061e63.
Lemma Fx_80de0 : fetch_word Asan.M.loaded_segments (0x80e30 : word) = Some Wx_80de0.
Proof. vm_refl. Qed.
Lemma Dx_80de0 : decode_any Wx_80de0 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80de4 : bv 32 := 0xeedff06f.
Lemma Fx_80de4 : fetch_word Asan.M.loaded_segments (0x80e34 : word) = Some Wx_80de4.
Proof. vm_refl. Qed.
Lemma Dx_80de4 : decode_any Wx_80de4 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80de8 : bv 32 := 0x00070803.
Lemma Fx_80de8 : fetch_word Asan.M.loaded_segments (0x80e38 : word) = Some Wx_80de8.
Proof. vm_refl. Qed.
Lemma Dx_80de8 : decode_any Wx_80de8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80dec : bv 32 := 0x0077f793.
Lemma Fx_80dec : fetch_word Asan.M.loaded_segments (0x80e3c : word) = Some Wx_80dec.
Proof. vm_refl. Qed.
Lemma Dx_80dec : decode_any Wx_80dec = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80df0 : bv 32 := 0x010038b3.
Lemma Fx_80df0 : fetch_word Asan.M.loaded_segments (0x80e40 : word) = Some Wx_80df0.
Proof. vm_refl. Qed.
Lemma Dx_80df0 : decode_any Wx_80df0 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80df4 : bv 32 := 0x0107a7b3.
Lemma Fx_80df4 : fetch_word Asan.M.loaded_segments (0x80e44 : word) = Some Wx_80df4.
Proof. vm_refl. Qed.
Lemma Dx_80df4 : decode_any Wx_80df4 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80df8 : bv 32 := 0x0017c793.
Lemma Fx_80df8 : fetch_word Asan.M.loaded_segments (0x80e48 : word) = Some Wx_80df8.
Proof. vm_refl. Qed.
Lemma Dx_80df8 : decode_any Wx_80df8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80dfc : bv 32 := 0x00f8f7b3.
Lemma Fx_80dfc : fetch_word Asan.M.loaded_segments (0x80e4c : word) = Some Wx_80dfc.
Proof. vm_refl. Qed.
Lemma Dx_80dfc : decode_any Wx_80dfc = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e00 : bv 32 := 0x00e6fa63.
Lemma Fx_80e00 : fetch_word Asan.M.loaded_segments (0x80e50 : word) = Some Wx_80e00.
Proof. vm_refl. Qed.
Lemma Dx_80e00 : decode_any Wx_80e00 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e04 : bv 32 := 0x0006c803.
Lemma Fx_80e04 : fetch_word Asan.M.loaded_segments (0x80e54 : word) = Some Wx_80e04.
Proof. vm_refl. Qed.
Lemma Dx_80e04 : decode_any Wx_80e04 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e08 : bv 32 := 0x00168693.
Lemma Fx_80e08 : fetch_word Asan.M.loaded_segments (0x80e58 : word) = Some Wx_80e08.
Proof. vm_refl. Qed.
Lemma Dx_80e08 : decode_any Wx_80e08 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e0c : bv 32 := 0x00f867b3.
Lemma Fx_80e0c : fetch_word Asan.M.loaded_segments (0x80e5c : word) = Some Wx_80e0c.
Proof. vm_refl. Qed.
Lemma Dx_80e0c : decode_any Wx_80e0c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e10 : bv 32 := 0xfee69ae3.
Lemma Fx_80e10 : fetch_word Asan.M.loaded_segments (0x80e60 : word) = Some Wx_80e10.
Proof. vm_refl. Qed.
Lemma Dx_80e10 : decode_any Wx_80e10 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e14 : bv 32 := 0x0ff7f693.
Lemma Fx_80e14 : fetch_word Asan.M.loaded_segments (0x80e64 : word) = Some Wx_80e14.
Proof. vm_refl. Qed.
Lemma Dx_80e14 : decode_any Wx_80e14 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e18 : bv 32 := 0xea068ce3.
Lemma Fx_80e18 : fetch_word Asan.M.loaded_segments (0x80e68 : word) = Some Wx_80e18.
Proof. vm_refl. Qed.
Lemma Dx_80e18 : decode_any Wx_80e18 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e1c : bv 32 := 0x00050493.
Lemma Fx_80e1c : fetch_word Asan.M.loaded_segments (0x80e6c : word) = Some Wx_80e1c.
Proof. vm_refl. Qed.
Lemma Dx_80e1c : decode_any Wx_80e1c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e20 : bv 32 := 0x00058b13.
Lemma Fx_80e20 : fetch_word Asan.M.loaded_segments (0x80e70 : word) = Some Wx_80e20.
Proof. vm_refl. Qed.
Lemma Dx_80e20 : decode_any Wx_80e20 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e24 : bv 32 := 0x00060593.
Lemma Fx_80e24 : fetch_word Asan.M.loaded_segments (0x80e74 : word) = Some Wx_80e24.
Proof. vm_refl. Qed.
Lemma Dx_80e24 : decode_any Wx_80e24 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e28 : bv 32 := 0x00060913.
Lemma Fx_80e28 : fetch_word Asan.M.loaded_segments (0x80e78 : word) = Some Wx_80e28.
Proof. vm_refl. Qed.
Lemma Dx_80e28 : decode_any Wx_80e28 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e2c : bv 32 := 0x3f1020ef.
Lemma Fx_80e2c : fetch_word Asan.M.loaded_segments (0x80e7c : word) = Some Wx_80e2c.
Proof. vm_refl. Qed.
Lemma Dx_80e2c : decode_any Wx_80e2c = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e30 : bv 32 := 0x000b0593.
Lemma Fx_80e30 : fetch_word Asan.M.loaded_segments (0x80e80 : word) = Some Wx_80e30.
Proof. vm_refl. Qed.
Lemma Dx_80e30 : decode_any Wx_80e30 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e34 : bv 32 := 0x00090613.
Lemma Fx_80e34 : fetch_word Asan.M.loaded_segments (0x80e84 : word) = Some Wx_80e34.
Proof. vm_refl. Qed.
Lemma Dx_80e34 : decode_any Wx_80e34 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e38 : bv 32 := 0x00050993.
Lemma Fx_80e38 : fetch_word Asan.M.loaded_segments (0x80e88 : word) = Some Wx_80e38.
Proof. vm_refl. Qed.
Lemma Dx_80e38 : decode_any Wx_80e38 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e3c : bv 32 := 0x00048513.
Lemma Fx_80e3c : fetch_word Asan.M.loaded_segments (0x80e8c : word) = Some Wx_80e3c.
Proof. vm_refl. Qed.
Lemma Dx_80e3c : decode_any Wx_80e3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_80e40 : bv 32 := 0xe80988e3.
Lemma Fx_80e40 : fetch_word Asan.M.loaded_segments (0x80e90 : word) = Some Wx_80e40.
Proof. vm_refl. Qed.
Lemma Dx_80e40 : decode_any Wx_80e40 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

