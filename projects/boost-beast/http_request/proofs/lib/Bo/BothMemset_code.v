(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_111eb8 : bv 32 := 0x0e060a63.
Lemma F_111eb8 : fetch_word AsanUbsan.M.loaded_segments (0x111eb8 : word) = Some W_111eb8.
Proof. vm_refl. Qed.
Lemma D_111eb8 : decode_any W_111eb8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ebc : bv 32 := 0x00b50023.
Lemma F_111ebc : fetch_word AsanUbsan.M.loaded_segments (0x111ebc : word) = Some W_111ebc.
Proof. vm_refl. Qed.
Lemma D_111ebc : decode_any W_111ebc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ec0 : bv 32 := 0x00c506b3.
Lemma F_111ec0 : fetch_word AsanUbsan.M.loaded_segments (0x111ec0 : word) = Some W_111ec0.
Proof. vm_refl. Qed.
Lemma D_111ec0 : decode_any W_111ec0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ec4 : bv 32 := 0x00300713.
Lemma F_111ec4 : fetch_word AsanUbsan.M.loaded_segments (0x111ec4 : word) = Some W_111ec4.
Proof. vm_refl. Qed.
Lemma D_111ec4 : decode_any W_111ec4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ec8 : bv 32 := 0xfeb68fa3.
Lemma F_111ec8 : fetch_word AsanUbsan.M.loaded_segments (0x111ec8 : word) = Some W_111ec8.
Proof. vm_refl. Qed.
Lemma D_111ec8 : decode_any W_111ec8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ecc : bv 32 := 0x0ee66063.
Lemma F_111ecc : fetch_word AsanUbsan.M.loaded_segments (0x111ecc : word) = Some W_111ecc.
Proof. vm_refl. Qed.
Lemma D_111ecc : decode_any W_111ecc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ed0 : bv 32 := 0x00b500a3.
Lemma F_111ed0 : fetch_word AsanUbsan.M.loaded_segments (0x111ed0 : word) = Some W_111ed0.
Proof. vm_refl. Qed.
Lemma D_111ed0 : decode_any W_111ed0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ed4 : bv 32 := 0x00b50123.
Lemma F_111ed4 : fetch_word AsanUbsan.M.loaded_segments (0x111ed4 : word) = Some W_111ed4.
Proof. vm_refl. Qed.
Lemma D_111ed4 : decode_any W_111ed4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ed8 : bv 32 := 0x00700713.
Lemma F_111ed8 : fetch_word AsanUbsan.M.loaded_segments (0x111ed8 : word) = Some W_111ed8.
Proof. vm_refl. Qed.
Lemma D_111ed8 : decode_any W_111ed8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111edc : bv 32 := 0xfeb68ea3.
Lemma F_111edc : fetch_word AsanUbsan.M.loaded_segments (0x111edc : word) = Some W_111edc.
Proof. vm_refl. Qed.
Lemma D_111edc : decode_any W_111edc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ee0 : bv 32 := 0xfeb68f23.
Lemma F_111ee0 : fetch_word AsanUbsan.M.loaded_segments (0x111ee0 : word) = Some W_111ee0.
Proof. vm_refl. Qed.
Lemma D_111ee0 : decode_any W_111ee0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ee4 : bv 32 := 0x0ce66463.
Lemma F_111ee4 : fetch_word AsanUbsan.M.loaded_segments (0x111ee4 : word) = Some W_111ee4.
Proof. vm_refl. Qed.
Lemma D_111ee4 : decode_any W_111ee4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ee8 : bv 32 := 0x00b501a3.
Lemma F_111ee8 : fetch_word AsanUbsan.M.loaded_segments (0x111ee8 : word) = Some W_111ee8.
Proof. vm_refl. Qed.
Lemma D_111ee8 : decode_any W_111ee8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111eec : bv 32 := 0x00900793.
Lemma F_111eec : fetch_word AsanUbsan.M.loaded_segments (0x111eec : word) = Some W_111eec.
Proof. vm_refl. Qed.
Lemma D_111eec : decode_any W_111eec = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ef0 : bv 32 := 0xfeb68e23.
Lemma F_111ef0 : fetch_word AsanUbsan.M.loaded_segments (0x111ef0 : word) = Some W_111ef0.
Proof. vm_refl. Qed.
Lemma D_111ef0 : decode_any W_111ef0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ef4 : bv 32 := 0x0af66c63.
Lemma F_111ef4 : fetch_word AsanUbsan.M.loaded_segments (0x111ef4 : word) = Some W_111ef4.
Proof. vm_refl. Qed.
Lemma D_111ef4 : decode_any W_111ef4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111ef8 : bv 32 := 0x40a006bb.
Lemma F_111ef8 : fetch_word AsanUbsan.M.loaded_segments (0x111ef8 : word) = Some W_111ef8.
Proof. vm_refl. Qed.
Lemma D_111ef8 : decode_any W_111ef8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111efc : bv 32 := 0x03859813.
Lemma F_111efc : fetch_word AsanUbsan.M.loaded_segments (0x111efc : word) = Some W_111efc.
Proof. vm_refl. Qed.
Lemma D_111efc : decode_any W_111efc = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f00 : bv 32 := 0x101015b7.
Lemma F_111f00 : fetch_word AsanUbsan.M.loaded_segments (0x111f00 : word) = Some W_111f00.
Proof. vm_refl. Qed.
Lemma D_111f00 : decode_any W_111f00 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f04 : bv 32 := 0x0036f693.
Lemma F_111f04 : fetch_word AsanUbsan.M.loaded_segments (0x111f04 : word) = Some W_111f04.
Proof. vm_refl. Qed.
Lemma D_111f04 : decode_any W_111f04 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f08 : bv 32 := 0x00459713.
Lemma F_111f08 : fetch_word AsanUbsan.M.loaded_segments (0x111f08 : word) = Some W_111f08.
Proof. vm_refl. Qed.
Lemma D_111f08 : decode_any W_111f08 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f0c : bv 32 := 0x40d60633.
Lemma F_111f0c : fetch_word AsanUbsan.M.loaded_segments (0x111f0c : word) = Some W_111f0c.
Proof. vm_refl. Qed.
Lemma D_111f0c : decode_any W_111f0c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f10 : bv 32 := 0x00d505b3.
Lemma F_111f10 : fetch_word AsanUbsan.M.loaded_segments (0x111f10 : word) = Some W_111f10.
Proof. vm_refl. Qed.
Lemma D_111f10 : decode_any W_111f10 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f14 : bv 32 := 0x10070693.
Lemma F_111f14 : fetch_word AsanUbsan.M.loaded_segments (0x111f14 : word) = Some W_111f14.
Proof. vm_refl. Qed.
Lemma D_111f14 : decode_any W_111f14 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f18 : bv 32 := 0xffc67713.
Lemma F_111f18 : fetch_word AsanUbsan.M.loaded_segments (0x111f18 : word) = Some W_111f18.
Proof. vm_refl. Qed.
Lemma D_111f18 : decode_any W_111f18 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f1c : bv 32 := 0x02d83633.
Lemma F_111f1c : fetch_word AsanUbsan.M.loaded_segments (0x111f1c : word) = Some W_111f1c.
Proof. vm_refl. Qed.
Lemma D_111f1c : decode_any W_111f1c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f20 : bv 32 := 0x00c5a023.
Lemma F_111f20 : fetch_word AsanUbsan.M.loaded_segments (0x111f20 : word) = Some W_111f20.
Proof. vm_refl. Qed.
Lemma D_111f20 : decode_any W_111f20 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f24 : bv 32 := 0x00e586b3.
Lemma F_111f24 : fetch_word AsanUbsan.M.loaded_segments (0x111f24 : word) = Some W_111f24.
Proof. vm_refl. Qed.
Lemma D_111f24 : decode_any W_111f24 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f28 : bv 32 := 0xfec6ae23.
Lemma F_111f28 : fetch_word AsanUbsan.M.loaded_segments (0x111f28 : word) = Some W_111f28.
Proof. vm_refl. Qed.
Lemma D_111f28 : decode_any W_111f28 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f2c : bv 32 := 0x08f76063.
Lemma F_111f2c : fetch_word AsanUbsan.M.loaded_segments (0x111f2c : word) = Some W_111f2c.
Proof. vm_refl. Qed.
Lemma D_111f2c : decode_any W_111f2c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f30 : bv 32 := 0x00c5a223.
Lemma F_111f30 : fetch_word AsanUbsan.M.loaded_segments (0x111f30 : word) = Some W_111f30.
Proof. vm_refl. Qed.
Lemma D_111f30 : decode_any W_111f30 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f34 : bv 32 := 0x00c5a423.
Lemma F_111f34 : fetch_word AsanUbsan.M.loaded_segments (0x111f34 : word) = Some W_111f34.
Proof. vm_refl. Qed.
Lemma D_111f34 : decode_any W_111f34 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f38 : bv 32 := 0x01900793.
Lemma F_111f38 : fetch_word AsanUbsan.M.loaded_segments (0x111f38 : word) = Some W_111f38.
Proof. vm_refl. Qed.
Lemma D_111f38 : decode_any W_111f38 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f3c : bv 32 := 0xfec6aa23.
Lemma F_111f3c : fetch_word AsanUbsan.M.loaded_segments (0x111f3c : word) = Some W_111f3c.
Proof. vm_refl. Qed.
Lemma D_111f3c : decode_any W_111f3c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f40 : bv 32 := 0xfec6ac23.
Lemma F_111f40 : fetch_word AsanUbsan.M.loaded_segments (0x111f40 : word) = Some W_111f40.
Proof. vm_refl. Qed.
Lemma D_111f40 : decode_any W_111f40 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f44 : bv 32 := 0x06f76463.
Lemma F_111f44 : fetch_word AsanUbsan.M.loaded_segments (0x111f44 : word) = Some W_111f44.
Proof. vm_refl. Qed.
Lemma D_111f44 : decode_any W_111f44 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f48 : bv 32 := 0x00c5a623.
Lemma F_111f48 : fetch_word AsanUbsan.M.loaded_segments (0x111f48 : word) = Some W_111f48.
Proof. vm_refl. Qed.
Lemma D_111f48 : decode_any W_111f48 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f4c : bv 32 := 0x00c5a823.
Lemma F_111f4c : fetch_word AsanUbsan.M.loaded_segments (0x111f4c : word) = Some W_111f4c.
Proof. vm_refl. Qed.
Lemma D_111f4c : decode_any W_111f4c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f50 : bv 32 := 0x00c5aa23.
Lemma F_111f50 : fetch_word AsanUbsan.M.loaded_segments (0x111f50 : word) = Some W_111f50.
Proof. vm_refl. Qed.
Lemma D_111f50 : decode_any W_111f50 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f54 : bv 32 := 0x00c5ac23.
Lemma F_111f54 : fetch_word AsanUbsan.M.loaded_segments (0x111f54 : word) = Some W_111f54.
Proof. vm_refl. Qed.
Lemma D_111f54 : decode_any W_111f54 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f58 : bv 32 := 0x0045f793.
Lemma F_111f58 : fetch_word AsanUbsan.M.loaded_segments (0x111f58 : word) = Some W_111f58.
Proof. vm_refl. Qed.
Lemma D_111f58 : decode_any W_111f58 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f5c : bv 32 := 0x02000813.
Lemma F_111f5c : fetch_word AsanUbsan.M.loaded_segments (0x111f5c : word) = Some W_111f5c.
Proof. vm_refl. Qed.
Lemma D_111f5c : decode_any W_111f5c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f60 : bv 32 := 0x01878793.
Lemma F_111f60 : fetch_word AsanUbsan.M.loaded_segments (0x111f60 : word) = Some W_111f60.
Proof. vm_refl. Qed.
Lemma D_111f60 : decode_any W_111f60 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f64 : bv 32 := 0x40f70733.
Lemma F_111f64 : fetch_word AsanUbsan.M.loaded_segments (0x111f64 : word) = Some W_111f64.
Proof. vm_refl. Qed.
Lemma D_111f64 : decode_any W_111f64 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f68 : bv 32 := 0xfec6a223.
Lemma F_111f68 : fetch_word AsanUbsan.M.loaded_segments (0x111f68 : word) = Some W_111f68.
Proof. vm_refl. Qed.
Lemma D_111f68 : decode_any W_111f68 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f6c : bv 32 := 0xfec6a423.
Lemma F_111f6c : fetch_word AsanUbsan.M.loaded_segments (0x111f6c : word) = Some W_111f6c.
Proof. vm_refl. Qed.
Lemma D_111f6c : decode_any W_111f6c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f70 : bv 32 := 0xfec6a623.
Lemma F_111f70 : fetch_word AsanUbsan.M.loaded_segments (0x111f70 : word) = Some W_111f70.
Proof. vm_refl. Qed.
Lemma D_111f70 : decode_any W_111f70 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f74 : bv 32 := 0xfec6a823.
Lemma F_111f74 : fetch_word AsanUbsan.M.loaded_segments (0x111f74 : word) = Some W_111f74.
Proof. vm_refl. Qed.
Lemma D_111f74 : decode_any W_111f74 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f78 : bv 32 := 0x03076a63.
Lemma F_111f78 : fetch_word AsanUbsan.M.loaded_segments (0x111f78 : word) = Some W_111f78.
Proof. vm_refl. Qed.
Lemma D_111f78 : decode_any W_111f78 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f7c : bv 32 := 0x02061613.
Lemma F_111f7c : fetch_word AsanUbsan.M.loaded_segments (0x111f7c : word) = Some W_111f7c.
Proof. vm_refl. Qed.
Lemma D_111f7c : decode_any W_111f7c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f80 : bv 32 := 0x00f585b3.
Lemma F_111f80 : fetch_word AsanUbsan.M.loaded_segments (0x111f80 : word) = Some W_111f80.
Proof. vm_refl. Qed.
Lemma D_111f80 : decode_any W_111f80 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f84 : bv 32 := 0x02065693.
Lemma F_111f84 : fetch_word AsanUbsan.M.loaded_segments (0x111f84 : word) = Some W_111f84.
Proof. vm_refl. Qed.
Lemma D_111f84 : decode_any W_111f84 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f88 : bv 32 := 0x00d66633.
Lemma F_111f88 : fetch_word AsanUbsan.M.loaded_segments (0x111f88 : word) = Some W_111f88.
Proof. vm_refl. Qed.
Lemma D_111f88 : decode_any W_111f88 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f8c : bv 32 := 0x01f00693.
Lemma F_111f8c : fetch_word AsanUbsan.M.loaded_segments (0x111f8c : word) = Some W_111f8c.
Proof. vm_refl. Qed.
Lemma D_111f8c : decode_any W_111f8c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f90 : bv 32 := 0x00c5b023.
Lemma F_111f90 : fetch_word AsanUbsan.M.loaded_segments (0x111f90 : word) = Some W_111f90.
Proof. vm_refl. Qed.
Lemma D_111f90 : decode_any W_111f90 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f94 : bv 32 := 0x00c5b423.
Lemma F_111f94 : fetch_word AsanUbsan.M.loaded_segments (0x111f94 : word) = Some W_111f94.
Proof. vm_refl. Qed.
Lemma D_111f94 : decode_any W_111f94 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f98 : bv 32 := 0x00c5b823.
Lemma F_111f98 : fetch_word AsanUbsan.M.loaded_segments (0x111f98 : word) = Some W_111f98.
Proof. vm_refl. Qed.
Lemma D_111f98 : decode_any W_111f98 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111f9c : bv 32 := 0x00c5bc23.
Lemma F_111f9c : fetch_word AsanUbsan.M.loaded_segments (0x111f9c : word) = Some W_111f9c.
Proof. vm_refl. Qed.
Lemma D_111f9c : decode_any W_111f9c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111fa0 : bv 32 := 0xfe070713.
Lemma F_111fa0 : fetch_word AsanUbsan.M.loaded_segments (0x111fa0 : word) = Some W_111fa0.
Proof. vm_refl. Qed.
Lemma D_111fa0 : decode_any W_111fa0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111fa4 : bv 32 := 0x02058593.
Lemma F_111fa4 : fetch_word AsanUbsan.M.loaded_segments (0x111fa4 : word) = Some W_111fa4.
Proof. vm_refl. Qed.
Lemma D_111fa4 : decode_any W_111fa4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111fa8 : bv 32 := 0xfee6e4e3.
Lemma F_111fa8 : fetch_word AsanUbsan.M.loaded_segments (0x111fa8 : word) = Some W_111fa8.
Proof. vm_refl. Qed.
Lemma D_111fa8 : decode_any W_111fa8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_111fac : bv 32 := 0x00008067.
Lemma F_111fac : fetch_word AsanUbsan.M.loaded_segments (0x111fac : word) = Some W_111fac.
Proof. vm_refl. Qed.
Lemma D_111fac : decode_any W_111fac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x111eb8%Z.
Definition Fo_000 := F_111eb8.
Definition Do_000 := D_111eb8.
Definition Fo_004 := F_111ebc.
Definition Do_004 := D_111ebc.
Definition Fo_008 := F_111ec0.
Definition Do_008 := D_111ec0.
Definition Fo_00c := F_111ec4.
Definition Do_00c := D_111ec4.
Definition Fo_010 := F_111ec8.
Definition Do_010 := D_111ec8.
Definition Fo_014 := F_111ecc.
Definition Do_014 := D_111ecc.
Definition Fo_018 := F_111ed0.
Definition Do_018 := D_111ed0.
Definition Fo_01c := F_111ed4.
Definition Do_01c := D_111ed4.
Definition Fo_020 := F_111ed8.
Definition Do_020 := D_111ed8.
Definition Fo_024 := F_111edc.
Definition Do_024 := D_111edc.
Definition Fo_028 := F_111ee0.
Definition Do_028 := D_111ee0.
Definition Fo_02c := F_111ee4.
Definition Do_02c := D_111ee4.
Definition Fo_030 := F_111ee8.
Definition Do_030 := D_111ee8.
Definition Fo_034 := F_111eec.
Definition Do_034 := D_111eec.
Definition Fo_038 := F_111ef0.
Definition Do_038 := D_111ef0.
Definition Fo_03c := F_111ef4.
Definition Do_03c := D_111ef4.
Definition Fo_040 := F_111ef8.
Definition Do_040 := D_111ef8.
Definition Fo_044 := F_111efc.
Definition Do_044 := D_111efc.
Definition Fo_048 := F_111f00.
Definition Do_048 := D_111f00.
Definition Fo_04c := F_111f04.
Definition Do_04c := D_111f04.
Definition Fo_050 := F_111f08.
Definition Do_050 := D_111f08.
Definition Fo_054 := F_111f0c.
Definition Do_054 := D_111f0c.
Definition Fo_058 := F_111f10.
Definition Do_058 := D_111f10.
Definition Fo_05c := F_111f14.
Definition Do_05c := D_111f14.
Definition Fo_060 := F_111f18.
Definition Do_060 := D_111f18.
Definition Fo_064 := F_111f1c.
Definition Do_064 := D_111f1c.
Definition Fo_068 := F_111f20.
Definition Do_068 := D_111f20.
Definition Fo_06c := F_111f24.
Definition Do_06c := D_111f24.
Definition Fo_070 := F_111f28.
Definition Do_070 := D_111f28.
Definition Fo_074 := F_111f2c.
Definition Do_074 := D_111f2c.
Definition Fo_078 := F_111f30.
Definition Do_078 := D_111f30.
Definition Fo_07c := F_111f34.
Definition Do_07c := D_111f34.
Definition Fo_080 := F_111f38.
Definition Do_080 := D_111f38.
Definition Fo_084 := F_111f3c.
Definition Do_084 := D_111f3c.
Definition Fo_088 := F_111f40.
Definition Do_088 := D_111f40.
Definition Fo_08c := F_111f44.
Definition Do_08c := D_111f44.
Definition Fo_090 := F_111f48.
Definition Do_090 := D_111f48.
Definition Fo_094 := F_111f4c.
Definition Do_094 := D_111f4c.
Definition Fo_098 := F_111f50.
Definition Do_098 := D_111f50.
Definition Fo_09c := F_111f54.
Definition Do_09c := D_111f54.
Definition Fo_0a0 := F_111f58.
Definition Do_0a0 := D_111f58.
Definition Fo_0a4 := F_111f5c.
Definition Do_0a4 := D_111f5c.
Definition Fo_0a8 := F_111f60.
Definition Do_0a8 := D_111f60.
Definition Fo_0ac := F_111f64.
Definition Do_0ac := D_111f64.
Definition Fo_0b0 := F_111f68.
Definition Do_0b0 := D_111f68.
Definition Fo_0b4 := F_111f6c.
Definition Do_0b4 := D_111f6c.
Definition Fo_0b8 := F_111f70.
Definition Do_0b8 := D_111f70.
Definition Fo_0bc := F_111f74.
Definition Do_0bc := D_111f74.
Definition Fo_0c0 := F_111f78.
Definition Do_0c0 := D_111f78.
Definition Fo_0c4 := F_111f7c.
Definition Do_0c4 := D_111f7c.
Definition Fo_0c8 := F_111f80.
Definition Do_0c8 := D_111f80.
Definition Fo_0cc := F_111f84.
Definition Do_0cc := D_111f84.
Definition Fo_0d0 := F_111f88.
Definition Do_0d0 := D_111f88.
Definition Fo_0d4 := F_111f8c.
Definition Do_0d4 := D_111f8c.
Definition Fo_0d8 := F_111f90.
Definition Do_0d8 := D_111f90.
Definition Fo_0dc := F_111f94.
Definition Do_0dc := D_111f94.
Definition Fo_0e0 := F_111f98.
Definition Do_0e0 := D_111f98.
Definition Fo_0e4 := F_111f9c.
Definition Do_0e4 := D_111f9c.
Definition Fo_0e8 := F_111fa0.
Definition Do_0e8 := D_111fa0.
Definition Fo_0ec := F_111fa4.
Definition Do_0ec := D_111fa4.
Definition Fo_0f0 := F_111fa8.
Definition Do_0f0 := D_111fa8.
Definition Fo_0f4 := F_111fac.
Definition Do_0f4 := D_111fac.
