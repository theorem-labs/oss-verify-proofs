(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3bdf0 : bv 32 := 0xfd010113.
Lemma F_3bdf0 : fetch_word Plain.M.loaded_segments (0x3bdf0 : word) = Some W_3bdf0.
Proof. vm_refl. Qed.
Lemma D_3bdf0 : decode_any W_3bdf0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdf4 : bv 32 := 0x02113423.
Lemma F_3bdf4 : fetch_word Plain.M.loaded_segments (0x3bdf4 : word) = Some W_3bdf4.
Proof. vm_refl. Qed.
Lemma D_3bdf4 : decode_any W_3bdf4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdf8 : bv 32 := 0x02813023.
Lemma F_3bdf8 : fetch_word Plain.M.loaded_segments (0x3bdf8 : word) = Some W_3bdf8.
Proof. vm_refl. Qed.
Lemma D_3bdf8 : decode_any W_3bdf8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdfc : bv 32 := 0x00913c23.
Lemma F_3bdfc : fetch_word Plain.M.loaded_segments (0x3bdfc : word) = Some W_3bdfc.
Proof. vm_refl. Qed.
Lemma D_3bdfc : decode_any W_3bdfc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be00 : bv 32 := 0x00068493.
Lemma F_3be00 : fetch_word Plain.M.loaded_segments (0x3be00 : word) = Some W_3be00.
Proof. vm_refl. Qed.
Lemma D_3be00 : decode_any W_3be00 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be04 : bv 32 := 0x04b57463.
Lemma F_3be04 : fetch_word Plain.M.loaded_segments (0x3be04 : word) = Some W_3be04.
Proof. vm_refl. Qed.
Lemma D_3be04 : decode_any W_3be04 = Some (Branch BC_GEU 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be08 : bv 32 := 0x00058413.
Lemma F_3be08 : fetch_word Plain.M.loaded_segments (0x3be08 : word) = Some W_3be08.
Proof. vm_refl. Qed.
Lemma D_3be08 : decode_any W_3be08 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be0c : bv 32 := 0x00150813.
Lemma F_3be0c : fetch_word Plain.M.loaded_segments (0x3be0c : word) = Some W_3be0c.
Proof. vm_refl. Qed.
Lemma D_3be0c : decode_any W_3be0c = Some (OpImm ALU_ADD 16 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be10 : bv 32 := 0x05f00593.
Lemma F_3be10 : fetch_word Plain.M.loaded_segments (0x3be10 : word) = Some W_3be10.
Proof. vm_refl. Qed.
Lemma D_3be10 : decode_any W_3be10 = Some (OpImm ALU_ADD 11 0 95, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be14 : bv 32 := 0x01f00693.
Lemma F_3be14 : fetch_word Plain.M.loaded_segments (0x3be14 : word) = Some W_3be14.
Proof. vm_refl. Qed.
Lemma D_3be14 : decode_any W_3be14 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be18 : bv 32 := 0x07f00713.
Lemma F_3be18 : fetch_word Plain.M.loaded_segments (0x3be18 : word) = Some W_3be18.
Proof. vm_refl. Qed.
Lemma D_3be18 : decode_any W_3be18 = Some (OpImm ALU_ADD 14 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be1c : bv 32 := 0x00900793.
Lemma F_3be1c : fetch_word Plain.M.loaded_segments (0x3be1c : word) = Some W_3be1c.
Proof. vm_refl. Qed.
Lemma D_3be1c : decode_any W_3be1c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be20 : bv 32 := 0x00080513.
Lemma F_3be20 : fetch_word Plain.M.loaded_segments (0x3be20 : word) = Some W_3be20.
Proof. vm_refl. Qed.
Lemma D_3be20 : decode_any W_3be20 = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be24 : bv 32 := 0xfff84803.
Lemma F_3be24 : fetch_word Plain.M.loaded_segments (0x3be24 : word) = Some W_3be24.
Proof. vm_refl. Qed.
Lemma D_3be24 : decode_any W_3be24 = Some (Load SZ1 false 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be28 : bv 32 := 0xfe080893.
Lemma F_3be28 : fetch_word Plain.M.loaded_segments (0x3be28 : word) = Some W_3be28.
Proof. vm_refl. Qed.
Lemma D_3be28 : decode_any W_3be28 = Some (OpImm ALU_ADD 17 16 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be2c : bv 32 := 0x00b8f863.
Lemma F_3be2c : fetch_word Plain.M.loaded_segments (0x3be2c : word) = Some W_3be2c.
Proof. vm_refl. Qed.
Lemma D_3be2c : decode_any W_3be2c = Some (Branch BC_GEU 17 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be30 : bv 32 := 0x00150813.
Lemma F_3be30 : fetch_word Plain.M.loaded_segments (0x3be30 : word) = Some W_3be30.
Proof. vm_refl. Qed.
Lemma D_3be30 : decode_any W_3be30 = Some (OpImm ALU_ADD 16 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be34 : bv 32 := 0x00850e63.
Lemma F_3be34 : fetch_word Plain.M.loaded_segments (0x3be34 : word) = Some W_3be34.
Proof. vm_refl. Qed.
Lemma D_3be34 : decode_any W_3be34 = Some (Branch BC_EQ 10 8 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be38 : bv 32 := 0xfe9ff06f.
Lemma F_3be38 : fetch_word Plain.M.loaded_segments (0x3be38 : word) = Some W_3be38.
Proof. vm_refl. Qed.
Lemma D_3be38 : decode_any W_3be38 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be3c : bv 32 := 0x0106e463.
Lemma F_3be3c : fetch_word Plain.M.loaded_segments (0x3be3c : word) = Some W_3be3c.
Proof. vm_refl. Qed.
Lemma D_3be3c : decode_any W_3be3c = Some (Branch BC_LTU 13 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be40 : bv 32 := 0x06f81463.
Lemma F_3be40 : fetch_word Plain.M.loaded_segments (0x3be40 : word) = Some W_3be40.
Proof. vm_refl. Qed.
Lemma D_3be40 : decode_any W_3be40 = Some (Branch BC_NE 16 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be44 : bv 32 := 0x0ee80263.
Lemma F_3be44 : fetch_word Plain.M.loaded_segments (0x3be44 : word) = Some W_3be44.
Proof. vm_refl. Qed.
Lemma D_3be44 : decode_any W_3be44 = Some (Branch BC_EQ 16 14 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be48 : bv 32 := 0xfe9ff06f.
Lemma F_3be48 : fetch_word Plain.M.loaded_segments (0x3be48 : word) = Some W_3be48.
Proof. vm_refl. Qed.
Lemma D_3be48 : decode_any W_3be48 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be4c : bv 32 := 0x00050413.
Lemma F_3be4c : fetch_word Plain.M.loaded_segments (0x3be4c : word) = Some W_3be4c.
Proof. vm_refl. Qed.
Lemma D_3be4c : decode_any W_3be4c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be50 : bv 32 := 0x00010513.
Lemma F_3be50 : fetch_word Plain.M.loaded_segments (0x3be50 : word) = Some W_3be50.
Proof. vm_refl. Qed.
Lemma D_3be50 : decode_any W_3be50 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be54 : bv 32 := 0x00300593.
Lemma F_3be54 : fetch_word Plain.M.loaded_segments (0x3be54 : word) = Some W_3be54.
Proof. vm_refl. Qed.
Lemma D_3be54 : decode_any W_3be54 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be58 : bv 32 := 0x00000613.
Lemma F_3be58 : fetch_word Plain.M.loaded_segments (0x3be58 : word) = Some W_3be58.
Proof. vm_refl. Qed.
Lemma D_3be58 : decode_any W_3be58 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be5c : bv 32 := 0xd70f60ef.
Lemma F_3be5c : fetch_word Plain.M.loaded_segments (0x3be5c : word) = Some W_3be5c.
Proof. vm_refl. Qed.
Lemma D_3be5c : decode_any W_3be5c = Some (Jal 1 2057584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be60 : bv 32 := 0x01013503.
Lemma F_3be60 : fetch_word Plain.M.loaded_segments (0x3be60 : word) = Some W_3be60.
Proof. vm_refl. Qed.
Lemma D_3be60 : decode_any W_3be60 = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be64 : bv 32 := 0x00200593.
Lemma F_3be64 : fetch_word Plain.M.loaded_segments (0x3be64 : word) = Some W_3be64.
Proof. vm_refl. Qed.
Lemma D_3be64 : decode_any W_3be64 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be68 : bv 32 := 0x00b56a63.
Lemma F_3be68 : fetch_word Plain.M.loaded_segments (0x3be68 : word) = Some W_3be68.
Proof. vm_refl. Qed.
Lemma D_3be68 : decode_any W_3be68 = Some (Branch BC_LTU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be6c : bv 32 := 0x00157513.
Lemma F_3be6c : fetch_word Plain.M.loaded_segments (0x3be6c : word) = Some W_3be6c.
Proof. vm_refl. Qed.
Lemma D_3be6c : decode_any W_3be6c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be70 : bv 32 := 0x00040597.
Lemma F_3be70 : fetch_word Plain.M.loaded_segments (0x3be70 : word) = Some W_3be70.
Proof. vm_refl. Qed.
Lemma D_3be70 : decode_any W_3be70 = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be74 : bv 32 := 0x21058593.
Lemma F_3be74 : fetch_word Plain.M.loaded_segments (0x3be74 : word) = Some W_3be74.
Proof. vm_refl. Qed.
Lemma D_3be74 : decode_any W_3be74 = Some (OpImm ALU_ADD 11 11 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be78 : bv 32 := 0x00b56533.
Lemma F_3be78 : fetch_word Plain.M.loaded_segments (0x3be78 : word) = Some W_3be78.
Proof. vm_refl. Qed.
Lemma D_3be78 : decode_any W_3be78 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be7c : bv 32 := 0x00013583.
Lemma F_3be7c : fetch_word Plain.M.loaded_segments (0x3be7c : word) = Some W_3be7c.
Proof. vm_refl. Qed.
Lemma D_3be7c : decode_any W_3be7c = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be80 : bv 32 := 0x00813603.
Lemma F_3be80 : fetch_word Plain.M.loaded_segments (0x3be80 : word) = Some W_3be80.
Proof. vm_refl. Qed.
Lemma D_3be80 : decode_any W_3be80 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be84 : bv 32 := 0x00b4b023.
Lemma F_3be84 : fetch_word Plain.M.loaded_segments (0x3be84 : word) = Some W_3be84.
Proof. vm_refl. Qed.
Lemma D_3be84 : decode_any W_3be84 = Some (Store SZ8 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be88 : bv 32 := 0x00c4b423.
Lemma F_3be88 : fetch_word Plain.M.loaded_segments (0x3be88 : word) = Some W_3be88.
Proof. vm_refl. Qed.
Lemma D_3be88 : decode_any W_3be88 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be8c : bv 32 := 0x00a4b823.
Lemma F_3be8c : fetch_word Plain.M.loaded_segments (0x3be8c : word) = Some W_3be8c.
Proof. vm_refl. Qed.
Lemma D_3be8c : decode_any W_3be8c = Some (Store SZ8 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be90 : bv 32 := 0x00040513.
Lemma F_3be90 : fetch_word Plain.M.loaded_segments (0x3be90 : word) = Some W_3be90.
Proof. vm_refl. Qed.
Lemma D_3be90 : decode_any W_3be90 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be94 : bv 32 := 0x02813083.
Lemma F_3be94 : fetch_word Plain.M.loaded_segments (0x3be94 : word) = Some W_3be94.
Proof. vm_refl. Qed.
Lemma D_3be94 : decode_any W_3be94 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be98 : bv 32 := 0x02013403.
Lemma F_3be98 : fetch_word Plain.M.loaded_segments (0x3be98 : word) = Some W_3be98.
Proof. vm_refl. Qed.
Lemma D_3be98 : decode_any W_3be98 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be9c : bv 32 := 0x01813483.
Lemma F_3be9c : fetch_word Plain.M.loaded_segments (0x3be9c : word) = Some W_3be9c.
Proof. vm_refl. Qed.
Lemma D_3be9c : decode_any W_3be9c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bea0 : bv 32 := 0x03010113.
Lemma F_3bea0 : fetch_word Plain.M.loaded_segments (0x3bea0 : word) = Some W_3bea0.
Proof. vm_refl. Qed.
Lemma D_3bea0 : decode_any W_3bea0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bea4 : bv 32 := 0x00008067.
Lemma F_3bea4 : fetch_word Plain.M.loaded_segments (0x3bea4 : word) = Some W_3bea4.
Proof. vm_refl. Qed.
Lemma D_3bea4 : decode_any W_3bea4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bea8 : bv 32 := 0x00d00593.
Lemma F_3bea8 : fetch_word Plain.M.loaded_segments (0x3bea8 : word) = Some W_3bea8.
Proof. vm_refl. Qed.
Lemma D_3bea8 : decode_any W_3bea8 = Some (OpImm ALU_ADD 11 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beac : bv 32 := 0x06b81e63.
Lemma F_3beac : fetch_word Plain.M.loaded_segments (0x3beac : word) = Some W_3beac.
Proof. vm_refl. Qed.
Lemma D_3beac : decode_any W_3beac = Some (Branch BC_NE 16 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beb0 : bv 32 := 0x02857063.
Lemma F_3beb0 : fetch_word Plain.M.loaded_segments (0x3beb0 : word) = Some W_3beb0.
Proof. vm_refl. Qed.
Lemma D_3beb0 : decode_any W_3beb0 = Some (Branch BC_GEU 10 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beb4 : bv 32 := 0x00054583.
Lemma F_3beb4 : fetch_word Plain.M.loaded_segments (0x3beb4 : word) = Some W_3beb4.
Proof. vm_refl. Qed.
Lemma D_3beb4 : decode_any W_3beb4 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beb8 : bv 32 := 0x00a00693.
Lemma F_3beb8 : fetch_word Plain.M.loaded_segments (0x3beb8 : word) = Some W_3beb8.
Proof. vm_refl. Qed.
Lemma D_3beb8 : decode_any W_3beb8 = Some (OpImm ALU_ADD 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bebc : bv 32 := 0x04d59063.
Lemma F_3bebc : fetch_word Plain.M.loaded_segments (0x3bebc : word) = Some W_3bebc.
Proof. vm_refl. Qed.
Lemma D_3bebc : decode_any W_3bebc = Some (Branch BC_NE 11 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bec0 : bv 32 := 0xfff50593.
Lemma F_3bec0 : fetch_word Plain.M.loaded_segments (0x3bec0 : word) = Some W_3bec0.
Proof. vm_refl. Qed.
Lemma D_3bec0 : decode_any W_3bec0 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bec4 : bv 32 := 0x00150413.
Lemma F_3bec4 : fetch_word Plain.M.loaded_segments (0x3bec4 : word) = Some W_3bec4.
Proof. vm_refl. Qed.
Lemma D_3bec4 : decode_any W_3bec4 = Some (OpImm ALU_ADD 8 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bec8 : bv 32 := 0x00b63023.
Lemma F_3bec8 : fetch_word Plain.M.loaded_segments (0x3bec8 : word) = Some W_3bec8.
Proof. vm_refl. Qed.
Lemma D_3bec8 : decode_any W_3bec8 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3becc : bv 32 := 0xfc5ff06f.
Lemma F_3becc : fetch_word Plain.M.loaded_segments (0x3becc : word) = Some W_3becc.
Proof. vm_refl. Qed.
Lemma D_3becc : decode_any W_3becc = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bed0 : bv 32 := 0x00010513.
Lemma F_3bed0 : fetch_word Plain.M.loaded_segments (0x3bed0 : word) = Some W_3bed0.
Proof. vm_refl. Qed.
Lemma D_3bed0 : decode_any W_3bed0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bed4 : bv 32 := 0x00300593.
Lemma F_3bed4 : fetch_word Plain.M.loaded_segments (0x3bed4 : word) = Some W_3bed4.
Proof. vm_refl. Qed.
Lemma D_3bed4 : decode_any W_3bed4 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bed8 : bv 32 := 0x00000613.
Lemma F_3bed8 : fetch_word Plain.M.loaded_segments (0x3bed8 : word) = Some W_3bed8.
Proof. vm_refl. Qed.
Lemma D_3bed8 : decode_any W_3bed8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bedc : bv 32 := 0xcf0f60ef.
Lemma F_3bedc : fetch_word Plain.M.loaded_segments (0x3bedc : word) = Some W_3bedc.
Proof. vm_refl. Qed.
Lemma D_3bedc : decode_any W_3bedc = Some (Jal 1 2057456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bee0 : bv 32 := 0x01013503.
Lemma F_3bee0 : fetch_word Plain.M.loaded_segments (0x3bee0 : word) = Some W_3bee0.
Proof. vm_refl. Qed.
Lemma D_3bee0 : decode_any W_3bee0 = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bee4 : bv 32 := 0x00200593.
Lemma F_3bee4 : fetch_word Plain.M.loaded_segments (0x3bee4 : word) = Some W_3bee4.
Proof. vm_refl. Qed.
Lemma D_3bee4 : decode_any W_3bee4 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bee8 : bv 32 := 0xf8b56ae3.
Lemma F_3bee8 : fetch_word Plain.M.loaded_segments (0x3bee8 : word) = Some W_3bee8.
Proof. vm_refl. Qed.
Lemma D_3bee8 : decode_any W_3bee8 = Some (Branch BC_LTU 10 11 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beec : bv 32 := 0x00157513.
Lemma F_3beec : fetch_word Plain.M.loaded_segments (0x3beec : word) = Some W_3beec.
Proof. vm_refl. Qed.
Lemma D_3beec : decode_any W_3beec = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bef0 : bv 32 := 0x00040597.
Lemma F_3bef0 : fetch_word Plain.M.loaded_segments (0x3bef0 : word) = Some W_3bef0.
Proof. vm_refl. Qed.
Lemma D_3bef0 : decode_any W_3bef0 = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bef4 : bv 32 := 0x1a858593.
Lemma F_3bef4 : fetch_word Plain.M.loaded_segments (0x3bef4 : word) = Some W_3bef4.
Proof. vm_refl. Qed.
Lemma D_3bef4 : decode_any W_3bef4 = Some (OpImm ALU_ADD 11 11 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bef8 : bv 32 := 0xf81ff06f.
Lemma F_3bef8 : fetch_word Plain.M.loaded_segments (0x3bef8 : word) = Some W_3bef8.
Proof. vm_refl. Qed.
Lemma D_3bef8 : decode_any W_3bef8 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3befc : bv 32 := 0x00010513.
Lemma F_3befc : fetch_word Plain.M.loaded_segments (0x3befc : word) = Some W_3befc.
Proof. vm_refl. Qed.
Lemma D_3befc : decode_any W_3befc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf00 : bv 32 := 0x00b00593.
Lemma F_3bf00 : fetch_word Plain.M.loaded_segments (0x3bf00 : word) = Some W_3bf00.
Proof. vm_refl. Qed.
Lemma D_3bf00 : decode_any W_3bf00 = Some (OpImm ALU_ADD 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf04 : bv 32 := 0x00000613.
Lemma F_3bf04 : fetch_word Plain.M.loaded_segments (0x3bf04 : word) = Some W_3bf04.
Proof. vm_refl. Qed.
Lemma D_3bf04 : decode_any W_3bf04 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf08 : bv 32 := 0xcc4f60ef.
Lemma F_3bf08 : fetch_word Plain.M.loaded_segments (0x3bf08 : word) = Some W_3bf08.
Proof. vm_refl. Qed.
Lemma D_3bf08 : decode_any W_3bf08 = Some (Jal 1 2057412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf0c : bv 32 := 0x01013503.
Lemma F_3bf0c : fetch_word Plain.M.loaded_segments (0x3bf0c : word) = Some W_3bf0c.
Proof. vm_refl. Qed.
Lemma D_3bf0c : decode_any W_3bf0c = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf10 : bv 32 := 0x00200593.
Lemma F_3bf10 : fetch_word Plain.M.loaded_segments (0x3bf10 : word) = Some W_3bf10.
Proof. vm_refl. Qed.
Lemma D_3bf10 : decode_any W_3bf10 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf14 : bv 32 := 0xf6b564e3.
Lemma F_3bf14 : fetch_word Plain.M.loaded_segments (0x3bf14 : word) = Some W_3bf14.
Proof. vm_refl. Qed.
Lemma D_3bf14 : decode_any W_3bf14 = Some (Branch BC_LTU 10 11 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf18 : bv 32 := 0x00157513.
Lemma F_3bf18 : fetch_word Plain.M.loaded_segments (0x3bf18 : word) = Some W_3bf18.
Proof. vm_refl. Qed.
Lemma D_3bf18 : decode_any W_3bf18 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf1c : bv 32 := 0x00040597.
Lemma F_3bf1c : fetch_word Plain.M.loaded_segments (0x3bf1c : word) = Some W_3bf1c.
Proof. vm_refl. Qed.
Lemma D_3bf1c : decode_any W_3bf1c = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf20 : bv 32 := 0x19458593.
Lemma F_3bf20 : fetch_word Plain.M.loaded_segments (0x3bf20 : word) = Some W_3bf20.
Proof. vm_refl. Qed.
Lemma D_3bf20 : decode_any W_3bf20 = Some (OpImm ALU_ADD 11 11 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf24 : bv 32 := 0xf55ff06f.
Lemma F_3bf24 : fetch_word Plain.M.loaded_segments (0x3bf24 : word) = Some W_3bf24.
Proof. vm_refl. Qed.
Lemma D_3bf24 : decode_any W_3bf24 = Some (Jal 0 2096980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf28 : bv 32 := 0x00000413.
Lemma F_3bf28 : fetch_word Plain.M.loaded_segments (0x3bf28 : word) = Some W_3bf28.
Proof. vm_refl. Qed.
Lemma D_3bf28 : decode_any W_3bf28 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf2c : bv 32 := 0xf65ff06f.
Lemma F_3bf2c : fetch_word Plain.M.loaded_segments (0x3bf2c : word) = Some W_3bf2c.
Proof. vm_refl. Qed.
Lemma D_3bf2c : decode_any W_3bf2c = Some (Jal 0 2096996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf30 : bv 32 := 0xfd010113.
Lemma F_3bf30 : fetch_word Plain.M.loaded_segments (0x3bf30 : word) = Some W_3bf30.
Proof. vm_refl. Qed.
Lemma D_3bf30 : decode_any W_3bf30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf34 : bv 32 := 0x02113423.
Lemma F_3bf34 : fetch_word Plain.M.loaded_segments (0x3bf34 : word) = Some W_3bf34.
Proof. vm_refl. Qed.
Lemma D_3bf34 : decode_any W_3bf34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf38 : bv 32 := 0x02813023.
Lemma F_3bf38 : fetch_word Plain.M.loaded_segments (0x3bf38 : word) = Some W_3bf38.
Proof. vm_refl. Qed.
Lemma D_3bf38 : decode_any W_3bf38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf3c : bv 32 := 0x00913c23.
Lemma F_3bf3c : fetch_word Plain.M.loaded_segments (0x3bf3c : word) = Some W_3bf3c.
Proof. vm_refl. Qed.
Lemma D_3bf3c : decode_any W_3bf3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf40 : bv 32 := 0x01213823.
Lemma F_3bf40 : fetch_word Plain.M.loaded_segments (0x3bf40 : word) = Some W_3bf40.
Proof. vm_refl. Qed.
Lemma D_3bf40 : decode_any W_3bf40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf44 : bv 32 := 0x01313423.
Lemma F_3bf44 : fetch_word Plain.M.loaded_segments (0x3bf44 : word) = Some W_3bf44.
Proof. vm_refl. Qed.
Lemma D_3bf44 : decode_any W_3bf44 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf48 : bv 32 := 0x00060413.
Lemma F_3bf48 : fetch_word Plain.M.loaded_segments (0x3bf48 : word) = Some W_3bf48.
Proof. vm_refl. Qed.
Lemma D_3bf48 : decode_any W_3bf48 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf4c : bv 32 := 0x00058493.
Lemma F_3bf4c : fetch_word Plain.M.loaded_segments (0x3bf4c : word) = Some W_3bf4c.
Proof. vm_refl. Qed.
Lemma D_3bf4c : decode_any W_3bf4c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf50 : bv 32 := 0x00050913.
Lemma F_3bf50 : fetch_word Plain.M.loaded_segments (0x3bf50 : word) = Some W_3bf50.
Proof. vm_refl. Qed.
Lemma D_3bf50 : decode_any W_3bf50 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf54 : bv 32 := 0x00058513.
Lemma F_3bf54 : fetch_word Plain.M.loaded_segments (0x3bf54 : word) = Some W_3bf54.
Proof. vm_refl. Qed.
Lemma D_3bf54 : decode_any W_3bf54 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf58 : bv 32 := 0x00060593.
Lemma F_3bf58 : fetch_word Plain.M.loaded_segments (0x3bf58 : word) = Some W_3bf58.
Proof. vm_refl. Qed.
Lemma D_3bf58 : decode_any W_3bf58 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf5c : bv 32 := 0xc64f80ef.
Lemma F_3bf5c : fetch_word Plain.M.loaded_segments (0x3bf5c : word) = Some W_3bf5c.
Proof. vm_refl. Qed.
Lemma D_3bf5c : decode_any W_3bf5c = Some (Jal 1 2065508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf60 : bv 32 := 0x02051593.
Lemma F_3bf60 : fetch_word Plain.M.loaded_segments (0x3bf60 : word) = Some W_3bf60.
Proof. vm_refl. Qed.
Lemma D_3bf60 : decode_any W_3bf60 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf64 : bv 32 := 0x7f882637.
Lemma F_3bf64 : fetch_word Plain.M.loaded_segments (0x3bf64 : word) = Some W_3bf64.
Proof. vm_refl. Qed.
Lemma D_3bf64 : decode_any W_3bf64 = Some (Lui 12 522370, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf68 : bv 32 := 0x57560613.
Lemma F_3bf68 : fetch_word Plain.M.loaded_segments (0x3bf68 : word) = Some W_3bf68.
Proof. vm_refl. Qed.
Lemma D_3bf68 : decode_any W_3bf68 = Some (OpImm ALU_ADD 12 12 1397, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf6c : bv 32 := 0x02061613.
Lemma F_3bf6c : fetch_word Plain.M.loaded_segments (0x3bf6c : word) = Some W_3bf6c.
Proof. vm_refl. Qed.
Lemma D_3bf6c : decode_any W_3bf6c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf70 : bv 32 := 0x02c5b5b3.
Lemma F_3bf70 : fetch_word Plain.M.loaded_segments (0x3bf70 : word) = Some W_3bf70.
Proof. vm_refl. Qed.
Lemma D_3bf70 : decode_any W_3bf70 = Some (Mul M_MULHU 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf74 : bv 32 := 0x0205d593.
Lemma F_3bf74 : fetch_word Plain.M.loaded_segments (0x3bf74 : word) = Some W_3bf74.
Proof. vm_refl. Qed.
Lemma D_3bf74 : decode_any W_3bf74 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf78 : bv 32 := 0x40b5063b.
Lemma F_3bf78 : fetch_word Plain.M.loaded_segments (0x3bf78 : word) = Some W_3bf78.
Proof. vm_refl. Qed.
Lemma D_3bf78 : decode_any W_3bf78 = Some (Op32 ALU_SUB 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf7c : bv 32 := 0x0016561b.
Lemma F_3bf7c : fetch_word Plain.M.loaded_segments (0x3bf7c : word) = Some W_3bf7c.
Proof. vm_refl. Qed.
Lemma D_3bf7c : decode_any W_3bf7c = Some (ShiftImm32 ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf80 : bv 32 := 0x00b605b3.
Lemma F_3bf80 : fetch_word Plain.M.loaded_segments (0x3bf80 : word) = Some W_3bf80.
Proof. vm_refl. Qed.
Lemma D_3bf80 : decode_any W_3bf80 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf84 : bv 32 := 0x00a5d593.
Lemma F_3bf84 : fetch_word Plain.M.loaded_segments (0x3bf84 : word) = Some W_3bf84.
Proof. vm_refl. Qed.
Lemma D_3bf84 : decode_any W_3bf84 = Some (ShiftImm ALU_SRL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf88 : bv 32 := 0x55700613.
Lemma F_3bf88 : fetch_word Plain.M.loaded_segments (0x3bf88 : word) = Some W_3bf88.
Proof. vm_refl. Qed.
Lemma D_3bf88 : decode_any W_3bf88 = Some (OpImm ALU_ADD 12 0 1367, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf8c : bv 32 := 0x02c585b3.
Lemma F_3bf8c : fetch_word Plain.M.loaded_segments (0x3bf8c : word) = Some W_3bf8c.
Proof. vm_refl. Qed.
Lemma D_3bf8c : decode_any W_3bf8c = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf90 : bv 32 := 0x40b5053b.
Lemma F_3bf90 : fetch_word Plain.M.loaded_segments (0x3bf90 : word) = Some W_3bf90.
Proof. vm_refl. Qed.
Lemma D_3bf90 : decode_any W_3bf90 = Some (Op32 ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf94 : bv 32 := 0x02051513.
Lemma F_3bf94 : fetch_word Plain.M.loaded_segments (0x3bf94 : word) = Some W_3bf94.
Proof. vm_refl. Qed.
Lemma D_3bf94 : decode_any W_3bf94 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf98 : bv 32 := 0x02055513.
Lemma F_3bf98 : fetch_word Plain.M.loaded_segments (0x3bf98 : word) = Some W_3bf98.
Proof. vm_refl. Qed.
Lemma D_3bf98 : decode_any W_3bf98 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bf9c : bv 32 := 0x00a90533.
Lemma F_3bf9c : fetch_word Plain.M.loaded_segments (0x3bf9c : word) = Some W_3bf9c.
Proof. vm_refl. Qed.
Lemma D_3bf9c : decode_any W_3bf9c = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfa0 : bv 32 := 0x7ff50513.
Lemma F_3bfa0 : fetch_word Plain.M.loaded_segments (0x3bfa0 : word) = Some W_3bfa0.
Proof. vm_refl. Qed.
Lemma D_3bfa0 : decode_any W_3bfa0 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfa4 : bv 32 := 0x02154983.
Lemma F_3bfa4 : fetch_word Plain.M.loaded_segments (0x3bfa4 : word) = Some W_3bfa4.
Proof. vm_refl. Qed.
Lemma D_3bfa4 : decode_any W_3bfa4 = Some (Load SZ1 false 19 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfa8 : bv 32 := 0x02098663.
Lemma F_3bfa8 : fetch_word Plain.M.loaded_segments (0x3bfa8 : word) = Some W_3bfa8.
Proof. vm_refl. Qed.
Lemma D_3bfa8 : decode_any W_3bfa8 = Some (Branch BC_EQ 19 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfac : bv 32 := 0x00499513.
Lemma F_3bfac : fetch_word Plain.M.loaded_segments (0x3bfac : word) = Some W_3bfac.
Proof. vm_refl. Qed.
Lemma D_3bfac : decode_any W_3bfac = Some (ShiftImm ALU_SLL 10 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfb0 : bv 32 := 0x00a90533.
Lemma F_3bfb0 : fetch_word Plain.M.loaded_segments (0x3bfb0 : word) = Some W_3bfb0.
Proof. vm_refl. Qed.
Lemma D_3bfb0 : decode_any W_3bfb0 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfb4 : bv 32 := 0x00053603.
Lemma F_3bfb4 : fetch_word Plain.M.loaded_segments (0x3bfb4 : word) = Some W_3bfb4.
Proof. vm_refl. Qed.
Lemma D_3bfb4 : decode_any W_3bfb4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfb8 : bv 32 := 0x00853683.
Lemma F_3bfb8 : fetch_word Plain.M.loaded_segments (0x3bfb8 : word) = Some W_3bfb8.
Proof. vm_refl. Qed.
Lemma D_3bfb8 : decode_any W_3bfb8 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfbc : bv 32 := 0x00048513.
Lemma F_3bfbc : fetch_word Plain.M.loaded_segments (0x3bfbc : word) = Some W_3bfbc.
Proof. vm_refl. Qed.
Lemma D_3bfbc : decode_any W_3bfbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfc0 : bv 32 := 0x00040593.
Lemma F_3bfc0 : fetch_word Plain.M.loaded_segments (0x3bfc0 : word) = Some W_3bfc0.
Proof. vm_refl. Qed.
Lemma D_3bfc0 : decode_any W_3bfc0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfc4 : bv 32 := 0x038000ef.
Lemma F_3bfc4 : fetch_word Plain.M.loaded_segments (0x3bfc4 : word) = Some W_3bfc4.
Proof. vm_refl. Qed.
Lemma D_3bfc4 : decode_any W_3bfc4 = Some (Jal 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfc8 : bv 32 := 0x40a00533.
Lemma F_3bfc8 : fetch_word Plain.M.loaded_segments (0x3bfc8 : word) = Some W_3bfc8.
Proof. vm_refl. Qed.
Lemma D_3bfc8 : decode_any W_3bfc8 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfcc : bv 32 := 0x01357533.
Lemma F_3bfcc : fetch_word Plain.M.loaded_segments (0x3bfcc : word) = Some W_3bfcc.
Proof. vm_refl. Qed.
Lemma D_3bfcc : decode_any W_3bfcc = Some (Op ALU_AND 10 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfd0 : bv 32 := 0x0080006f.
Lemma F_3bfd0 : fetch_word Plain.M.loaded_segments (0x3bfd0 : word) = Some W_3bfd0.
Proof. vm_refl. Qed.
Lemma D_3bfd0 : decode_any W_3bfd0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfd4 : bv 32 := 0x00000513.
Lemma F_3bfd4 : fetch_word Plain.M.loaded_segments (0x3bfd4 : word) = Some W_3bfd4.
Proof. vm_refl. Qed.
Lemma D_3bfd4 : decode_any W_3bfd4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfd8 : bv 32 := 0x03051513.
Lemma F_3bfd8 : fetch_word Plain.M.loaded_segments (0x3bfd8 : word) = Some W_3bfd8.
Proof. vm_refl. Qed.
Lemma D_3bfd8 : decode_any W_3bfd8 = Some (ShiftImm ALU_SLL 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfdc : bv 32 := 0x03055513.
Lemma F_3bfdc : fetch_word Plain.M.loaded_segments (0x3bfdc : word) = Some W_3bfdc.
Proof. vm_refl. Qed.
Lemma D_3bfdc : decode_any W_3bfdc = Some (ShiftImm ALU_SRL 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfe0 : bv 32 := 0x02813083.
Lemma F_3bfe0 : fetch_word Plain.M.loaded_segments (0x3bfe0 : word) = Some W_3bfe0.
Proof. vm_refl. Qed.
Lemma D_3bfe0 : decode_any W_3bfe0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfe4 : bv 32 := 0x02013403.
Lemma F_3bfe4 : fetch_word Plain.M.loaded_segments (0x3bfe4 : word) = Some W_3bfe4.
Proof. vm_refl. Qed.
Lemma D_3bfe4 : decode_any W_3bfe4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfe8 : bv 32 := 0x01813483.
Lemma F_3bfe8 : fetch_word Plain.M.loaded_segments (0x3bfe8 : word) = Some W_3bfe8.
Proof. vm_refl. Qed.
Lemma D_3bfe8 : decode_any W_3bfe8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfec : bv 32 := 0x01013903.
Lemma F_3bfec : fetch_word Plain.M.loaded_segments (0x3bfec : word) = Some W_3bfec.
Proof. vm_refl. Qed.
Lemma D_3bfec : decode_any W_3bfec = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bff0 : bv 32 := 0x00813983.
Lemma F_3bff0 : fetch_word Plain.M.loaded_segments (0x3bff0 : word) = Some W_3bff0.
Proof. vm_refl. Qed.
Lemma D_3bff0 : decode_any W_3bff0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bff4 : bv 32 := 0x03010113.
Lemma F_3bff4 : fetch_word Plain.M.loaded_segments (0x3bff4 : word) = Some W_3bff4.
Proof. vm_refl. Qed.
Lemma D_3bff4 : decode_any W_3bff4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bff8 : bv 32 := 0x00008067.
Lemma F_3bff8 : fetch_word Plain.M.loaded_segments (0x3bff8 : word) = Some W_3bff8.
Proof. vm_refl. Qed.
Lemma D_3bff8 : decode_any W_3bff8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bffc : bv 32 := 0x0ad59e63.
Lemma F_3bffc : fetch_word Plain.M.loaded_segments (0x3bffc : word) = Some W_3bffc.
Proof. vm_refl. Qed.
Lemma D_3bffc : decode_any W_3bffc = Some (Branch BC_NE 11 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c000 : bv 32 := 0x00400693.
Lemma F_3c000 : fetch_word Plain.M.loaded_segments (0x3c000 : word) = Some W_3c000.
Proof. vm_refl. Qed.
Lemma D_3c000 : decode_any W_3c000 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c004 : bv 32 := 0x06d5ee63.
Lemma F_3c004 : fetch_word Plain.M.loaded_segments (0x3c004 : word) = Some W_3c004.
Proof. vm_refl. Qed.
Lemma D_3c004 : decode_any W_3c004 = Some (Branch BC_LTU 11 13 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c008 : bv 32 := 0xdfdfe6b7.
Lemma F_3c008 : fetch_word Plain.M.loaded_segments (0x3c008 : word) = Some W_3c008.
Proof. vm_refl. Qed.
Lemma D_3c008 : decode_any W_3c008 = Some (Lui 13 916990, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c00c : bv 32 := 0xfdf6869b.
Lemma F_3c00c : fetch_word Plain.M.loaded_segments (0x3c00c : word) = Some W_3c00c.
Proof. vm_refl. Qed.
Lemma D_3c00c : decode_any W_3c00c = Some (OpImm32 13 13 4063, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c010 : bv 32 := 0x00300713.
Lemma F_3c010 : fetch_word Plain.M.loaded_segments (0x3c010 : word) = Some W_3c010.
Proof. vm_refl. Qed.
Lemma D_3c010 : decode_any W_3c010 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c014 : bv 32 := 0x00154783.
Lemma F_3c014 : fetch_word Plain.M.loaded_segments (0x3c014 : word) = Some W_3c014.
Proof. vm_refl. Qed.
Lemma D_3c014 : decode_any W_3c014 = Some (Load SZ1 false 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c018 : bv 32 := 0x00254803.
Lemma F_3c018 : fetch_word Plain.M.loaded_segments (0x3c018 : word) = Some W_3c018.
Proof. vm_refl. Qed.
Lemma D_3c018 : decode_any W_3c018 = Some (Load SZ1 false 16 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c01c : bv 32 := 0x00354883.
Lemma F_3c01c : fetch_word Plain.M.loaded_segments (0x3c01c : word) = Some W_3c01c.
Proof. vm_refl. Qed.
Lemma D_3c01c : decode_any W_3c01c = Some (Load SZ1 false 17 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c020 : bv 32 := 0x00054283.
Lemma F_3c020 : fetch_word Plain.M.loaded_segments (0x3c020 : word) = Some W_3c020.
Proof. vm_refl. Qed.
Lemma D_3c020 : decode_any W_3c020 = Some (Load SZ1 false 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c024 : bv 32 := 0x00879793.
Lemma F_3c024 : fetch_word Plain.M.loaded_segments (0x3c024 : word) = Some W_3c024.
Proof. vm_refl. Qed.
Lemma D_3c024 : decode_any W_3c024 = Some (ShiftImm ALU_SLL 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c028 : bv 32 := 0x01081813.
Lemma F_3c028 : fetch_word Plain.M.loaded_segments (0x3c028 : word) = Some W_3c028.
Proof. vm_refl. Qed.
Lemma D_3c028 : decode_any W_3c028 = Some (ShiftImm ALU_SLL 16 16 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c02c : bv 32 := 0x0188989b.
Lemma F_3c02c : fetch_word Plain.M.loaded_segments (0x3c02c : word) = Some W_3c02c.
Proof. vm_refl. Qed.
Lemma D_3c02c : decode_any W_3c02c = Some (ShiftImm32 ALU_SLL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c030 : bv 32 := 0x0057e7b3.
Lemma F_3c030 : fetch_word Plain.M.loaded_segments (0x3c030 : word) = Some W_3c030.
Proof. vm_refl. Qed.
Lemma D_3c030 : decode_any W_3c030 = Some (Op ALU_OR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c034 : bv 32 := 0x00064283.
Lemma F_3c034 : fetch_word Plain.M.loaded_segments (0x3c034 : word) = Some W_3c034.
Proof. vm_refl. Qed.
Lemma D_3c034 : decode_any W_3c034 = Some (Load SZ1 false 5 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c038 : bv 32 := 0x00164303.
Lemma F_3c038 : fetch_word Plain.M.loaded_segments (0x3c038 : word) = Some W_3c038.
Proof. vm_refl. Qed.
Lemma D_3c038 : decode_any W_3c038 = Some (Load SZ1 false 6 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c03c : bv 32 := 0x01186833.
Lemma F_3c03c : fetch_word Plain.M.loaded_segments (0x3c03c : word) = Some W_3c03c.
Proof. vm_refl. Qed.
Lemma D_3c03c : decode_any W_3c03c = Some (Op ALU_OR 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c040 : bv 32 := 0x00264883.
Lemma F_3c040 : fetch_word Plain.M.loaded_segments (0x3c040 : word) = Some W_3c040.
Proof. vm_refl. Qed.
Lemma D_3c040 : decode_any W_3c040 = Some (Load SZ1 false 17 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c044 : bv 32 := 0x00364383.
Lemma F_3c044 : fetch_word Plain.M.loaded_segments (0x3c044 : word) = Some W_3c044.
Proof. vm_refl. Qed.
Lemma D_3c044 : decode_any W_3c044 = Some (Load SZ1 false 7 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c048 : bv 32 := 0x00831313.
Lemma F_3c048 : fetch_word Plain.M.loaded_segments (0x3c048 : word) = Some W_3c048.
Proof. vm_refl. Qed.
Lemma D_3c048 : decode_any W_3c048 = Some (ShiftImm ALU_SLL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c04c : bv 32 := 0x005362b3.
Lemma F_3c04c : fetch_word Plain.M.loaded_segments (0x3c04c : word) = Some W_3c04c.
Proof. vm_refl. Qed.
Lemma D_3c04c : decode_any W_3c04c = Some (Op ALU_OR 5 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c050 : bv 32 := 0x01089893.
Lemma F_3c050 : fetch_word Plain.M.loaded_segments (0x3c050 : word) = Some W_3c050.
Proof. vm_refl. Qed.
Lemma D_3c050 : decode_any W_3c050 = Some (ShiftImm ALU_SLL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c054 : bv 32 := 0x0183931b.
Lemma F_3c054 : fetch_word Plain.M.loaded_segments (0x3c054 : word) = Some W_3c054.
Proof. vm_refl. Qed.
Lemma D_3c054 : decode_any W_3c054 = Some (ShiftImm32 ALU_SLL 6 7 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c058 : bv 32 := 0x0068e8b3.
Lemma F_3c058 : fetch_word Plain.M.loaded_segments (0x3c058 : word) = Some W_3c058.
Proof. vm_refl. Qed.
Lemma D_3c058 : decode_any W_3c058 = Some (Op ALU_OR 17 17 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c05c : bv 32 := 0x0107e7b3.
Lemma F_3c05c : fetch_word Plain.M.loaded_segments (0x3c05c : word) = Some W_3c05c.
Proof. vm_refl. Qed.
Lemma D_3c05c : decode_any W_3c05c = Some (Op ALU_OR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c060 : bv 32 := 0x0112e833.
Lemma F_3c060 : fetch_word Plain.M.loaded_segments (0x3c060 : word) = Some W_3c060.
Proof. vm_refl. Qed.
Lemma D_3c060 : decode_any W_3c060 = Some (Op ALU_OR 16 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c064 : bv 32 := 0x00f847b3.
Lemma F_3c064 : fetch_word Plain.M.loaded_segments (0x3c064 : word) = Some W_3c064.
Proof. vm_refl. Qed.
Lemma D_3c064 : decode_any W_3c064 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c068 : bv 32 := 0x00d7f7b3.
Lemma F_3c068 : fetch_word Plain.M.loaded_segments (0x3c068 : word) = Some W_3c068.
Proof. vm_refl. Qed.
Lemma D_3c068 : decode_any W_3c068 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c06c : bv 32 := 0x04079663.
Lemma F_3c06c : fetch_word Plain.M.loaded_segments (0x3c06c : word) = Some W_3c06c.
Proof. vm_refl. Qed.
Lemma D_3c06c : decode_any W_3c06c = Some (Branch BC_NE 15 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c070 : bv 32 := 0x00450513.
Lemma F_3c070 : fetch_word Plain.M.loaded_segments (0x3c070 : word) = Some W_3c070.
Proof. vm_refl. Qed.
Lemma D_3c070 : decode_any W_3c070 = Some (OpImm ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c074 : bv 32 := 0xffc58593.
Lemma F_3c074 : fetch_word Plain.M.loaded_segments (0x3c074 : word) = Some W_3c074.
Proof. vm_refl. Qed.
Lemma D_3c074 : decode_any W_3c074 = Some (OpImm ALU_ADD 11 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c078 : bv 32 := 0x00460613.
Lemma F_3c078 : fetch_word Plain.M.loaded_segments (0x3c078 : word) = Some W_3c078.
Proof. vm_refl. Qed.
Lemma D_3c078 : decode_any W_3c078 = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c07c : bv 32 := 0xf8b76ce3.
Lemma F_3c07c : fetch_word Plain.M.loaded_segments (0x3c07c : word) = Some W_3c07c.
Proof. vm_refl. Qed.
Lemma D_3c07c : decode_any W_3c07c = Some (Branch BC_LTU 14 11 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c080 : bv 32 := 0x04058263.
Lemma F_3c080 : fetch_word Plain.M.loaded_segments (0x3c080 : word) = Some W_3c080.
Proof. vm_refl. Qed.
Lemma D_3c080 : decode_any W_3c080 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c084 : bv 32 := 0xfff58693.
Lemma F_3c084 : fetch_word Plain.M.loaded_segments (0x3c084 : word) = Some W_3c084.
Proof. vm_refl. Qed.
Lemma D_3c084 : decode_any W_3c084 = Some (OpImm ALU_ADD 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c088 : bv 32 := 0x00054583.
Lemma F_3c088 : fetch_word Plain.M.loaded_segments (0x3c088 : word) = Some W_3c088.
Proof. vm_refl. Qed.
Lemma D_3c088 : decode_any W_3c088 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c08c : bv 32 := 0x00064703.
Lemma F_3c08c : fetch_word Plain.M.loaded_segments (0x3c08c : word) = Some W_3c08c.
Proof. vm_refl. Qed.
Lemma D_3c08c : decode_any W_3c08c = Some (Load SZ1 false 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c090 : bv 32 := 0x00b745b3.
Lemma F_3c090 : fetch_word Plain.M.loaded_segments (0x3c090 : word) = Some W_3c090.
Proof. vm_refl. Qed.
Lemma D_3c090 : decode_any W_3c090 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c094 : bv 32 := 0x0df5f713.
Lemma F_3c094 : fetch_word Plain.M.loaded_segments (0x3c094 : word) = Some W_3c094.
Proof. vm_refl. Qed.
Lemma D_3c094 : decode_any W_3c094 = Some (OpImm ALU_AND 14 11 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c098 : bv 32 := 0x00173593.
Lemma F_3c098 : fetch_word Plain.M.loaded_segments (0x3c098 : word) = Some W_3c098.
Proof. vm_refl. Qed.
Lemma D_3c098 : decode_any W_3c098 = Some (OpImm ALU_SLTU 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c09c : bv 32 := 0x02071063.
Lemma F_3c09c : fetch_word Plain.M.loaded_segments (0x3c09c : word) = Some W_3c09c.
Proof. vm_refl. Qed.
Lemma D_3c09c : decode_any W_3c09c = Some (Branch BC_NE 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0a0 : bv 32 := 0x00150513.
Lemma F_3c0a0 : fetch_word Plain.M.loaded_segments (0x3c0a0 : word) = Some W_3c0a0.
Proof. vm_refl. Qed.
Lemma D_3c0a0 : decode_any W_3c0a0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0a4 : bv 32 := 0x00d03733.
Lemma F_3c0a4 : fetch_word Plain.M.loaded_segments (0x3c0a4 : word) = Some W_3c0a4.
Proof. vm_refl. Qed.
Lemma D_3c0a4 : decode_any W_3c0a4 = Some (Op ALU_SLTU 14 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0a8 : bv 32 := 0xfff68693.
Lemma F_3c0a8 : fetch_word Plain.M.loaded_segments (0x3c0a8 : word) = Some W_3c0a8.
Proof. vm_refl. Qed.
Lemma D_3c0a8 : decode_any W_3c0a8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0ac : bv 32 := 0x00160613.
Lemma F_3c0ac : fetch_word Plain.M.loaded_segments (0x3c0ac : word) = Some W_3c0ac.
Proof. vm_refl. Qed.
Lemma D_3c0ac : decode_any W_3c0ac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0b0 : bv 32 := 0x00070663.
Lemma F_3c0b0 : fetch_word Plain.M.loaded_segments (0x3c0b0 : word) = Some W_3c0b0.
Proof. vm_refl. Qed.
Lemma D_3c0b0 : decode_any W_3c0b0 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0b4 : bv 32 := 0xfd5ff06f.
Lemma F_3c0b4 : fetch_word Plain.M.loaded_segments (0x3c0b4 : word) = Some W_3c0b4.
Proof. vm_refl. Qed.
Lemma D_3c0b4 : decode_any W_3c0b4 = Some (Jal 0 2097108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0b8 : bv 32 := 0x00000593.
Lemma F_3c0b8 : fetch_word Plain.M.loaded_segments (0x3c0b8 : word) = Some W_3c0b8.
Proof. vm_refl. Qed.
Lemma D_3c0b8 : decode_any W_3c0b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0bc : bv 32 := 0x00058513.
Lemma F_3c0bc : fetch_word Plain.M.loaded_segments (0x3c0bc : word) = Some W_3c0bc.
Proof. vm_refl. Qed.
Lemma D_3c0bc : decode_any W_3c0bc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0c0 : bv 32 := 0x00008067.
Lemma F_3c0c0 : fetch_word Plain.M.loaded_segments (0x3c0c0 : word) = Some W_3c0c0.
Proof. vm_refl. Qed.
Lemma D_3c0c0 : decode_any W_3c0c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0c4 : bv 32 := 0x00100593.
Lemma F_3c0c4 : fetch_word Plain.M.loaded_segments (0x3c0c4 : word) = Some W_3c0c4.
Proof. vm_refl. Qed.
Lemma D_3c0c4 : decode_any W_3c0c4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0c8 : bv 32 := 0xff5ff06f.
Lemma F_3c0c8 : fetch_word Plain.M.loaded_segments (0x3c0c8 : word) = Some W_3c0c8.
Proof. vm_refl. Qed.
Lemma D_3c0c8 : decode_any W_3c0c8 = Some (Jal 0 2097140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0cc : bv 32 := 0xfc010113.
Lemma F_3c0cc : fetch_word Plain.M.loaded_segments (0x3c0cc : word) = Some W_3c0cc.
Proof. vm_refl. Qed.
Lemma D_3c0cc : decode_any W_3c0cc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0d0 : bv 32 := 0x02113c23.
Lemma F_3c0d0 : fetch_word Plain.M.loaded_segments (0x3c0d0 : word) = Some W_3c0d0.
Proof. vm_refl. Qed.
Lemma D_3c0d0 : decode_any W_3c0d0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0d4 : bv 32 := 0x02813823.
Lemma F_3c0d4 : fetch_word Plain.M.loaded_segments (0x3c0d4 : word) = Some W_3c0d4.
Proof. vm_refl. Qed.
Lemma D_3c0d4 : decode_any W_3c0d4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0d8 : bv 32 := 0x02913423.
Lemma F_3c0d8 : fetch_word Plain.M.loaded_segments (0x3c0d8 : word) = Some W_3c0d8.
Proof. vm_refl. Qed.
Lemma D_3c0d8 : decode_any W_3c0d8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0dc : bv 32 := 0x00050413.
Lemma F_3c0dc : fetch_word Plain.M.loaded_segments (0x3c0dc : word) = Some W_3c0dc.
Proof. vm_refl. Qed.
Lemma D_3c0dc : decode_any W_3c0dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0e0 : bv 32 := 0x00053503.
Lemma F_3c0e0 : fetch_word Plain.M.loaded_segments (0x3c0e0 : word) = Some W_3c0e0.
Proof. vm_refl. Qed.
Lemma D_3c0e0 : decode_any W_3c0e0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0e4 : bv 32 := 0x00813023.
Lemma F_3c0e4 : fetch_word Plain.M.loaded_segments (0x3c0e4 : word) = Some W_3c0e4.
Proof. vm_refl. Qed.
Lemma D_3c0e4 : decode_any W_3c0e4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0e8 : bv 32 := 0x00a13423.
Lemma F_3c0e8 : fetch_word Plain.M.loaded_segments (0x3c0e8 : word) = Some W_3c0e8.
Proof. vm_refl. Qed.
Lemma D_3c0e8 : decode_any W_3c0e8 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0ec : bv 32 := 0x00013823.
Lemma F_3c0ec : fetch_word Plain.M.loaded_segments (0x3c0ec : word) = Some W_3c0ec.
Proof. vm_refl. Qed.
Lemma D_3c0ec : decode_any W_3c0ec = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0f0 : bv 32 := 0x00013c23.
Lemma F_3c0f0 : fetch_word Plain.M.loaded_segments (0x3c0f0 : word) = Some W_3c0f0.
Proof. vm_refl. Qed.
Lemma D_3c0f0 : decode_any W_3c0f0 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0f4 : bv 32 := 0x02010023.
Lemma F_3c0f4 : fetch_word Plain.M.loaded_segments (0x3c0f4 : word) = Some W_3c0f4.
Proof. vm_refl. Qed.
Lemma D_3c0f4 : decode_any W_3c0f4 = Some (Store SZ1 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0f8 : bv 32 := 0x00010513.
Lemma F_3c0f8 : fetch_word Plain.M.loaded_segments (0x3c0f8 : word) = Some W_3c0f8.
Proof. vm_refl. Qed.
Lemma D_3c0f8 : decode_any W_3c0f8 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c0fc : bv 32 := 0x0c0000ef.
Lemma F_3c0fc : fetch_word Plain.M.loaded_segments (0x3c0fc : word) = Some W_3c0fc.
Proof. vm_refl. Qed.
Lemma D_3c0fc : decode_any W_3c0fc = Some (Jal 1 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c100 : bv 32 := 0x02014503.
Lemma F_3c100 : fetch_word Plain.M.loaded_segments (0x3c100 : word) = Some W_3c100.
Proof. vm_refl. Qed.
Lemma D_3c100 : decode_any W_3c100 = Some (Load SZ1 false 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c104 : bv 32 := 0x02050063.
Lemma F_3c104 : fetch_word Plain.M.loaded_segments (0x3c104 : word) = Some W_3c104.
Proof. vm_refl. Qed.
Lemma D_3c104 : decode_any W_3c104 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c108 : bv 32 := 0x00000493.
Lemma F_3c108 : fetch_word Plain.M.loaded_segments (0x3c108 : word) = Some W_3c108.
Proof. vm_refl. Qed.
Lemma D_3c108 : decode_any W_3c108 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c10c : bv 32 := 0x00048513.
Lemma F_3c10c : fetch_word Plain.M.loaded_segments (0x3c10c : word) = Some W_3c10c.
Proof. vm_refl. Qed.
Lemma D_3c10c : decode_any W_3c10c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c110 : bv 32 := 0x03813083.
Lemma F_3c110 : fetch_word Plain.M.loaded_segments (0x3c110 : word) = Some W_3c110.
Proof. vm_refl. Qed.
Lemma D_3c110 : decode_any W_3c110 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c114 : bv 32 := 0x03013403.
Lemma F_3c114 : fetch_word Plain.M.loaded_segments (0x3c114 : word) = Some W_3c114.
Proof. vm_refl. Qed.
Lemma D_3c114 : decode_any W_3c114 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c118 : bv 32 := 0x02813483.
Lemma F_3c118 : fetch_word Plain.M.loaded_segments (0x3c118 : word) = Some W_3c118.
Proof. vm_refl. Qed.
Lemma D_3c118 : decode_any W_3c118 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c11c : bv 32 := 0x04010113.
Lemma F_3c11c : fetch_word Plain.M.loaded_segments (0x3c11c : word) = Some W_3c11c.
Proof. vm_refl. Qed.
Lemma D_3c11c : decode_any W_3c11c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c120 : bv 32 := 0x00008067.
Lemma F_3c120 : fetch_word Plain.M.loaded_segments (0x3c120 : word) = Some W_3c120.
Proof. vm_refl. Qed.
Lemma D_3c120 : decode_any W_3c120 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c124 : bv 32 := 0x00013583.
Lemma F_3c124 : fetch_word Plain.M.loaded_segments (0x3c124 : word) = Some W_3c124.
Proof. vm_refl. Qed.
Lemma D_3c124 : decode_any W_3c124 = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c128 : bv 32 := 0x00813503.
Lemma F_3c128 : fetch_word Plain.M.loaded_segments (0x3c128 : word) = Some W_3c128.
Proof. vm_refl. Qed.
Lemma D_3c128 : decode_any W_3c128 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c12c : bv 32 := 0x00100493.
Lemma F_3c12c : fetch_word Plain.M.loaded_segments (0x3c12c : word) = Some W_3c12c.
Proof. vm_refl. Qed.
Lemma D_3c12c : decode_any W_3c12c = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c130 : bv 32 := 0x00b41463.
Lemma F_3c130 : fetch_word Plain.M.loaded_segments (0x3c130 : word) = Some W_3c130.
Proof. vm_refl. Qed.
Lemma D_3c130 : decode_any W_3c130 = Some (Branch BC_NE 8 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c134 : bv 32 := 0xfc050ce3.
Lemma F_3c134 : fetch_word Plain.M.loaded_segments (0x3c134 : word) = Some W_3c134.
Proof. vm_refl. Qed.
Lemma D_3c134 : decode_any W_3c134 = Some (Branch BC_EQ 10 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c138 : bv 32 := 0x00010513.
Lemma F_3c138 : fetch_word Plain.M.loaded_segments (0x3c138 : word) = Some W_3c138.
Proof. vm_refl. Qed.
Lemma D_3c138 : decode_any W_3c138 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c13c : bv 32 := 0x080000ef.
Lemma F_3c13c : fetch_word Plain.M.loaded_segments (0x3c13c : word) = Some W_3c13c.
Proof. vm_refl. Qed.
Lemma D_3c13c : decode_any W_3c13c = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c140 : bv 32 := 0x02014503.
Lemma F_3c140 : fetch_word Plain.M.loaded_segments (0x3c140 : word) = Some W_3c140.
Proof. vm_refl. Qed.
Lemma D_3c140 : decode_any W_3c140 = Some (Load SZ1 false 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c144 : bv 32 := 0xfc0512e3.
Lemma F_3c144 : fetch_word Plain.M.loaded_segments (0x3c144 : word) = Some W_3c144.
Proof. vm_refl. Qed.
Lemma D_3c144 : decode_any W_3c144 = Some (Branch BC_NE 10 0 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c148 : bv 32 := 0x00013583.
Lemma F_3c148 : fetch_word Plain.M.loaded_segments (0x3c148 : word) = Some W_3c148.
Proof. vm_refl. Qed.
Lemma D_3c148 : decode_any W_3c148 = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c14c : bv 32 := 0x00813503.
Lemma F_3c14c : fetch_word Plain.M.loaded_segments (0x3c14c : word) = Some W_3c14c.
Proof. vm_refl. Qed.
Lemma D_3c14c : decode_any W_3c14c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c150 : bv 32 := 0xfcb41ee3.
Lemma F_3c150 : fetch_word Plain.M.loaded_segments (0x3c150 : word) = Some W_3c150.
Proof. vm_refl. Qed.
Lemma D_3c150 : decode_any W_3c150 = Some (Branch BC_NE 8 11 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c154 : bv 32 := 0xfc051ce3.
Lemma F_3c154 : fetch_word Plain.M.loaded_segments (0x3c154 : word) = Some W_3c154.
Proof. vm_refl. Qed.
Lemma D_3c154 : decode_any W_3c154 = Some (Branch BC_NE 10 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c158 : bv 32 := 0xfb5ff06f.
Lemma F_3c158 : fetch_word Plain.M.loaded_segments (0x3c158 : word) = Some W_3c158.
Proof. vm_refl. Qed.
Lemma D_3c158 : decode_any W_3c158 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c15c : bv 32 := 0xfd010113.
Lemma F_3c15c : fetch_word Plain.M.loaded_segments (0x3c15c : word) = Some W_3c15c.
Proof. vm_refl. Qed.
Lemma D_3c15c : decode_any W_3c15c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c160 : bv 32 := 0x02113423.
Lemma F_3c160 : fetch_word Plain.M.loaded_segments (0x3c160 : word) = Some W_3c160.
Proof. vm_refl. Qed.
Lemma D_3c160 : decode_any W_3c160 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c164 : bv 32 := 0x02813023.
Lemma F_3c164 : fetch_word Plain.M.loaded_segments (0x3c164 : word) = Some W_3c164.
Proof. vm_refl. Qed.
Lemma D_3c164 : decode_any W_3c164 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c168 : bv 32 := 0x00053403.
Lemma F_3c168 : fetch_word Plain.M.loaded_segments (0x3c168 : word) = Some W_3c168.
Proof. vm_refl. Qed.
Lemma D_3c168 : decode_any W_3c168 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c16c : bv 32 := 0x00810513.
Lemma F_3c16c : fetch_word Plain.M.loaded_segments (0x3c16c : word) = Some W_3c16c.
Proof. vm_refl. Qed.
Lemma D_3c16c : decode_any W_3c16c = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c170 : bv 32 := 0x01300593.
Lemma F_3c170 : fetch_word Plain.M.loaded_segments (0x3c170 : word) = Some W_3c170.
Proof. vm_refl. Qed.
Lemma D_3c170 : decode_any W_3c170 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c174 : bv 32 := 0x00000613.
Lemma F_3c174 : fetch_word Plain.M.loaded_segments (0x3c174 : word) = Some W_3c174.
Proof. vm_refl. Qed.
Lemma D_3c174 : decode_any W_3c174 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c178 : bv 32 := 0xa54f60ef.
Lemma F_3c178 : fetch_word Plain.M.loaded_segments (0x3c178 : word) = Some W_3c178.
Proof. vm_refl. Qed.
Lemma D_3c178 : decode_any W_3c178 = Some (Jal 1 2056788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c17c : bv 32 := 0x01813503.
Lemma F_3c17c : fetch_word Plain.M.loaded_segments (0x3c17c : word) = Some W_3c17c.
Proof. vm_refl. Qed.
Lemma D_3c17c : decode_any W_3c17c = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c180 : bv 32 := 0x00200593.
Lemma F_3c180 : fetch_word Plain.M.loaded_segments (0x3c180 : word) = Some W_3c180.
Proof. vm_refl. Qed.
Lemma D_3c180 : decode_any W_3c180 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c184 : bv 32 := 0x00b56a63.
Lemma F_3c184 : fetch_word Plain.M.loaded_segments (0x3c184 : word) = Some W_3c184.
Proof. vm_refl. Qed.
Lemma D_3c184 : decode_any W_3c184 = Some (Branch BC_LTU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c188 : bv 32 := 0x00157513.
Lemma F_3c188 : fetch_word Plain.M.loaded_segments (0x3c188 : word) = Some W_3c188.
Proof. vm_refl. Qed.
Lemma D_3c188 : decode_any W_3c188 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c18c : bv 32 := 0x00040597.
Lemma F_3c18c : fetch_word Plain.M.loaded_segments (0x3c18c : word) = Some W_3c18c.
Proof. vm_refl. Qed.
Lemma D_3c18c : decode_any W_3c18c = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c190 : bv 32 := 0xf8458593.
Lemma F_3c190 : fetch_word Plain.M.loaded_segments (0x3c190 : word) = Some W_3c190.
Proof. vm_refl. Qed.
Lemma D_3c190 : decode_any W_3c190 = Some (OpImm ALU_ADD 11 11 3972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c194 : bv 32 := 0x00b56533.
Lemma F_3c194 : fetch_word Plain.M.loaded_segments (0x3c194 : word) = Some W_3c194.
Proof. vm_refl. Qed.
Lemma D_3c194 : decode_any W_3c194 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c198 : bv 32 := 0x00813583.
Lemma F_3c198 : fetch_word Plain.M.loaded_segments (0x3c198 : word) = Some W_3c198.
Proof. vm_refl. Qed.
Lemma D_3c198 : decode_any W_3c198 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c19c : bv 32 := 0x01013603.
Lemma F_3c19c : fetch_word Plain.M.loaded_segments (0x3c19c : word) = Some W_3c19c.
Proof. vm_refl. Qed.
Lemma D_3c19c : decode_any W_3c19c = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1a0 : bv 32 := 0x00b43023.
Lemma F_3c1a0 : fetch_word Plain.M.loaded_segments (0x3c1a0 : word) = Some W_3c1a0.
Proof. vm_refl. Qed.
Lemma D_3c1a0 : decode_any W_3c1a0 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1a4 : bv 32 := 0x00c43423.
Lemma F_3c1a4 : fetch_word Plain.M.loaded_segments (0x3c1a4 : word) = Some W_3c1a4.
Proof. vm_refl. Qed.
Lemma D_3c1a4 : decode_any W_3c1a4 = Some (Store SZ8 8 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1a8 : bv 32 := 0x00a43823.
Lemma F_3c1a8 : fetch_word Plain.M.loaded_segments (0x3c1a8 : word) = Some W_3c1a8.
Proof. vm_refl. Qed.
Lemma D_3c1a8 : decode_any W_3c1a8 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1ac : bv 32 := 0x02813083.
Lemma F_3c1ac : fetch_word Plain.M.loaded_segments (0x3c1ac : word) = Some W_3c1ac.
Proof. vm_refl. Qed.
Lemma D_3c1ac : decode_any W_3c1ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1b0 : bv 32 := 0x02013403.
Lemma F_3c1b0 : fetch_word Plain.M.loaded_segments (0x3c1b0 : word) = Some W_3c1b0.
Proof. vm_refl. Qed.
Lemma D_3c1b0 : decode_any W_3c1b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1b4 : bv 32 := 0x03010113.
Lemma F_3c1b4 : fetch_word Plain.M.loaded_segments (0x3c1b4 : word) = Some W_3c1b4.
Proof. vm_refl. Qed.
Lemma D_3c1b4 : decode_any W_3c1b4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1b8 : bv 32 := 0x00008067.
Lemma F_3c1b8 : fetch_word Plain.M.loaded_segments (0x3c1b8 : word) = Some W_3c1b8.
Proof. vm_refl. Qed.
Lemma D_3c1b8 : decode_any W_3c1b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1bc : bv 32 := 0x00053603.
Lemma F_3c1bc : fetch_word Plain.M.loaded_segments (0x3c1bc : word) = Some W_3c1bc.
Proof. vm_refl. Qed.
Lemma D_3c1bc : decode_any W_3c1bc = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1c0 : bv 32 := 0x00853583.
Lemma F_3c1c0 : fetch_word Plain.M.loaded_segments (0x3c1c0 : word) = Some W_3c1c0.
Proof. vm_refl. Qed.
Lemma D_3c1c0 : decode_any W_3c1c0 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1c4 : bv 32 := 0xfffd9697.
Lemma F_3c1c4 : fetch_word Plain.M.loaded_segments (0x3c1c4 : word) = Some W_3c1c4.
Proof. vm_refl. Qed.
Lemma D_3c1c4 : decode_any W_3c1c4 = Some (Auipc 13 1048537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1c8 : bv 32 := 0x02c00713.
Lemma F_3c1c8 : fetch_word Plain.M.loaded_segments (0x3c1c8 : word) = Some W_3c1c8.
Proof. vm_refl. Qed.
Lemma D_3c1c8 : decode_any W_3c1c8 = Some (OpImm ALU_ADD 14 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1cc : bv 32 := 0x02000793.
Lemma F_3c1cc : fetch_word Plain.M.loaded_segments (0x3c1cc : word) = Some W_3c1cc.
Proof. vm_refl. Qed.
Lemma D_3c1cc : decode_any W_3c1cc = Some (OpImm ALU_ADD 15 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1d0 : bv 32 := 0x52668693.
Lemma F_3c1d0 : fetch_word Plain.M.loaded_segments (0x3c1d0 : word) = Some W_3c1d0.
Proof. vm_refl. Qed.
Lemma D_3c1d0 : decode_any W_3c1d0 = Some (OpImm ALU_ADD 13 13 1318, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1d4 : bv 32 := 0x00063803.
Lemma F_3c1d4 : fetch_word Plain.M.loaded_segments (0x3c1d4 : word) = Some W_3c1d4.
Proof. vm_refl. Qed.
Lemma D_3c1d4 : decode_any W_3c1d4 = Some (Load SZ8 true 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1d8 : bv 32 := 0x00863603.
Lemma F_3c1d8 : fetch_word Plain.M.loaded_segments (0x3c1d8 : word) = Some W_3c1d8.
Proof. vm_refl. Qed.
Lemma D_3c1d8 : decode_any W_3c1d8 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1dc : bv 32 := 0x00053823.
Lemma F_3c1dc : fetch_word Plain.M.loaded_segments (0x3c1dc : word) = Some W_3c1dc.
Proof. vm_refl. Qed.
Lemma D_3c1dc : decode_any W_3c1dc = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1e0 : bv 32 := 0x00053c23.
Lemma F_3c1e0 : fetch_word Plain.M.loaded_segments (0x3c1e0 : word) = Some W_3c1e0.
Proof. vm_refl. Qed.
Lemma D_3c1e0 : decode_any W_3c1e0 = Some (Store SZ8 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1e4 : bv 32 := 0x0105c8b3.
Lemma F_3c1e4 : fetch_word Plain.M.loaded_segments (0x3c1e4 : word) = Some W_3c1e4.
Proof. vm_refl. Qed.
Lemma D_3c1e4 : decode_any W_3c1e4 = Some (Op ALU_XOR 17 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1e8 : bv 32 := 0x00c80633.
Lemma F_3c1e8 : fetch_word Plain.M.loaded_segments (0x3c1e8 : word) = Some W_3c1e8.
Proof. vm_refl. Qed.
Lemma D_3c1e8 : decode_any W_3c1e8 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1ec : bv 32 := 0x011038b3.
Lemma F_3c1ec : fetch_word Plain.M.loaded_segments (0x3c1ec : word) = Some W_3c1ec.
Proof. vm_refl. Qed.
Lemma D_3c1ec : decode_any W_3c1ec = Some (Op ALU_SLTU 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1f0 : bv 32 := 0x00900813.
Lemma F_3c1f0 : fetch_word Plain.M.loaded_segments (0x3c1f0 : word) = Some W_3c1f0.
Proof. vm_refl. Qed.
Lemma D_3c1f0 : decode_any W_3c1f0 = Some (OpImm ALU_ADD 16 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1f4 : bv 32 := 0x00c58e63.
Lemma F_3c1f4 : fetch_word Plain.M.loaded_segments (0x3c1f4 : word) = Some W_3c1f4.
Proof. vm_refl. Qed.
Lemma D_3c1f4 : decode_any W_3c1f4 = Some (Branch BC_EQ 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1f8 : bv 32 := 0x0005c283.
Lemma F_3c1f8 : fetch_word Plain.M.loaded_segments (0x3c1f8 : word) = Some W_3c1f8.
Proof. vm_refl. Qed.
Lemma D_3c1f8 : decode_any W_3c1f8 = Some (Load SZ1 false 5 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1fc : bv 32 := 0x00f28463.
Lemma F_3c1fc : fetch_word Plain.M.loaded_segments (0x3c1fc : word) = Some W_3c1fc.
Proof. vm_refl. Qed.
Lemma D_3c1fc : decode_any W_3c1fc = Some (Branch BC_EQ 5 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c200 : bv 32 := 0x01029863.
Lemma F_3c200 : fetch_word Plain.M.loaded_segments (0x3c200 : word) = Some W_3c200.
Proof. vm_refl. Qed.
Lemma D_3c200 : decode_any W_3c200 = Some (Branch BC_NE 5 16 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c204 : bv 32 := 0x00158593.
Lemma F_3c204 : fetch_word Plain.M.loaded_segments (0x3c204 : word) = Some W_3c204.
Proof. vm_refl. Qed.
Lemma D_3c204 : decode_any W_3c204 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c208 : bv 32 := 0x00b53423.
Lemma F_3c208 : fetch_word Plain.M.loaded_segments (0x3c208 : word) = Some W_3c208.
Proof. vm_refl. Qed.
Lemma D_3c208 : decode_any W_3c208 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c20c : bv 32 := 0xfec596e3.
Lemma F_3c20c : fetch_word Plain.M.loaded_segments (0x3c20c : word) = Some W_3c20c.
Proof. vm_refl. Qed.
Lemma D_3c20c : decode_any W_3c20c = Some (Branch BC_NE 11 12 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c210 : bv 32 := 0x02c58663.
Lemma F_3c210 : fetch_word Plain.M.loaded_segments (0x3c210 : word) = Some W_3c210.
Proof. vm_refl. Qed.
Lemma D_3c210 : decode_any W_3c210 = Some (Branch BC_EQ 11 12 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c214 : bv 32 := 0x0005c283.
Lemma F_3c214 : fetch_word Plain.M.loaded_segments (0x3c214 : word) = Some W_3c214.
Proof. vm_refl. Qed.
Lemma D_3c214 : decode_any W_3c214 = Some (Load SZ1 false 5 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c218 : bv 32 := 0x00568333.
Lemma F_3c218 : fetch_word Plain.M.loaded_segments (0x3c218 : word) = Some W_3c218.
Proof. vm_refl. Qed.
Lemma D_3c218 : decode_any W_3c218 = Some (Op ALU_ADD 6 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c21c : bv 32 := 0x00034303.
Lemma F_3c21c : fetch_word Plain.M.loaded_segments (0x3c21c : word) = Some W_3c21c.
Proof. vm_refl. Qed.
Lemma D_3c21c : decode_any W_3c21c = Some (Load SZ1 false 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c220 : bv 32 := 0x02031263.
Lemma F_3c220 : fetch_word Plain.M.loaded_segments (0x3c220 : word) = Some W_3c220.
Proof. vm_refl. Qed.
Lemma D_3c220 : decode_any W_3c220 = Some (Branch BC_NE 6 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c224 : bv 32 := 0x02e29463.
Lemma F_3c224 : fetch_word Plain.M.loaded_segments (0x3c224 : word) = Some W_3c224.
Proof. vm_refl. Qed.
Lemma D_3c224 : decode_any W_3c224 = Some (Branch BC_NE 5 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c228 : bv 32 := 0x00000893.
Lemma F_3c228 : fetch_word Plain.M.loaded_segments (0x3c228 : word) = Some W_3c228.
Proof. vm_refl. Qed.
Lemma D_3c228 : decode_any W_3c228 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c22c : bv 32 := 0x00158593.
Lemma F_3c22c : fetch_word Plain.M.loaded_segments (0x3c22c : word) = Some W_3c22c.
Proof. vm_refl. Qed.
Lemma D_3c22c : decode_any W_3c22c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c230 : bv 32 := 0x00b53423.
Lemma F_3c230 : fetch_word Plain.M.loaded_segments (0x3c230 : word) = Some W_3c230.
Proof. vm_refl. Qed.
Lemma D_3c230 : decode_any W_3c230 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c234 : bv 32 := 0xfcc592e3.
Lemma F_3c234 : fetch_word Plain.M.loaded_segments (0x3c234 : word) = Some W_3c234.
Proof. vm_refl. Qed.
Lemma D_3c234 : decode_any W_3c234 = Some (Branch BC_NE 11 12 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c238 : bv 32 := 0xfd9ff06f.
Lemma F_3c238 : fetch_word Plain.M.loaded_segments (0x3c238 : word) = Some W_3c238.
Proof. vm_refl. Qed.
Lemma D_3c238 : decode_any W_3c238 = Some (Jal 0 2097112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c23c : bv 32 := 0x00053423.
Lemma F_3c23c : fetch_word Plain.M.loaded_segments (0x3c23c : word) = Some W_3c23c.
Proof. vm_refl. Qed.
Lemma D_3c23c : decode_any W_3c23c = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c240 : bv 32 := 0x00008067.
Lemma F_3c240 : fetch_word Plain.M.loaded_segments (0x3c240 : word) = Some W_3c240.
Proof. vm_refl. Qed.
Lemma D_3c240 : decode_any W_3c240 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c244 : bv 32 := 0x0018f713.
Lemma F_3c244 : fetch_word Plain.M.loaded_segments (0x3c244 : word) = Some W_3c244.
Proof. vm_refl. Qed.
Lemma D_3c244 : decode_any W_3c244 = Some (OpImm ALU_AND 14 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c248 : bv 32 := 0x00070a63.
Lemma F_3c248 : fetch_word Plain.M.loaded_segments (0x3c248 : word) = Some W_3c248.
Proof. vm_refl. Qed.
Lemma D_3c248 : decode_any W_3c248 = Some (Branch BC_EQ 14 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c24c : bv 32 := 0x00100593.
Lemma F_3c24c : fetch_word Plain.M.loaded_segments (0x3c24c : word) = Some W_3c24c.
Proof. vm_refl. Qed.
Lemma D_3c24c : decode_any W_3c24c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c250 : bv 32 := 0x00053423.
Lemma F_3c250 : fetch_word Plain.M.loaded_segments (0x3c250 : word) = Some W_3c250.
Proof. vm_refl. Qed.
Lemma D_3c250 : decode_any W_3c250 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c254 : bv 32 := 0x02b50023.
Lemma F_3c254 : fetch_word Plain.M.loaded_segments (0x3c254 : word) = Some W_3c254.
Proof. vm_refl. Qed.
Lemma D_3c254 : decode_any W_3c254 = Some (Store SZ1 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c258 : bv 32 := 0x00008067.
Lemma F_3c258 : fetch_word Plain.M.loaded_segments (0x3c258 : word) = Some W_3c258.
Proof. vm_refl. Qed.
Lemma D_3c258 : decode_any W_3c258 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c25c : bv 32 := 0x00158713.
Lemma F_3c25c : fetch_word Plain.M.loaded_segments (0x3c25c : word) = Some W_3c25c.
Proof. vm_refl. Qed.
Lemma D_3c25c : decode_any W_3c25c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c260 : bv 32 := 0x00e53423.
Lemma F_3c260 : fetch_word Plain.M.loaded_segments (0x3c260 : word) = Some W_3c260.
Proof. vm_refl. Qed.
Lemma D_3c260 : decode_any W_3c260 = Some (Store SZ8 10 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c264 : bv 32 := 0x00c70e63.
Lemma F_3c264 : fetch_word Plain.M.loaded_segments (0x3c264 : word) = Some W_3c264.
Proof. vm_refl. Qed.
Lemma D_3c264 : decode_any W_3c264 = Some (Branch BC_EQ 14 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c268 : bv 32 := 0x00074783.
Lemma F_3c268 : fetch_word Plain.M.loaded_segments (0x3c268 : word) = Some W_3c268.
Proof. vm_refl. Qed.
Lemma D_3c268 : decode_any W_3c268 = Some (Load SZ1 false 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c26c : bv 32 := 0x00f687b3.
Lemma F_3c26c : fetch_word Plain.M.loaded_segments (0x3c26c : word) = Some W_3c26c.
Proof. vm_refl. Qed.
Lemma D_3c26c : decode_any W_3c26c = Some (Op ALU_ADD 15 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c270 : bv 32 := 0x0007c783.
Lemma F_3c270 : fetch_word Plain.M.loaded_segments (0x3c270 : word) = Some W_3c270.
Proof. vm_refl. Qed.
Lemma D_3c270 : decode_any W_3c270 = Some (Load SZ1 false 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c274 : bv 32 := 0x00170713.
Lemma F_3c274 : fetch_word Plain.M.loaded_segments (0x3c274 : word) = Some W_3c274.
Proof. vm_refl. Qed.
Lemma D_3c274 : decode_any W_3c274 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c278 : bv 32 := 0xfe0794e3.
Lemma F_3c278 : fetch_word Plain.M.loaded_segments (0x3c278 : word) = Some W_3c278.
Proof. vm_refl. Qed.
Lemma D_3c278 : decode_any W_3c278 = Some (Branch BC_NE 15 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c27c : bv 32 := 0xfff70613.
Lemma F_3c27c : fetch_word Plain.M.loaded_segments (0x3c27c : word) = Some W_3c27c.
Proof. vm_refl. Qed.
Lemma D_3c27c : decode_any W_3c27c = Some (OpImm ALU_ADD 12 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c280 : bv 32 := 0x40b60633.
Lemma F_3c280 : fetch_word Plain.M.loaded_segments (0x3c280 : word) = Some W_3c280.
Proof. vm_refl. Qed.
Lemma D_3c280 : decode_any W_3c280 = Some (Op ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c284 : bv 32 := 0x00b53823.
Lemma F_3c284 : fetch_word Plain.M.loaded_segments (0x3c284 : word) = Some W_3c284.
Proof. vm_refl. Qed.
Lemma D_3c284 : decode_any W_3c284 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c288 : bv 32 := 0x00c53c23.
Lemma F_3c288 : fetch_word Plain.M.loaded_segments (0x3c288 : word) = Some W_3c288.
Proof. vm_refl. Qed.
Lemma D_3c288 : decode_any W_3c288 = Some (Store SZ8 10 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c28c : bv 32 := 0x00008067.
Lemma F_3c28c : fetch_word Plain.M.loaded_segments (0x3c28c : word) = Some W_3c28c.
Proof. vm_refl. Qed.
Lemma D_3c28c : decode_any W_3c28c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c290 : bv 32 := 0xfd010113.
Lemma F_3c290 : fetch_word Plain.M.loaded_segments (0x3c290 : word) = Some W_3c290.
Proof. vm_refl. Qed.
Lemma D_3c290 : decode_any W_3c290 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c294 : bv 32 := 0x02113423.
Lemma F_3c294 : fetch_word Plain.M.loaded_segments (0x3c294 : word) = Some W_3c294.
Proof. vm_refl. Qed.
Lemma D_3c294 : decode_any W_3c294 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c298 : bv 32 := 0x02813023.
Lemma F_3c298 : fetch_word Plain.M.loaded_segments (0x3c298 : word) = Some W_3c298.
Proof. vm_refl. Qed.
Lemma D_3c298 : decode_any W_3c298 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c29c : bv 32 := 0x00060413.
Lemma F_3c29c : fetch_word Plain.M.loaded_segments (0x3c29c : word) = Some W_3c29c.
Proof. vm_refl. Qed.
Lemma D_3c29c : decode_any W_3c29c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2a0 : bv 32 := 0x00053303.
Lemma F_3c2a0 : fetch_word Plain.M.loaded_segments (0x3c2a0 : word) = Some W_3c2a0.
Proof. vm_refl. Qed.
Lemma D_3c2a0 : decode_any W_3c2a0 = Some (Load SZ8 true 6 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2a4 : bv 32 := 0x1ab30863.
Lemma F_3c2a4 : fetch_word Plain.M.loaded_segments (0x3c2a4 : word) = Some W_3c2a4.
Proof. vm_refl. Qed.
Lemma D_3c2a4 : decode_any W_3c2a4 = Some (Branch BC_EQ 6 11 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2a8 : bv 32 := 0x00900613.
Lemma F_3c2a8 : fetch_word Plain.M.loaded_segments (0x3c2a8 : word) = Some W_3c2a8.
Proof. vm_refl. Qed.
Lemma D_3c2a8 : decode_any W_3c2a8 = Some (OpImm ALU_ADD 12 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2ac : bv 32 := 0x02000693.
Lemma F_3c2ac : fetch_word Plain.M.loaded_segments (0x3c2ac : word) = Some W_3c2ac.
Proof. vm_refl. Qed.
Lemma D_3c2ac : decode_any W_3c2ac = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2b0 : bv 32 := 0x03b00713.
Lemma F_3c2b0 : fetch_word Plain.M.loaded_segments (0x3c2b0 : word) = Some W_3c2b0.
Proof. vm_refl. Qed.
Lemma D_3c2b0 : decode_any W_3c2b0 = Some (OpImm ALU_ADD 14 0 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2b4 : bv 32 := 0xfffd9897.
Lemma F_3c2b4 : fetch_word Plain.M.loaded_segments (0x3c2b4 : word) = Some W_3c2b4.
Proof. vm_refl. Qed.
Lemma D_3c2b4 : decode_any W_3c2b4 = Some (Auipc 17 1048537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2b8 : bv 32 := 0x03d00793.
Lemma F_3c2b8 : fetch_word Plain.M.loaded_segments (0x3c2b8 : word) = Some W_3c2b8.
Proof. vm_refl. Qed.
Lemma D_3c2b8 : decode_any W_3c2b8 = Some (OpImm ALU_ADD 15 0 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2bc : bv 32 := 0x02200813.
Lemma F_3c2bc : fetch_word Plain.M.loaded_segments (0x3c2bc : word) = Some W_3c2bc.
Proof. vm_refl. Qed.
Lemma D_3c2bc : decode_any W_3c2bc = Some (OpImm ALU_ADD 16 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2c0 : bv 32 := 0x43688893.
Lemma F_3c2c0 : fetch_word Plain.M.loaded_segments (0x3c2c0 : word) = Some W_3c2c0.
Proof. vm_refl. Qed.
Lemma D_3c2c0 : decode_any W_3c2c0 = Some (OpImm ALU_ADD 17 17 1078, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2c4 : bv 32 := 0x05c00293.
Lemma F_3c2c4 : fetch_word Plain.M.loaded_segments (0x3c2c4 : word) = Some W_3c2c4.
Proof. vm_refl. Qed.
Lemma D_3c2c4 : decode_any W_3c2c4 = Some (OpImm ALU_ADD 5 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2c8 : bv 32 := 0x00034383.
Lemma F_3c2c8 : fetch_word Plain.M.loaded_segments (0x3c2c8 : word) = Some W_3c2c8.
Proof. vm_refl. Qed.
Lemma D_3c2c8 : decode_any W_3c2c8 = Some (Load SZ1 false 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2cc : bv 32 := 0x00c38863.
Lemma F_3c2cc : fetch_word Plain.M.loaded_segments (0x3c2cc : word) = Some W_3c2cc.
Proof. vm_refl. Qed.
Lemma D_3c2cc : decode_any W_3c2cc = Some (Branch BC_EQ 7 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2d0 : bv 32 := 0x00d38663.
Lemma F_3c2d0 : fetch_word Plain.M.loaded_segments (0x3c2d0 : word) = Some W_3c2d0.
Proof. vm_refl. Qed.
Lemma D_3c2d0 : decode_any W_3c2d0 = Some (Branch BC_EQ 7 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2d4 : bv 32 := 0x24e39263.
Lemma F_3c2d4 : fetch_word Plain.M.loaded_segments (0x3c2d4 : word) = Some W_3c2d4.
Proof. vm_refl. Qed.
Lemma D_3c2d4 : decode_any W_3c2d4 = Some (Branch BC_NE 7 14 580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2d8 : bv 32 := 0x0200006f.
Lemma F_3c2d8 : fetch_word Plain.M.loaded_segments (0x3c2d8 : word) = Some W_3c2d8.
Proof. vm_refl. Qed.
Lemma D_3c2d8 : decode_any W_3c2d8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2dc : bv 32 := 0x00130313.
Lemma F_3c2dc : fetch_word Plain.M.loaded_segments (0x3c2dc : word) = Some W_3c2dc.
Proof. vm_refl. Qed.
Lemma D_3c2dc : decode_any W_3c2dc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2e0 : bv 32 := 0x00653023.
Lemma F_3c2e0 : fetch_word Plain.M.loaded_segments (0x3c2e0 : word) = Some W_3c2e0.
Proof. vm_refl. Qed.
Lemma D_3c2e0 : decode_any W_3c2e0 = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2e4 : bv 32 := 0x1cb30463.
Lemma F_3c2e4 : fetch_word Plain.M.loaded_segments (0x3c2e4 : word) = Some W_3c2e4.
Proof. vm_refl. Qed.
Lemma D_3c2e4 : decode_any W_3c2e4 = Some (Branch BC_EQ 6 11 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2e8 : bv 32 := 0x00034383.
Lemma F_3c2e8 : fetch_word Plain.M.loaded_segments (0x3c2e8 : word) = Some W_3c2e8.
Proof. vm_refl. Qed.
Lemma D_3c2e8 : decode_any W_3c2e8 = Some (Load SZ1 false 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2ec : bv 32 := 0xfec388e3.
Lemma F_3c2ec : fetch_word Plain.M.loaded_segments (0x3c2ec : word) = Some W_3c2ec.
Proof. vm_refl. Qed.
Lemma D_3c2ec : decode_any W_3c2ec = Some (Branch BC_EQ 7 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2f0 : bv 32 := 0xfed386e3.
Lemma F_3c2f0 : fetch_word Plain.M.loaded_segments (0x3c2f0 : word) = Some W_3c2f0.
Proof. vm_refl. Qed.
Lemma D_3c2f0 : decode_any W_3c2f0 = Some (Branch BC_EQ 7 13 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2f4 : bv 32 := 0x1ee39263.
Lemma F_3c2f4 : fetch_word Plain.M.loaded_segments (0x3c2f4 : word) = Some W_3c2f4.
Proof. vm_refl. Qed.
Lemma D_3c2f4 : decode_any W_3c2f4 = Some (Branch BC_NE 7 14 484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2f8 : bv 32 := 0x00130393.
Lemma F_3c2f8 : fetch_word Plain.M.loaded_segments (0x3c2f8 : word) = Some W_3c2f8.
Proof. vm_refl. Qed.
Lemma D_3c2f8 : decode_any W_3c2f8 = Some (OpImm ALU_ADD 7 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c2fc : bv 32 := 0x00753023.
Lemma F_3c2fc : fetch_word Plain.M.loaded_segments (0x3c2fc : word) = Some W_3c2fc.
Proof. vm_refl. Qed.
Lemma D_3c2fc : decode_any W_3c2fc = Some (Store SZ8 10 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c300 : bv 32 := 0x18b38063.
Lemma F_3c300 : fetch_word Plain.M.loaded_segments (0x3c300 : word) = Some W_3c300.
Proof. vm_refl. Qed.
Lemma D_3c300 : decode_any W_3c300 = Some (Branch BC_EQ 7 11 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c304 : bv 32 := 0x00230313.
Lemma F_3c304 : fetch_word Plain.M.loaded_segments (0x3c304 : word) = Some W_3c304.
Proof. vm_refl. Qed.
Lemma D_3c304 : decode_any W_3c304 = Some (OpImm ALU_ADD 6 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c308 : bv 32 := 0x0003ce03.
Lemma F_3c308 : fetch_word Plain.M.loaded_segments (0x3c308 : word) = Some W_3c308.
Proof. vm_refl. Qed.
Lemma D_3c308 : decode_any W_3c308 = Some (Load SZ1 false 28 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c30c : bv 32 := 0x00de0463.
Lemma F_3c30c : fetch_word Plain.M.loaded_segments (0x3c30c : word) = Some W_3c30c.
Proof. vm_refl. Qed.
Lemma D_3c30c : decode_any W_3c30c = Some (Branch BC_EQ 28 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c310 : bv 32 := 0x00ce1c63.
Lemma F_3c310 : fetch_word Plain.M.loaded_segments (0x3c310 : word) = Some W_3c310.
Proof. vm_refl. Qed.
Lemma D_3c310 : decode_any W_3c310 = Some (Branch BC_NE 28 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c314 : bv 32 := 0x00138393.
Lemma F_3c314 : fetch_word Plain.M.loaded_segments (0x3c314 : word) = Some W_3c314.
Proof. vm_refl. Qed.
Lemma D_3c314 : decode_any W_3c314 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c318 : bv 32 := 0x00753023.
Lemma F_3c318 : fetch_word Plain.M.loaded_segments (0x3c318 : word) = Some W_3c318.
Proof. vm_refl. Qed.
Lemma D_3c318 : decode_any W_3c318 = Some (Store SZ8 10 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c31c : bv 32 := 0x00130313.
Lemma F_3c31c : fetch_word Plain.M.loaded_segments (0x3c31c : word) = Some W_3c31c.
Proof. vm_refl. Qed.
Lemma D_3c31c : decode_any W_3c31c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c320 : bv 32 := 0xfeb394e3.
Lemma F_3c320 : fetch_word Plain.M.loaded_segments (0x3c320 : word) = Some W_3c320.
Proof. vm_refl. Qed.
Lemma D_3c320 : decode_any W_3c320 = Some (Branch BC_NE 7 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c324 : bv 32 := 0x15c0006f.
Lemma F_3c324 : fetch_word Plain.M.loaded_segments (0x3c324 : word) = Some W_3c324.
Proof. vm_refl. Qed.
Lemma D_3c324 : decode_any W_3c324 = Some (Jal 0 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c328 : bv 32 := 0x01c88e33.
Lemma F_3c328 : fetch_word Plain.M.loaded_segments (0x3c328 : word) = Some W_3c328.
Proof. vm_refl. Qed.
Lemma D_3c328 : decode_any W_3c328 = Some (Op ALU_ADD 28 17 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c32c : bv 32 := 0x000e4383.
Lemma F_3c32c : fetch_word Plain.M.loaded_segments (0x3c32c : word) = Some W_3c32c.
Proof. vm_refl. Qed.
Lemma D_3c32c : decode_any W_3c32c = Some (Load SZ1 false 7 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c330 : bv 32 := 0x20038a63.
Lemma F_3c330 : fetch_word Plain.M.loaded_segments (0x3c330 : word) = Some W_3c330.
Proof. vm_refl. Qed.
Lemma D_3c330 : decode_any W_3c330 = Some (Branch BC_EQ 7 0 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c334 : bv 32 := 0x00653023.
Lemma F_3c334 : fetch_word Plain.M.loaded_segments (0x3c334 : word) = Some W_3c334.
Proof. vm_refl. Qed.
Lemma D_3c334 : decode_any W_3c334 = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c338 : bv 32 := 0x1eb30863.
Lemma F_3c338 : fetch_word Plain.M.loaded_segments (0x3c338 : word) = Some W_3c338.
Proof. vm_refl. Qed.
Lemma D_3c338 : decode_any W_3c338 = Some (Branch BC_EQ 6 11 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c33c : bv 32 := 0x00034383.
Lemma F_3c33c : fetch_word Plain.M.loaded_segments (0x3c33c : word) = Some W_3c33c.
Proof. vm_refl. Qed.
Lemma D_3c33c : decode_any W_3c33c = Some (Load SZ1 false 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c340 : bv 32 := 0x00788e33.
Lemma F_3c340 : fetch_word Plain.M.loaded_segments (0x3c340 : word) = Some W_3c340.
Proof. vm_refl. Qed.
Lemma D_3c340 : decode_any W_3c340 = Some (Op ALU_ADD 28 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c344 : bv 32 := 0x000e4e03.
Lemma F_3c344 : fetch_word Plain.M.loaded_segments (0x3c344 : word) = Some W_3c344.
Proof. vm_refl. Qed.
Lemma D_3c344 : decode_any W_3c344 = Some (Load SZ1 false 28 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c348 : bv 32 := 0x00130313.
Lemma F_3c348 : fetch_word Plain.M.loaded_segments (0x3c348 : word) = Some W_3c348.
Proof. vm_refl. Qed.
Lemma D_3c348 : decode_any W_3c348 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c34c : bv 32 := 0xfe0e14e3.
Lemma F_3c34c : fetch_word Plain.M.loaded_segments (0x3c34c : word) = Some W_3c34c.
Proof. vm_refl. Qed.
Lemma D_3c34c : decode_any W_3c34c = Some (Branch BC_NE 28 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c350 : bv 32 := 0x00c38463.
Lemma F_3c350 : fetch_word Plain.M.loaded_segments (0x3c350 : word) = Some W_3c350.
Proof. vm_refl. Qed.
Lemma D_3c350 : decode_any W_3c350 = Some (Branch BC_EQ 7 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c354 : bv 32 := 0x02d39063.
Lemma F_3c354 : fetch_word Plain.M.loaded_segments (0x3c354 : word) = Some W_3c354.
Proof. vm_refl. Qed.
Lemma D_3c354 : decode_any W_3c354 = Some (Branch BC_NE 7 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c358 : bv 32 := 0x00653023.
Lemma F_3c358 : fetch_word Plain.M.loaded_segments (0x3c358 : word) = Some W_3c358.
Proof. vm_refl. Qed.
Lemma D_3c358 : decode_any W_3c358 = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c35c : bv 32 := 0x1cb30663.
Lemma F_3c35c : fetch_word Plain.M.loaded_segments (0x3c35c : word) = Some W_3c35c.
Proof. vm_refl. Qed.
Lemma D_3c35c : decode_any W_3c35c = Some (Branch BC_EQ 6 11 460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c360 : bv 32 := 0x00034383.
Lemma F_3c360 : fetch_word Plain.M.loaded_segments (0x3c360 : word) = Some W_3c360.
Proof. vm_refl. Qed.
Lemma D_3c360 : decode_any W_3c360 = Some (Load SZ1 false 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c364 : bv 32 := 0x00d38463.
Lemma F_3c364 : fetch_word Plain.M.loaded_segments (0x3c364 : word) = Some W_3c364.
Proof. vm_refl. Qed.
Lemma D_3c364 : decode_any W_3c364 = Some (Branch BC_EQ 7 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c368 : bv 32 := 0x00c39c63.
Lemma F_3c368 : fetch_word Plain.M.loaded_segments (0x3c368 : word) = Some W_3c368.
Proof. vm_refl. Qed.
Lemma D_3c368 : decode_any W_3c368 = Some (Branch BC_NE 7 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c36c : bv 32 := 0x00130313.
Lemma F_3c36c : fetch_word Plain.M.loaded_segments (0x3c36c : word) = Some W_3c36c.
Proof. vm_refl. Qed.
Lemma D_3c36c : decode_any W_3c36c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c370 : bv 32 := 0xfe9ff06f.
Lemma F_3c370 : fetch_word Plain.M.loaded_segments (0x3c370 : word) = Some W_3c370.
Proof. vm_refl. Qed.
Lemma D_3c370 : decode_any W_3c370 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c374 : bv 32 := 0x00000e13.
Lemma F_3c374 : fetch_word Plain.M.loaded_segments (0x3c374 : word) = Some W_3c374.
Proof. vm_refl. Qed.
Lemma D_3c374 : decode_any W_3c374 = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c378 : bv 32 := 0xfff30313.
Lemma F_3c378 : fetch_word Plain.M.loaded_segments (0x3c378 : word) = Some W_3c378.
Proof. vm_refl. Qed.
Lemma D_3c378 : decode_any W_3c378 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c37c : bv 32 := 0x0080006f.
Lemma F_3c37c : fetch_word Plain.M.loaded_segments (0x3c37c : word) = Some W_3c37c.
Proof. vm_refl. Qed.
Lemma D_3c37c : decode_any W_3c37c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c380 : bv 32 := 0x00100e13.
Lemma F_3c380 : fetch_word Plain.M.loaded_segments (0x3c380 : word) = Some W_3c380.
Proof. vm_refl. Qed.
Lemma D_3c380 : decode_any W_3c380 = Some (OpImm ALU_ADD 28 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c384 : bv 32 := 0xf6e38ae3.
Lemma F_3c384 : fetch_word Plain.M.loaded_segments (0x3c384 : word) = Some W_3c384.
Proof. vm_refl. Qed.
Lemma D_3c384 : decode_any W_3c384 = Some (Branch BC_EQ 7 14 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c388 : bv 32 := 0x1af39c63.
Lemma F_3c388 : fetch_word Plain.M.loaded_segments (0x3c388 : word) = Some W_3c388.
Proof. vm_refl. Qed.
Lemma D_3c388 : decode_any W_3c388 = Some (Branch BC_NE 7 15 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c38c : bv 32 := 0x00130393.
Lemma F_3c38c : fetch_word Plain.M.loaded_segments (0x3c38c : word) = Some W_3c38c.
Proof. vm_refl. Qed.
Lemma D_3c38c : decode_any W_3c38c = Some (OpImm ALU_ADD 7 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c390 : bv 32 := 0x00753023.
Lemma F_3c390 : fetch_word Plain.M.loaded_segments (0x3c390 : word) = Some W_3c390.
Proof. vm_refl. Qed.
Lemma D_3c390 : decode_any W_3c390 = Some (Store SZ8 10 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c394 : bv 32 := 0x18b38a63.
Lemma F_3c394 : fetch_word Plain.M.loaded_segments (0x3c394 : word) = Some W_3c394.
Proof. vm_refl. Qed.
Lemma D_3c394 : decode_any W_3c394 = Some (Branch BC_EQ 7 11 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c398 : bv 32 := 0x00230313.
Lemma F_3c398 : fetch_word Plain.M.loaded_segments (0x3c398 : word) = Some W_3c398.
Proof. vm_refl. Qed.
Lemma D_3c398 : decode_any W_3c398 = Some (OpImm ALU_ADD 6 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c39c : bv 32 := 0x0003ce03.
Lemma F_3c39c : fetch_word Plain.M.loaded_segments (0x3c39c : word) = Some W_3c39c.
Proof. vm_refl. Qed.
Lemma D_3c39c : decode_any W_3c39c = Some (Load SZ1 false 28 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3a0 : bv 32 := 0x00ce0463.
Lemma F_3c3a0 : fetch_word Plain.M.loaded_segments (0x3c3a0 : word) = Some W_3c3a0.
Proof. vm_refl. Qed.
Lemma D_3c3a0 : decode_any W_3c3a0 = Some (Branch BC_EQ 28 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3a4 : bv 32 := 0x00de1c63.
Lemma F_3c3a4 : fetch_word Plain.M.loaded_segments (0x3c3a4 : word) = Some W_3c3a4.
Proof. vm_refl. Qed.
Lemma D_3c3a4 : decode_any W_3c3a4 = Some (Branch BC_NE 28 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3a8 : bv 32 := 0x00138393.
Lemma F_3c3a8 : fetch_word Plain.M.loaded_segments (0x3c3a8 : word) = Some W_3c3a8.
Proof. vm_refl. Qed.
Lemma D_3c3a8 : decode_any W_3c3a8 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3ac : bv 32 := 0x00753023.
Lemma F_3c3ac : fetch_word Plain.M.loaded_segments (0x3c3ac : word) = Some W_3c3ac.
Proof. vm_refl. Qed.
Lemma D_3c3ac : decode_any W_3c3ac = Some (Store SZ8 10 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3b0 : bv 32 := 0x00130313.
Lemma F_3c3b0 : fetch_word Plain.M.loaded_segments (0x3c3b0 : word) = Some W_3c3b0.
Proof. vm_refl. Qed.
Lemma D_3c3b0 : decode_any W_3c3b0 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3b4 : bv 32 := 0x16b38a63.
Lemma F_3c3b4 : fetch_word Plain.M.loaded_segments (0x3c3b4 : word) = Some W_3c3b4.
Proof. vm_refl. Qed.
Lemma D_3c3b4 : decode_any W_3c3b4 = Some (Branch BC_EQ 7 11 372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3b8 : bv 32 := 0xfe5ff06f.
Lemma F_3c3b8 : fetch_word Plain.M.loaded_segments (0x3c3b8 : word) = Some W_3c3b8.
Proof. vm_refl. Qed.
Lemma D_3c3b8 : decode_any W_3c3b8 = Some (Jal 0 2097124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3bc : bv 32 := 0x050e1e63.
Lemma F_3c3bc : fetch_word Plain.M.loaded_segments (0x3c3bc : word) = Some W_3c3bc.
Proof. vm_refl. Qed.
Lemma D_3c3bc : decode_any W_3c3bc = Some (Branch BC_NE 28 16 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3c0 : bv 32 := 0x00138313.
Lemma F_3c3c0 : fetch_word Plain.M.loaded_segments (0x3c3c0 : word) = Some W_3c3c0.
Proof. vm_refl. Qed.
Lemma D_3c3c0 : decode_any W_3c3c0 = Some (OpImm ALU_ADD 6 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3c4 : bv 32 := 0x00653023.
Lemma F_3c3c4 : fetch_word Plain.M.loaded_segments (0x3c3c4 : word) = Some W_3c3c4.
Proof. vm_refl. Qed.
Lemma D_3c3c4 : decode_any W_3c3c4 = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3c8 : bv 32 := 0x16b30063.
Lemma F_3c3c8 : fetch_word Plain.M.loaded_segments (0x3c3c8 : word) = Some W_3c3c8.
Proof. vm_refl. Qed.
Lemma D_3c3c8 : decode_any W_3c3c8 = Some (Branch BC_EQ 6 11 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3cc : bv 32 := 0x00034e03.
Lemma F_3c3cc : fetch_word Plain.M.loaded_segments (0x3c3cc : word) = Some W_3c3cc.
Proof. vm_refl. Qed.
Lemma D_3c3cc : decode_any W_3c3cc = Some (Load SZ1 false 28 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3d0 : bv 32 := 0x005e0c63.
Lemma F_3c3d0 : fetch_word Plain.M.loaded_segments (0x3c3d0 : word) = Some W_3c3d0.
Proof. vm_refl. Qed.
Lemma D_3c3d0 : decode_any W_3c3d0 = Some (Branch BC_EQ 28 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3d4 : bv 32 := 0x070e0a63.
Lemma F_3c3d4 : fetch_word Plain.M.loaded_segments (0x3c3d4 : word) = Some W_3c3d4.
Proof. vm_refl. Qed.
Lemma D_3c3d4 : decode_any W_3c3d4 = Some (Branch BC_EQ 28 16 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3d8 : bv 32 := 0xfffda397.
Lemma F_3c3d8 : fetch_word Plain.M.loaded_segments (0x3c3d8 : word) = Some W_3c3d8.
Proof. vm_refl. Qed.
Lemma D_3c3d8 : decode_any W_3c3d8 = Some (Auipc 7 1048538, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3dc : bv 32 := 0xb7f38393.
Lemma F_3c3dc : fetch_word Plain.M.loaded_segments (0x3c3dc : word) = Some W_3c3dc.
Proof. vm_refl. Qed.
Lemma D_3c3dc : decode_any W_3c3dc = Some (OpImm ALU_ADD 7 7 2943, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3e0 : bv 32 := 0x01c383b3.
Lemma F_3c3e0 : fetch_word Plain.M.loaded_segments (0x3c3e0 : word) = Some W_3c3e0.
Proof. vm_refl. Qed.
Lemma D_3c3e0 : decode_any W_3c3e0 = Some (Op ALU_ADD 7 7 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3e4 : bv 32 := 0x0200006f.
Lemma F_3c3e4 : fetch_word Plain.M.loaded_segments (0x3c3e4 : word) = Some W_3c3e4.
Proof. vm_refl. Qed.
Lemma D_3c3e4 : decode_any W_3c3e4 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3e8 : bv 32 := 0x00238313.
Lemma F_3c3e8 : fetch_word Plain.M.loaded_segments (0x3c3e8 : word) = Some W_3c3e8.
Proof. vm_refl. Qed.
Lemma D_3c3e8 : decode_any W_3c3e8 = Some (OpImm ALU_ADD 6 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3ec : bv 32 := 0x00653023.
Lemma F_3c3ec : fetch_word Plain.M.loaded_segments (0x3c3ec : word) = Some W_3c3ec.
Proof. vm_refl. Qed.
Lemma D_3c3ec : decode_any W_3c3ec = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3f0 : bv 32 := 0x12b30c63.
Lemma F_3c3f0 : fetch_word Plain.M.loaded_segments (0x3c3f0 : word) = Some W_3c3f0.
Proof. vm_refl. Qed.
Lemma D_3c3f0 : decode_any W_3c3f0 = Some (Branch BC_EQ 6 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3f4 : bv 32 := 0x00034383.
Lemma F_3c3f4 : fetch_word Plain.M.loaded_segments (0x3c3f4 : word) = Some W_3c3f4.
Proof. vm_refl. Qed.
Lemma D_3c3f4 : decode_any W_3c3f4 = Some (Load SZ1 false 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3f8 : bv 32 := 0xfffdae17.
Lemma F_3c3f8 : fetch_word Plain.M.loaded_segments (0x3c3f8 : word) = Some W_3c3f8.
Proof. vm_refl. Qed.
Lemma D_3c3f8 : decode_any W_3c3f8 = Some (Auipc 28 1048538, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c3fc : bv 32 := 0xa5fe0e13.
Lemma F_3c3fc : fetch_word Plain.M.loaded_segments (0x3c3fc : word) = Some W_3c3fc.
Proof. vm_refl. Qed.
Lemma D_3c3fc : decode_any W_3c3fc = Some (OpImm ALU_ADD 28 28 2655, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c400 : bv 32 := 0x007e03b3.
Lemma F_3c400 : fetch_word Plain.M.loaded_segments (0x3c400 : word) = Some W_3c400.
Proof. vm_refl. Qed.
Lemma D_3c400 : decode_any W_3c400 = Some (Op ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c404 : bv 32 := 0x0003c383.
Lemma F_3c404 : fetch_word Plain.M.loaded_segments (0x3c404 : word) = Some W_3c404.
Proof. vm_refl. Qed.
Lemma D_3c404 : decode_any W_3c404 = Some (Load SZ1 false 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c408 : bv 32 := 0x12038e63.
Lemma F_3c408 : fetch_word Plain.M.loaded_segments (0x3c408 : word) = Some W_3c408.
Proof. vm_refl. Qed.
Lemma D_3c408 : decode_any W_3c408 = Some (Branch BC_EQ 7 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c40c : bv 32 := 0x00030393.
Lemma F_3c40c : fetch_word Plain.M.loaded_segments (0x3c40c : word) = Some W_3c40c.
Proof. vm_refl. Qed.
Lemma D_3c40c : decode_any W_3c40c = Some (OpImm ALU_ADD 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c410 : bv 32 := 0x00130313.
Lemma F_3c410 : fetch_word Plain.M.loaded_segments (0x3c410 : word) = Some W_3c410.
Proof. vm_refl. Qed.
Lemma D_3c410 : decode_any W_3c410 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c414 : bv 32 := 0xfb1ff06f.
Lemma F_3c414 : fetch_word Plain.M.loaded_segments (0x3c414 : word) = Some W_3c414.
Proof. vm_refl. Qed.
Lemma D_3c414 : decode_any W_3c414 = Some (Jal 0 2097072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c418 : bv 32 := 0x01c88e33.
Lemma F_3c418 : fetch_word Plain.M.loaded_segments (0x3c418 : word) = Some W_3c418.
Proof. vm_refl. Qed.
Lemma D_3c418 : decode_any W_3c418 = Some (Op ALU_ADD 28 17 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c41c : bv 32 := 0x000e4383.
Lemma F_3c41c : fetch_word Plain.M.loaded_segments (0x3c41c : word) = Some W_3c41c.
Proof. vm_refl. Qed.
Lemma D_3c41c : decode_any W_3c41c = Some (Load SZ1 false 7 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c420 : bv 32 := 0x12038263.
Lemma F_3c420 : fetch_word Plain.M.loaded_segments (0x3c420 : word) = Some W_3c420.
Proof. vm_refl. Qed.
Lemma D_3c420 : decode_any W_3c420 = Some (Branch BC_EQ 7 0 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c424 : bv 32 := 0x00653023.
Lemma F_3c424 : fetch_word Plain.M.loaded_segments (0x3c424 : word) = Some W_3c424.
Proof. vm_refl. Qed.
Lemma D_3c424 : decode_any W_3c424 = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c428 : bv 32 := 0x10b30063.
Lemma F_3c428 : fetch_word Plain.M.loaded_segments (0x3c428 : word) = Some W_3c428.
Proof. vm_refl. Qed.
Lemma D_3c428 : decode_any W_3c428 = Some (Branch BC_EQ 6 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c42c : bv 32 := 0x00034383.
Lemma F_3c42c : fetch_word Plain.M.loaded_segments (0x3c42c : word) = Some W_3c42c.
Proof. vm_refl. Qed.
Lemma D_3c42c : decode_any W_3c42c = Some (Load SZ1 false 7 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c430 : bv 32 := 0x007883b3.
Lemma F_3c430 : fetch_word Plain.M.loaded_segments (0x3c430 : word) = Some W_3c430.
Proof. vm_refl. Qed.
Lemma D_3c430 : decode_any W_3c430 = Some (Op ALU_ADD 7 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c434 : bv 32 := 0x0003c383.
Lemma F_3c434 : fetch_word Plain.M.loaded_segments (0x3c434 : word) = Some W_3c434.
Proof. vm_refl. Qed.
Lemma D_3c434 : decode_any W_3c434 = Some (Load SZ1 false 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c438 : bv 32 := 0x00130313.
Lemma F_3c438 : fetch_word Plain.M.loaded_segments (0x3c438 : word) = Some W_3c438.
Proof. vm_refl. Qed.
Lemma D_3c438 : decode_any W_3c438 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c43c : bv 32 := 0xfe0394e3.
Lemma F_3c43c : fetch_word Plain.M.loaded_segments (0x3c43c : word) = Some W_3c43c.
Proof. vm_refl. Qed.
Lemma D_3c43c : decode_any W_3c43c = Some (Branch BC_NE 7 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c440 : bv 32 := 0xfff30313.
Lemma F_3c440 : fetch_word Plain.M.loaded_segments (0x3c440 : word) = Some W_3c440.
Proof. vm_refl. Qed.
Lemma D_3c440 : decode_any W_3c440 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c444 : bv 32 := 0x00c0006f.
Lemma F_3c444 : fetch_word Plain.M.loaded_segments (0x3c444 : word) = Some W_3c444.
Proof. vm_refl. Qed.
Lemma D_3c444 : decode_any W_3c444 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c448 : bv 32 := 0x00238313.
Lemma F_3c448 : fetch_word Plain.M.loaded_segments (0x3c448 : word) = Some W_3c448.
Proof. vm_refl. Qed.
Lemma D_3c448 : decode_any W_3c448 = Some (OpImm ALU_ADD 6 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c44c : bv 32 := 0x00653023.
Lemma F_3c44c : fetch_word Plain.M.loaded_segments (0x3c44c : word) = Some W_3c44c.
Proof. vm_refl. Qed.
Lemma D_3c44c : decode_any W_3c44c = Some (Store SZ8 10 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c450 : bv 32 := 0xe6b31ce3.
Lemma F_3c450 : fetch_word Plain.M.loaded_segments (0x3c450 : word) = Some W_3c450.
Proof. vm_refl. Qed.
Lemma D_3c450 : decode_any W_3c450 = Some (Branch BC_NE 6 11 7800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c454 : bv 32 := 0x00810513.
Lemma F_3c454 : fetch_word Plain.M.loaded_segments (0x3c454 : word) = Some W_3c454.
Proof. vm_refl. Qed.
Lemma D_3c454 : decode_any W_3c454 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c458 : bv 32 := 0x00300593.
Lemma F_3c458 : fetch_word Plain.M.loaded_segments (0x3c458 : word) = Some W_3c458.
Proof. vm_refl. Qed.
Lemma D_3c458 : decode_any W_3c458 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c45c : bv 32 := 0x00000613.
Lemma F_3c45c : fetch_word Plain.M.loaded_segments (0x3c45c : word) = Some W_3c45c.
Proof. vm_refl. Qed.
Lemma D_3c45c : decode_any W_3c45c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c460 : bv 32 := 0xf6df50ef.
Lemma F_3c460 : fetch_word Plain.M.loaded_segments (0x3c460 : word) = Some W_3c460.
Proof. vm_refl. Qed.
Lemma D_3c460 : decode_any W_3c460 = Some (Jal 1 2056044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c464 : bv 32 := 0x01813503.
Lemma F_3c464 : fetch_word Plain.M.loaded_segments (0x3c464 : word) = Some W_3c464.
Proof. vm_refl. Qed.
Lemma D_3c464 : decode_any W_3c464 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c468 : bv 32 := 0x00200593.
Lemma F_3c468 : fetch_word Plain.M.loaded_segments (0x3c468 : word) = Some W_3c468.
Proof. vm_refl. Qed.
Lemma D_3c468 : decode_any W_3c468 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c46c : bv 32 := 0x08b56c63.
Lemma F_3c46c : fetch_word Plain.M.loaded_segments (0x3c46c : word) = Some W_3c46c.
Proof. vm_refl. Qed.
Lemma D_3c46c : decode_any W_3c46c = Some (Branch BC_LTU 10 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c470 : bv 32 := 0x00157513.
Lemma F_3c470 : fetch_word Plain.M.loaded_segments (0x3c470 : word) = Some W_3c470.
Proof. vm_refl. Qed.
Lemma D_3c470 : decode_any W_3c470 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c474 : bv 32 := 0x00040597.
Lemma F_3c474 : fetch_word Plain.M.loaded_segments (0x3c474 : word) = Some W_3c474.
Proof. vm_refl. Qed.
Lemma D_3c474 : decode_any W_3c474 = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c478 : bv 32 := 0xdec58593.
Lemma F_3c478 : fetch_word Plain.M.loaded_segments (0x3c478 : word) = Some W_3c478.
Proof. vm_refl. Qed.
Lemma D_3c478 : decode_any W_3c478 = Some (OpImm ALU_ADD 11 11 3564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c47c : bv 32 := 0x0840006f.
Lemma F_3c47c : fetch_word Plain.M.loaded_segments (0x3c47c : word) = Some W_3c47c.
Proof. vm_refl. Qed.
Lemma D_3c47c : decode_any W_3c47c = Some (Jal 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c480 : bv 32 := 0x00810513.
Lemma F_3c480 : fetch_word Plain.M.loaded_segments (0x3c480 : word) = Some W_3c480.
Proof. vm_refl. Qed.
Lemma D_3c480 : decode_any W_3c480 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c484 : bv 32 := 0x00300593.
Lemma F_3c484 : fetch_word Plain.M.loaded_segments (0x3c484 : word) = Some W_3c484.
Proof. vm_refl. Qed.
Lemma D_3c484 : decode_any W_3c484 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c488 : bv 32 := 0x00000613.
Lemma F_3c488 : fetch_word Plain.M.loaded_segments (0x3c488 : word) = Some W_3c488.
Proof. vm_refl. Qed.
Lemma D_3c488 : decode_any W_3c488 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c48c : bv 32 := 0xf41f50ef.
Lemma F_3c48c : fetch_word Plain.M.loaded_segments (0x3c48c : word) = Some W_3c48c.
Proof. vm_refl. Qed.
Lemma D_3c48c : decode_any W_3c48c = Some (Jal 1 2056000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c490 : bv 32 := 0x01813503.
Lemma F_3c490 : fetch_word Plain.M.loaded_segments (0x3c490 : word) = Some W_3c490.
Proof. vm_refl. Qed.
Lemma D_3c490 : decode_any W_3c490 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c494 : bv 32 := 0x00200593.
Lemma F_3c494 : fetch_word Plain.M.loaded_segments (0x3c494 : word) = Some W_3c494.
Proof. vm_refl. Qed.
Lemma D_3c494 : decode_any W_3c494 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c498 : bv 32 := 0x06b56663.
Lemma F_3c498 : fetch_word Plain.M.loaded_segments (0x3c498 : word) = Some W_3c498.
Proof. vm_refl. Qed.
Lemma D_3c498 : decode_any W_3c498 = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c49c : bv 32 := 0x00157513.
Lemma F_3c49c : fetch_word Plain.M.loaded_segments (0x3c49c : word) = Some W_3c49c.
Proof. vm_refl. Qed.
Lemma D_3c49c : decode_any W_3c49c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4a0 : bv 32 := 0x00040597.
Lemma F_3c4a0 : fetch_word Plain.M.loaded_segments (0x3c4a0 : word) = Some W_3c4a0.
Proof. vm_refl. Qed.
Lemma D_3c4a0 : decode_any W_3c4a0 = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4a4 : bv 32 := 0xe0858593.
Lemma F_3c4a4 : fetch_word Plain.M.loaded_segments (0x3c4a4 : word) = Some W_3c4a4.
Proof. vm_refl. Qed.
Lemma D_3c4a4 : decode_any W_3c4a4 = Some (OpImm ALU_ADD 11 11 3592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4a8 : bv 32 := 0x0580006f.
Lemma F_3c4a8 : fetch_word Plain.M.loaded_segments (0x3c4a8 : word) = Some W_3c4a8.
Proof. vm_refl. Qed.
Lemma D_3c4a8 : decode_any W_3c4a8 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4ac : bv 32 := 0x00810513.
Lemma F_3c4ac : fetch_word Plain.M.loaded_segments (0x3c4ac : word) = Some W_3c4ac.
Proof. vm_refl. Qed.
Lemma D_3c4ac : decode_any W_3c4ac = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4b0 : bv 32 := 0x00300593.
Lemma F_3c4b0 : fetch_word Plain.M.loaded_segments (0x3c4b0 : word) = Some W_3c4b0.
Proof. vm_refl. Qed.
Lemma D_3c4b0 : decode_any W_3c4b0 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4b4 : bv 32 := 0x00000613.
Lemma F_3c4b4 : fetch_word Plain.M.loaded_segments (0x3c4b4 : word) = Some W_3c4b4.
Proof. vm_refl. Qed.
Lemma D_3c4b4 : decode_any W_3c4b4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4b8 : bv 32 := 0xf15f50ef.
Lemma F_3c4b8 : fetch_word Plain.M.loaded_segments (0x3c4b8 : word) = Some W_3c4b8.
Proof. vm_refl. Qed.
Lemma D_3c4b8 : decode_any W_3c4b8 = Some (Jal 1 2055956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4bc : bv 32 := 0x01813503.
Lemma F_3c4bc : fetch_word Plain.M.loaded_segments (0x3c4bc : word) = Some W_3c4bc.
Proof. vm_refl. Qed.
Lemma D_3c4bc : decode_any W_3c4bc = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4c0 : bv 32 := 0x00200593.
Lemma F_3c4c0 : fetch_word Plain.M.loaded_segments (0x3c4c0 : word) = Some W_3c4c0.
Proof. vm_refl. Qed.
Lemma D_3c4c0 : decode_any W_3c4c0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4c4 : bv 32 := 0x04b56063.
Lemma F_3c4c4 : fetch_word Plain.M.loaded_segments (0x3c4c4 : word) = Some W_3c4c4.
Proof. vm_refl. Qed.
Lemma D_3c4c4 : decode_any W_3c4c4 = Some (Branch BC_LTU 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4c8 : bv 32 := 0x00157513.
Lemma F_3c4c8 : fetch_word Plain.M.loaded_segments (0x3c4c8 : word) = Some W_3c4c8.
Proof. vm_refl. Qed.
Lemma D_3c4c8 : decode_any W_3c4c8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4cc : bv 32 := 0x00040597.
Lemma F_3c4cc : fetch_word Plain.M.loaded_segments (0x3c4cc : word) = Some W_3c4cc.
Proof. vm_refl. Qed.
Lemma D_3c4cc : decode_any W_3c4cc = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4d0 : bv 32 := 0xdac58593.
Lemma F_3c4d0 : fetch_word Plain.M.loaded_segments (0x3c4d0 : word) = Some W_3c4d0.
Proof. vm_refl. Qed.
Lemma D_3c4d0 : decode_any W_3c4d0 = Some (OpImm ALU_ADD 11 11 3500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4d4 : bv 32 := 0x02c0006f.
Lemma F_3c4d4 : fetch_word Plain.M.loaded_segments (0x3c4d4 : word) = Some W_3c4d4.
Proof. vm_refl. Qed.
Lemma D_3c4d4 : decode_any W_3c4d4 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4d8 : bv 32 := 0x00810513.
Lemma F_3c4d8 : fetch_word Plain.M.loaded_segments (0x3c4d8 : word) = Some W_3c4d8.
Proof. vm_refl. Qed.
Lemma D_3c4d8 : decode_any W_3c4d8 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4dc : bv 32 := 0x01600593.
Lemma F_3c4dc : fetch_word Plain.M.loaded_segments (0x3c4dc : word) = Some W_3c4dc.
Proof. vm_refl. Qed.
Lemma D_3c4dc : decode_any W_3c4dc = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4e0 : bv 32 := 0x00000613.
Lemma F_3c4e0 : fetch_word Plain.M.loaded_segments (0x3c4e0 : word) = Some W_3c4e0.
Proof. vm_refl. Qed.
Lemma D_3c4e0 : decode_any W_3c4e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4e4 : bv 32 := 0xee9f50ef.
Lemma F_3c4e4 : fetch_word Plain.M.loaded_segments (0x3c4e4 : word) = Some W_3c4e4.
Proof. vm_refl. Qed.
Lemma D_3c4e4 : decode_any W_3c4e4 = Some (Jal 1 2055912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4e8 : bv 32 := 0x01813503.
Lemma F_3c4e8 : fetch_word Plain.M.loaded_segments (0x3c4e8 : word) = Some W_3c4e8.
Proof. vm_refl. Qed.
Lemma D_3c4e8 : decode_any W_3c4e8 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4ec : bv 32 := 0x00200593.
Lemma F_3c4ec : fetch_word Plain.M.loaded_segments (0x3c4ec : word) = Some W_3c4ec.
Proof. vm_refl. Qed.
Lemma D_3c4ec : decode_any W_3c4ec = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4f0 : bv 32 := 0x00b56a63.
Lemma F_3c4f0 : fetch_word Plain.M.loaded_segments (0x3c4f0 : word) = Some W_3c4f0.
Proof. vm_refl. Qed.
Lemma D_3c4f0 : decode_any W_3c4f0 = Some (Branch BC_LTU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4f4 : bv 32 := 0x00157513.
Lemma F_3c4f4 : fetch_word Plain.M.loaded_segments (0x3c4f4 : word) = Some W_3c4f4.
Proof. vm_refl. Qed.
Lemma D_3c4f4 : decode_any W_3c4f4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4f8 : bv 32 := 0x00040597.
Lemma F_3c4f8 : fetch_word Plain.M.loaded_segments (0x3c4f8 : word) = Some W_3c4f8.
Proof. vm_refl. Qed.
Lemma D_3c4f8 : decode_any W_3c4f8 = Some (Auipc 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c4fc : bv 32 := 0xd9858593.
Lemma F_3c4fc : fetch_word Plain.M.loaded_segments (0x3c4fc : word) = Some W_3c4fc.
Proof. vm_refl. Qed.
Lemma D_3c4fc : decode_any W_3c4fc = Some (OpImm ALU_ADD 11 11 3480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c500 : bv 32 := 0x00b56533.
Lemma F_3c500 : fetch_word Plain.M.loaded_segments (0x3c500 : word) = Some W_3c500.
Proof. vm_refl. Qed.
Lemma D_3c500 : decode_any W_3c500 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c504 : bv 32 := 0x00813583.
Lemma F_3c504 : fetch_word Plain.M.loaded_segments (0x3c504 : word) = Some W_3c504.
Proof. vm_refl. Qed.
Lemma D_3c504 : decode_any W_3c504 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c508 : bv 32 := 0x01013603.
Lemma F_3c508 : fetch_word Plain.M.loaded_segments (0x3c508 : word) = Some W_3c508.
Proof. vm_refl. Qed.
Lemma D_3c508 : decode_any W_3c508 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c50c : bv 32 := 0x00b43023.
Lemma F_3c50c : fetch_word Plain.M.loaded_segments (0x3c50c : word) = Some W_3c50c.
Proof. vm_refl. Qed.
Lemma D_3c50c : decode_any W_3c50c = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c510 : bv 32 := 0x00c43423.
Lemma F_3c510 : fetch_word Plain.M.loaded_segments (0x3c510 : word) = Some W_3c510.
Proof. vm_refl. Qed.
Lemma D_3c510 : decode_any W_3c510 = Some (Store SZ8 8 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c514 : bv 32 := 0x00a43823.
Lemma F_3c514 : fetch_word Plain.M.loaded_segments (0x3c514 : word) = Some W_3c514.
Proof. vm_refl. Qed.
Lemma D_3c514 : decode_any W_3c514 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c518 : bv 32 := 0x02813083.
Lemma F_3c518 : fetch_word Plain.M.loaded_segments (0x3c518 : word) = Some W_3c518.
Proof. vm_refl. Qed.
Lemma D_3c518 : decode_any W_3c518 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c51c : bv 32 := 0x02013403.
Lemma F_3c51c : fetch_word Plain.M.loaded_segments (0x3c51c : word) = Some W_3c51c.
Proof. vm_refl. Qed.
Lemma D_3c51c : decode_any W_3c51c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c520 : bv 32 := 0x03010113.
Lemma F_3c520 : fetch_word Plain.M.loaded_segments (0x3c520 : word) = Some W_3c520.
Proof. vm_refl. Qed.
Lemma D_3c520 : decode_any W_3c520 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c524 : bv 32 := 0x00008067.
Lemma F_3c524 : fetch_word Plain.M.loaded_segments (0x3c524 : word) = Some W_3c524.
Proof. vm_refl. Qed.
Lemma D_3c524 : decode_any W_3c524 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c528 : bv 32 := 0x00300593.
Lemma F_3c528 : fetch_word Plain.M.loaded_segments (0x3c528 : word) = Some W_3c528.
Proof. vm_refl. Qed.
Lemma D_3c528 : decode_any W_3c528 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c52c : bv 32 := 0x00040513.
Lemma F_3c52c : fetch_word Plain.M.loaded_segments (0x3c52c : word) = Some W_3c52c.
Proof. vm_refl. Qed.
Lemma D_3c52c : decode_any W_3c52c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c530 : bv 32 := 0x02813083.
Lemma F_3c530 : fetch_word Plain.M.loaded_segments (0x3c530 : word) = Some W_3c530.
Proof. vm_refl. Qed.
Lemma D_3c530 : decode_any W_3c530 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c534 : bv 32 := 0x02013403.
Lemma F_3c534 : fetch_word Plain.M.loaded_segments (0x3c534 : word) = Some W_3c534.
Proof. vm_refl. Qed.
Lemma D_3c534 : decode_any W_3c534 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c538 : bv 32 := 0x03010113.
Lemma F_3c538 : fetch_word Plain.M.loaded_segments (0x3c538 : word) = Some W_3c538.
Proof. vm_refl. Qed.
Lemma D_3c538 : decode_any W_3c538 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c53c : bv 32 := 0x0100006f.
Lemma F_3c53c : fetch_word Plain.M.loaded_segments (0x3c53c : word) = Some W_3c53c.
Proof. vm_refl. Qed.
Lemma D_3c53c : decode_any W_3c53c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c540 : bv 32 := 0xfc0e0ce3.
Lemma F_3c540 : fetch_word Plain.M.loaded_segments (0x3c540 : word) = Some W_3c540.
Proof. vm_refl. Qed.
Lemma D_3c540 : decode_any W_3c540 = Some (Branch BC_EQ 28 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c544 : bv 32 := 0x01600593.
Lemma F_3c544 : fetch_word Plain.M.loaded_segments (0x3c544 : word) = Some W_3c544.
Proof. vm_refl. Qed.
Lemma D_3c544 : decode_any W_3c544 = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c548 : bv 32 := 0xfe5ff06f.
Lemma F_3c548 : fetch_word Plain.M.loaded_segments (0x3c548 : word) = Some W_3c548.
Proof. vm_refl. Qed.
Lemma D_3c548 : decode_any W_3c548 = Some (Jal 0 2097124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c54c : bv 32 := 0xfe010113.
Lemma F_3c54c : fetch_word Plain.M.loaded_segments (0x3c54c : word) = Some W_3c54c.
Proof. vm_refl. Qed.
Lemma D_3c54c : decode_any W_3c54c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c550 : bv 32 := 0x00113c23.
Lemma F_3c550 : fetch_word Plain.M.loaded_segments (0x3c550 : word) = Some W_3c550.
Proof. vm_refl. Qed.
Lemma D_3c550 : decode_any W_3c550 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c554 : bv 32 := 0x00813823.
Lemma F_3c554 : fetch_word Plain.M.loaded_segments (0x3c554 : word) = Some W_3c554.
Proof. vm_refl. Qed.
Lemma D_3c554 : decode_any W_3c554 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c558 : bv 32 := 0x00913423.
Lemma F_3c558 : fetch_word Plain.M.loaded_segments (0x3c558 : word) = Some W_3c558.
Proof. vm_refl. Qed.
Lemma D_3c558 : decode_any W_3c558 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c55c : bv 32 := 0x01213023.
Lemma F_3c55c : fetch_word Plain.M.loaded_segments (0x3c55c : word) = Some W_3c55c.
Proof. vm_refl. Qed.
Lemma D_3c55c : decode_any W_3c55c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c560 : bv 32 := 0x00058493.
Lemma F_3c560 : fetch_word Plain.M.loaded_segments (0x3c560 : word) = Some W_3c560.
Proof. vm_refl. Qed.
Lemma D_3c560 : decode_any W_3c560 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c564 : bv 32 := 0x00050413.
Lemma F_3c564 : fetch_word Plain.M.loaded_segments (0x3c564 : word) = Some W_3c564.
Proof. vm_refl. Qed.
Lemma D_3c564 : decode_any W_3c564 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c568 : bv 32 := 0x00055517.
Lemma F_3c568 : fetch_word Plain.M.loaded_segments (0x3c568 : word) = Some W_3c568.
Proof. vm_refl. Qed.
Lemma D_3c568 : decode_any W_3c568 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c56c : bv 32 := 0x80050503.
Lemma F_3c56c : fetch_word Plain.M.loaded_segments (0x3c56c : word) = Some W_3c56c.
Proof. vm_refl. Qed.
Lemma D_3c56c : decode_any W_3c56c = Some (Load SZ1 true 10 10 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c570 : bv 32 := 0x0230000f.
Lemma F_3c570 : fetch_word Plain.M.loaded_segments (0x3c570 : word) = Some W_3c570.
Proof. vm_refl. Qed.
Lemma D_3c570 : decode_any W_3c570 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c574 : bv 32 := 0x00054597.
Lemma F_3c574 : fetch_word Plain.M.loaded_segments (0x3c574 : word) = Some W_3c574.
Proof. vm_refl. Qed.
Lemma D_3c574 : decode_any W_3c574 = Some (Auipc 11 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c578 : bv 32 := 0x7bc58913.
Lemma F_3c578 : fetch_word Plain.M.loaded_segments (0x3c578 : word) = Some W_3c578.
Proof. vm_refl. Qed.
Lemma D_3c578 : decode_any W_3c578 = Some (OpImm ALU_ADD 18 11 1980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c57c : bv 32 := 0x06050463.
Lemma F_3c57c : fetch_word Plain.M.loaded_segments (0x3c57c : word) = Some W_3c57c.
Proof. vm_refl. Qed.
Lemma D_3c57c : decode_any W_3c57c = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c580 : bv 32 := 0x00893503.
Lemma F_3c580 : fetch_word Plain.M.loaded_segments (0x3c580 : word) = Some W_3c580.
Proof. vm_refl. Qed.
Lemma D_3c580 : decode_any W_3c580 = Some (Load SZ8 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c584 : bv 32 := 0xfffd9597.
Lemma F_3c584 : fetch_word Plain.M.loaded_segments (0x3c584 : word) = Some W_3c584.
Proof. vm_refl. Qed.
Lemma D_3c584 : decode_any W_3c584 = Some (Auipc 11 1048537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c588 : bv 32 := 0x8645b583.
Lemma F_3c588 : fetch_word Plain.M.loaded_segments (0x3c588 : word) = Some W_3c588.
Proof. vm_refl. Qed.
Lemma D_3c588 : decode_any W_3c588 = Some (Load SZ8 true 11 11 2148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c58c : bv 32 := 0x00155513.
Lemma F_3c58c : fetch_word Plain.M.loaded_segments (0x3c58c : word) = Some W_3c58c.
Proof. vm_refl. Qed.
Lemma D_3c58c : decode_any W_3c58c = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c590 : bv 32 := 0x00b51663.
Lemma F_3c590 : fetch_word Plain.M.loaded_segments (0x3c590 : word) = Some W_3c590.
Proof. vm_refl. Qed.
Lemma D_3c590 : decode_any W_3c590 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c594 : bv 32 := 0x00903533.
Lemma F_3c594 : fetch_word Plain.M.loaded_segments (0x3c594 : word) = Some W_3c594.
Proof. vm_refl. Qed.
Lemma D_3c594 : decode_any W_3c594 = Some (Op ALU_SLTU 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c598 : bv 32 := 0x0180006f.
Lemma F_3c598 : fetch_word Plain.M.loaded_segments (0x3c598 : word) = Some W_3c598.
Proof. vm_refl. Qed.
Lemma D_3c598 : decode_any W_3c598 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c59c : bv 32 := 0x00093503.
Lemma F_3c59c : fetch_word Plain.M.loaded_segments (0x3c59c : word) = Some W_3c59c.
Proof. vm_refl. Qed.
Lemma D_3c59c : decode_any W_3c59c = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5a0 : bv 32 := 0x03053603.
Lemma F_3c5a0 : fetch_word Plain.M.loaded_segments (0x3c5a0 : word) = Some W_3c5a0.
Proof. vm_refl. Qed.
Lemma D_3c5a0 : decode_any W_3c5a0 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5a4 : bv 32 := 0x00090513.
Lemma F_3c5a4 : fetch_word Plain.M.loaded_segments (0x3c5a4 : word) = Some W_3c5a4.
Proof. vm_refl. Qed.
Lemma D_3c5a4 : decode_any W_3c5a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5a8 : bv 32 := 0x00048593.
Lemma F_3c5a8 : fetch_word Plain.M.loaded_segments (0x3c5a8 : word) = Some W_3c5a8.
Proof. vm_refl. Qed.
Lemma D_3c5a8 : decode_any W_3c5a8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5ac : bv 32 := 0x000600e7.
Lemma F_3c5ac : fetch_word Plain.M.loaded_segments (0x3c5ac : word) = Some W_3c5ac.
Proof. vm_refl. Qed.
Lemma D_3c5ac : decode_any W_3c5ac = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5b0 : bv 32 := 0x00250513.
Lemma F_3c5b0 : fetch_word Plain.M.loaded_segments (0x3c5b0 : word) = Some W_3c5b0.
Proof. vm_refl. Qed.
Lemma D_3c5b0 : decode_any W_3c5b0 = Some (OpImm ALU_ADD 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5b4 : bv 32 := 0x02049493.
Lemma F_3c5b4 : fetch_word Plain.M.loaded_segments (0x3c5b4 : word) = Some W_3c5b4.
Proof. vm_refl. Qed.
Lemma D_3c5b4 : decode_any W_3c5b4 = Some (ShiftImm ALU_SLL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5b8 : bv 32 := 0x0204d493.
Lemma F_3c5b8 : fetch_word Plain.M.loaded_segments (0x3c5b8 : word) = Some W_3c5b8.
Proof. vm_refl. Qed.
Lemma D_3c5b8 : decode_any W_3c5b8 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5bc : bv 32 := 0x00943023.
Lemma F_3c5bc : fetch_word Plain.M.loaded_segments (0x3c5bc : word) = Some W_3c5bc.
Proof. vm_refl. Qed.
Lemma D_3c5bc : decode_any W_3c5bc = Some (Store SZ8 8 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5c0 : bv 32 := 0x01243423.
Lemma F_3c5c0 : fetch_word Plain.M.loaded_segments (0x3c5c0 : word) = Some W_3c5c0.
Proof. vm_refl. Qed.
Lemma D_3c5c0 : decode_any W_3c5c0 = Some (Store SZ8 8 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5c4 : bv 32 := 0x00a43823.
Lemma F_3c5c4 : fetch_word Plain.M.loaded_segments (0x3c5c4 : word) = Some W_3c5c4.
Proof. vm_refl. Qed.
Lemma D_3c5c4 : decode_any W_3c5c4 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5c8 : bv 32 := 0x00040513.
Lemma F_3c5c8 : fetch_word Plain.M.loaded_segments (0x3c5c8 : word) = Some W_3c5c8.
Proof. vm_refl. Qed.
Lemma D_3c5c8 : decode_any W_3c5c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5cc : bv 32 := 0x01813083.
Lemma F_3c5cc : fetch_word Plain.M.loaded_segments (0x3c5cc : word) = Some W_3c5cc.
Proof. vm_refl. Qed.
Lemma D_3c5cc : decode_any W_3c5cc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5d0 : bv 32 := 0x01013403.
Lemma F_3c5d0 : fetch_word Plain.M.loaded_segments (0x3c5d0 : word) = Some W_3c5d0.
Proof. vm_refl. Qed.
Lemma D_3c5d0 : decode_any W_3c5d0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5d4 : bv 32 := 0x00813483.
Lemma F_3c5d4 : fetch_word Plain.M.loaded_segments (0x3c5d4 : word) = Some W_3c5d4.
Proof. vm_refl. Qed.
Lemma D_3c5d4 : decode_any W_3c5d4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5d8 : bv 32 := 0x00013903.
Lemma F_3c5d8 : fetch_word Plain.M.loaded_segments (0x3c5d8 : word) = Some W_3c5d8.
Proof. vm_refl. Qed.
Lemma D_3c5d8 : decode_any W_3c5d8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5dc : bv 32 := 0x02010113.
Lemma F_3c5dc : fetch_word Plain.M.loaded_segments (0x3c5dc : word) = Some W_3c5dc.
Proof. vm_refl. Qed.
Lemma D_3c5dc : decode_any W_3c5dc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5e0 : bv 32 := 0x00008067.
Lemma F_3c5e0 : fetch_word Plain.M.loaded_segments (0x3c5e0 : word) = Some W_3c5e0.
Proof. vm_refl. Qed.
Lemma D_3c5e0 : decode_any W_3c5e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5e4 : bv 32 := 0x00054517.
Lemma F_3c5e4 : fetch_word Plain.M.loaded_segments (0x3c5e4 : word) = Some W_3c5e4.
Proof. vm_refl. Qed.
Lemma D_3c5e4 : decode_any W_3c5e4 = Some (Auipc 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5e8 : bv 32 := 0x78450513.
Lemma F_3c5e8 : fetch_word Plain.M.loaded_segments (0x3c5e8 : word) = Some W_3c5e8.
Proof. vm_refl. Qed.
Lemma D_3c5e8 : decode_any W_3c5e8 = Some (OpImm ALU_ADD 10 10 1924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5ec : bv 32 := 0x0bc000ef.
Lemma F_3c5ec : fetch_word Plain.M.loaded_segments (0x3c5ec : word) = Some W_3c5ec.
Proof. vm_refl. Qed.
Lemma D_3c5ec : decode_any W_3c5ec = Some (Jal 1 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5f0 : bv 32 := 0x0005051b.
Lemma F_3c5f0 : fetch_word Plain.M.loaded_segments (0x3c5f0 : word) = Some W_3c5f0.
Proof. vm_refl. Qed.
Lemma D_3c5f0 : decode_any W_3c5f0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5f4 : bv 32 := 0xf80506e3.
Lemma F_3c5f4 : fetch_word Plain.M.loaded_segments (0x3c5f4 : word) = Some W_3c5f4.
Proof. vm_refl. Qed.
Lemma D_3c5f4 : decode_any W_3c5f4 = Some (Branch BC_EQ 10 0 8076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5f8 : bv 32 := 0xfffd9517.
Lemma F_3c5f8 : fetch_word Plain.M.loaded_segments (0x3c5f8 : word) = Some W_3c5f8.
Proof. vm_refl. Qed.
Lemma D_3c5f8 : decode_any W_3c5f8 = Some (Auipc 10 1048537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c5fc : bv 32 := 0x8b053503.
Lemma F_3c5fc : fetch_word Plain.M.loaded_segments (0x3c5fc : word) = Some W_3c5fc.
Proof. vm_refl. Qed.
Lemma D_3c5fc : decode_any W_3c5fc = Some (Load SZ8 true 10 10 2224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c600 : bv 32 := 0x00a93423.
Lemma F_3c600 : fetch_word Plain.M.loaded_segments (0x3c600 : word) = Some W_3c600.
Proof. vm_refl. Qed.
Lemma D_3c600 : decode_any W_3c600 = Some (Store SZ8 18 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c604 : bv 32 := 0x01090513.
Lemma F_3c604 : fetch_word Plain.M.loaded_segments (0x3c604 : word) = Some W_3c604.
Proof. vm_refl. Qed.
Lemma D_3c604 : decode_any W_3c604 = Some (OpImm ALU_ADD 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c608 : bv 32 := 0x02400613.
Lemma F_3c608 : fetch_word Plain.M.loaded_segments (0x3c608 : word) = Some W_3c608.
Proof. vm_refl. Qed.
Lemma D_3c608 : decode_any W_3c608 = Some (OpImm ALU_ADD 12 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c60c : bv 32 := 0x00000593.
Lemma F_3c60c : fetch_word Plain.M.loaded_segments (0x3c60c : word) = Some W_3c60c.
Proof. vm_refl. Qed.
Lemma D_3c60c : decode_any W_3c60c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c610 : bv 32 := 0x194390ef.
Lemma F_3c610 : fetch_word Plain.M.loaded_segments (0x3c610 : word) = Some W_3c610.
Proof. vm_refl. Qed.
Lemma D_3c610 : decode_any W_3c610 = Some (Jal 1 233876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c614 : bv 32 := 0x0003e517.
Lemma F_3c614 : fetch_word Plain.M.loaded_segments (0x3c614 : word) = Some W_3c614.
Proof. vm_refl. Qed.
Lemma D_3c614 : decode_any W_3c614 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c618 : bv 32 := 0x72c50513.
Lemma F_3c618 : fetch_word Plain.M.loaded_segments (0x3c618 : word) = Some W_3c618.
Proof. vm_refl. Qed.
Lemma D_3c618 : decode_any W_3c618 = Some (OpImm ALU_ADD 10 10 1836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c61c : bv 32 := 0x00a93023.
Lemma F_3c61c : fetch_word Plain.M.loaded_segments (0x3c61c : word) = Some W_3c61c.
Proof. vm_refl. Qed.
Lemma D_3c61c : decode_any W_3c61c = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c620 : bv 32 := 0x00054517.
Lemma F_3c620 : fetch_word Plain.M.loaded_segments (0x3c620 : word) = Some W_3c620.
Proof. vm_refl. Qed.
Lemma D_3c620 : decode_any W_3c620 = Some (Auipc 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c624 : bv 32 := 0x74850513.
Lemma F_3c624 : fetch_word Plain.M.loaded_segments (0x3c624 : word) = Some W_3c624.
Proof. vm_refl. Qed.
Lemma D_3c624 : decode_any W_3c624 = Some (OpImm ALU_ADD 10 10 1864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c628 : bv 32 := 0x0d0000ef.
Lemma F_3c628 : fetch_word Plain.M.loaded_segments (0x3c628 : word) = Some W_3c628.
Proof. vm_refl. Qed.
Lemma D_3c628 : decode_any W_3c628 = Some (Jal 1 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c62c : bv 32 := 0xf55ff06f.
Lemma F_3c62c : fetch_word Plain.M.loaded_segments (0x3c62c : word) = Some W_3c62c.
Proof. vm_refl. Qed.
Lemma D_3c62c : decode_any W_3c62c = Some (Jal 0 2096980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c630 : bv 32 := 0x00853603.
Lemma F_3c630 : fetch_word Plain.M.loaded_segments (0x3c630 : word) = Some W_3c630.
Proof. vm_refl. Qed.
Lemma D_3c630 : decode_any W_3c630 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c634 : bv 32 := 0x01053703.
Lemma F_3c634 : fetch_word Plain.M.loaded_segments (0x3c634 : word) = Some W_3c634.
Proof. vm_refl. Qed.
Lemma D_3c634 : decode_any W_3c634 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c638 : bv 32 := 0x02853683.
Lemma F_3c638 : fetch_word Plain.M.loaded_segments (0x3c638 : word) = Some W_3c638.
Proof. vm_refl. Qed.
Lemma D_3c638 : decode_any W_3c638 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c63c : bv 32 := 0x40c70633.
Lemma F_3c63c : fetch_word Plain.M.loaded_segments (0x3c63c : word) = Some W_3c63c.
Proof. vm_refl. Qed.
Lemma D_3c63c : decode_any W_3c63c = Some (Op ALU_SUB 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c640 : bv 32 := 0x04c6e063.
Lemma F_3c640 : fetch_word Plain.M.loaded_segments (0x3c640 : word) = Some W_3c640.
Proof. vm_refl. Qed.
Lemma D_3c640 : decode_any W_3c640 = Some (Branch BC_LTU 13 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c644 : bv 32 := 0x00053703.
Lemma F_3c644 : fetch_word Plain.M.loaded_segments (0x3c644 : word) = Some W_3c644.
Proof. vm_refl. Qed.
Lemma D_3c644 : decode_any W_3c644 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c648 : bv 32 := 0x02053783.
Lemma F_3c648 : fetch_word Plain.M.loaded_segments (0x3c648 : word) = Some W_3c648.
Proof. vm_refl. Qed.
Lemma D_3c648 : decode_any W_3c648 = Some (Load SZ8 true 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c64c : bv 32 := 0x40c68533.
Lemma F_3c64c : fetch_word Plain.M.loaded_segments (0x3c64c : word) = Some W_3c64c.
Proof. vm_refl. Qed.
Lemma D_3c64c : decode_any W_3c64c = Some (Op ALU_SUB 10 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c650 : bv 32 := 0x40e787b3.
Lemma F_3c650 : fetch_word Plain.M.loaded_segments (0x3c650 : word) = Some W_3c650.
Proof. vm_refl. Qed.
Lemma D_3c650 : decode_any W_3c650 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c654 : bv 32 := 0x40c78633.
Lemma F_3c654 : fetch_word Plain.M.loaded_segments (0x3c654 : word) = Some W_3c654.
Proof. vm_refl. Qed.
Lemma D_3c654 : decode_any W_3c654 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c658 : bv 32 := 0x00b56463.
Lemma F_3c658 : fetch_word Plain.M.loaded_segments (0x3c658 : word) = Some W_3c658.
Proof. vm_refl. Qed.
Lemma D_3c658 : decode_any W_3c658 = Some (Branch BC_LTU 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c65c : bv 32 := 0x00058513.
Lemma F_3c65c : fetch_word Plain.M.loaded_segments (0x3c65c : word) = Some W_3c65c.
Proof. vm_refl. Qed.
Lemma D_3c65c : decode_any W_3c65c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c660 : bv 32 := 0x20000593.
Lemma F_3c660 : fetch_word Plain.M.loaded_segments (0x3c660 : word) = Some W_3c660.
Proof. vm_refl. Qed.
Lemma D_3c660 : decode_any W_3c660 = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c664 : bv 32 := 0x00c5f663.
Lemma F_3c664 : fetch_word Plain.M.loaded_segments (0x3c664 : word) = Some W_3c664.
Proof. vm_refl. Qed.
Lemma D_3c664 : decode_any W_3c664 = Some (Branch BC_GEU 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c668 : bv 32 := 0x00c57863.
Lemma F_3c668 : fetch_word Plain.M.loaded_segments (0x3c668 : word) = Some W_3c668.
Proof. vm_refl. Qed.
Lemma D_3c668 : decode_any W_3c668 = Some (Branch BC_GEU 10 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c66c : bv 32 := 0x00008067.
Lemma F_3c66c : fetch_word Plain.M.loaded_segments (0x3c66c : word) = Some W_3c66c.
Proof. vm_refl. Qed.
Lemma D_3c66c : decode_any W_3c66c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c670 : bv 32 := 0x20000613.
Lemma F_3c670 : fetch_word Plain.M.loaded_segments (0x3c670 : word) = Some W_3c670.
Proof. vm_refl. Qed.
Lemma D_3c670 : decode_any W_3c670 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c674 : bv 32 := 0xfec56ce3.
Lemma F_3c674 : fetch_word Plain.M.loaded_segments (0x3c674 : word) = Some W_3c674.
Proof. vm_refl. Qed.
Lemma D_3c674 : decode_any W_3c674 = Some (Branch BC_LTU 10 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c678 : bv 32 := 0x00060513.
Lemma F_3c678 : fetch_word Plain.M.loaded_segments (0x3c678 : word) = Some W_3c678.
Proof. vm_refl. Qed.
Lemma D_3c678 : decode_any W_3c678 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c67c : bv 32 := 0x00008067.
Lemma F_3c67c : fetch_word Plain.M.loaded_segments (0x3c67c : word) = Some W_3c67c.
Proof. vm_refl. Qed.
Lemma D_3c67c : decode_any W_3c67c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c680 : bv 32 := 0xff010113.
Lemma F_3c680 : fetch_word Plain.M.loaded_segments (0x3c680 : word) = Some W_3c680.
Proof. vm_refl. Qed.
Lemma D_3c680 : decode_any W_3c680 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c684 : bv 32 := 0x00113423.
Lemma F_3c684 : fetch_word Plain.M.loaded_segments (0x3c684 : word) = Some W_3c684.
Proof. vm_refl. Qed.
Lemma D_3c684 : decode_any W_3c684 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c688 : bv 32 := 0xfffd7517.
Lemma F_3c688 : fetch_word Plain.M.loaded_segments (0x3c688 : word) = Some W_3c688.
Proof. vm_refl. Qed.
Lemma D_3c688 : decode_any W_3c688 = Some (Auipc 10 1048535, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c68c : bv 32 := 0xfffd7597.
Lemma F_3c68c : fetch_word Plain.M.loaded_segments (0x3c68c : word) = Some W_3c68c.
Proof. vm_refl. Qed.
Lemma D_3c68c : decode_any W_3c68c = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c690 : bv 32 := 0xfffd7617.
Lemma F_3c690 : fetch_word Plain.M.loaded_segments (0x3c690 : word) = Some W_3c690.
Proof. vm_refl. Qed.
Lemma D_3c690 : decode_any W_3c690 = Some (Auipc 12 1048535, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c694 : bv 32 := 0xb2450513.
Lemma F_3c694 : fetch_word Plain.M.loaded_segments (0x3c694 : word) = Some W_3c694.
Proof. vm_refl. Qed.
Lemma D_3c694 : decode_any W_3c694 = Some (OpImm ALU_ADD 10 10 2852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c698 : bv 32 := 0x71458593.
Lemma F_3c698 : fetch_word Plain.M.loaded_segments (0x3c698 : word) = Some W_3c698.
Proof. vm_refl. Qed.
Lemma D_3c698 : decode_any W_3c698 = Some (OpImm ALU_ADD 11 11 1812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c69c : bv 32 := 0xd3a60693.
Lemma F_3c69c : fetch_word Plain.M.loaded_segments (0x3c69c : word) = Some W_3c69c.
Proof. vm_refl. Qed.
Lemma D_3c69c : decode_any W_3c69c = Some (OpImm ALU_ADD 13 12 3386, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6a0 : bv 32 := 0x03300613.
Lemma F_3c6a0 : fetch_word Plain.M.loaded_segments (0x3c6a0 : word) = Some W_3c6a0.
Proof. vm_refl. Qed.
Lemma D_3c6a0 : decode_any W_3c6a0 = Some (OpImm ALU_ADD 12 0 51, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6a4 : bv 32 := 0x7c12a0ef.
Lemma F_3c6a4 : fetch_word Plain.M.loaded_segments (0x3c6a4 : word) = Some W_3c6a4.
Proof. vm_refl. Qed.
Lemma D_3c6a4 : decode_any W_3c6a4 = Some (Jal 1 176064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6a8 : bv 32 := 0x00050583.
Lemma F_3c6a8 : fetch_word Plain.M.loaded_segments (0x3c6a8 : word) = Some W_3c6a8.
Proof. vm_refl. Qed.
Lemma D_3c6a8 : decode_any W_3c6a8 = Some (Load SZ1 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6ac : bv 32 := 0x0230000f.
Lemma F_3c6ac : fetch_word Plain.M.loaded_segments (0x3c6ac : word) = Some W_3c6ac.
Proof. vm_refl. Qed.
Lemma D_3c6ac : decode_any W_3c6ac = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6b0 : bv 32 := 0x00058663.
Lemma F_3c6b0 : fetch_word Plain.M.loaded_segments (0x3c6b0 : word) = Some W_3c6b0.
Proof. vm_refl. Qed.
Lemma D_3c6b0 : decode_any W_3c6b0 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6b4 : bv 32 := 0x00000513.
Lemma F_3c6b4 : fetch_word Plain.M.loaded_segments (0x3c6b4 : word) = Some W_3c6b4.
Proof. vm_refl. Qed.
Lemma D_3c6b4 : decode_any W_3c6b4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6b8 : bv 32 := 0x00008067.
Lemma F_3c6b8 : fetch_word Plain.M.loaded_segments (0x3c6b8 : word) = Some W_3c6b8.
Proof. vm_refl. Qed.
Lemma D_3c6b8 : decode_any W_3c6b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6bc : bv 32 := 0x00154583.
Lemma F_3c6bc : fetch_word Plain.M.loaded_segments (0x3c6bc : word) = Some W_3c6bc.
Proof. vm_refl. Qed.
Lemma D_3c6bc : decode_any W_3c6bc = Some (Load SZ1 false 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6c0 : bv 32 := 0x00100613.
Lemma F_3c6c0 : fetch_word Plain.M.loaded_segments (0x3c6c0 : word) = Some W_3c6c0.
Proof. vm_refl. Qed.
Lemma D_3c6c0 : decode_any W_3c6c0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6c4 : bv 32 := 0x00c58a63.
Lemma F_3c6c4 : fetch_word Plain.M.loaded_segments (0x3c6c4 : word) = Some W_3c6c4.
Proof. vm_refl. Qed.
Lemma D_3c6c4 : decode_any W_3c6c4 = Some (Branch BC_EQ 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6c8 : bv 32 := 0x0025f613.
Lemma F_3c6c8 : fetch_word Plain.M.loaded_segments (0x3c6c8 : word) = Some W_3c6c8.
Proof. vm_refl. Qed.
Lemma D_3c6c8 : decode_any W_3c6c8 = Some (OpImm ALU_AND 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6cc : bv 32 := 0x00061c63.
Lemma F_3c6cc : fetch_word Plain.M.loaded_segments (0x3c6cc : word) = Some W_3c6cc.
Proof. vm_refl. Qed.
Lemma D_3c6cc : decode_any W_3c6cc = Some (Branch BC_NE 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6d0 : bv 32 := 0x00200613.
Lemma F_3c6d0 : fetch_word Plain.M.loaded_segments (0x3c6d0 : word) = Some W_3c6d0.
Proof. vm_refl. Qed.
Lemma D_3c6d0 : decode_any W_3c6d0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6d4 : bv 32 := 0x00c500a3.
Lemma F_3c6d4 : fetch_word Plain.M.loaded_segments (0x3c6d4 : word) = Some W_3c6d4.
Proof. vm_refl. Qed.
Lemma D_3c6d4 : decode_any W_3c6d4 = Some (Store SZ1 10 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6d8 : bv 32 := 0xfff58593.
Lemma F_3c6d8 : fetch_word Plain.M.loaded_segments (0x3c6d8 : word) = Some W_3c6d8.
Proof. vm_refl. Qed.
Lemma D_3c6d8 : decode_any W_3c6d8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6dc : bv 32 := 0x00b03533.
Lemma F_3c6dc : fetch_word Plain.M.loaded_segments (0x3c6dc : word) = Some W_3c6dc.
Proof. vm_refl. Qed.
Lemma D_3c6dc : decode_any W_3c6dc = Some (Op ALU_SLTU 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6e0 : bv 32 := 0x00008067.
Lemma F_3c6e0 : fetch_word Plain.M.loaded_segments (0x3c6e0 : word) = Some W_3c6e0.
Proof. vm_refl. Qed.
Lemma D_3c6e0 : decode_any W_3c6e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6e4 : bv 32 := 0xff010113.
Lemma F_3c6e4 : fetch_word Plain.M.loaded_segments (0x3c6e4 : word) = Some W_3c6e4.
Proof. vm_refl. Qed.
Lemma D_3c6e4 : decode_any W_3c6e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6e8 : bv 32 := 0x00113423.
Lemma F_3c6e8 : fetch_word Plain.M.loaded_segments (0x3c6e8 : word) = Some W_3c6e8.
Proof. vm_refl. Qed.
Lemma D_3c6e8 : decode_any W_3c6e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6ec : bv 32 := 0xfffd8517.
Lemma F_3c6ec : fetch_word Plain.M.loaded_segments (0x3c6ec : word) = Some W_3c6ec.
Proof. vm_refl. Qed.
Lemma D_3c6ec : decode_any W_3c6ec = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6f0 : bv 32 := 0xb8550513.
Lemma F_3c6f0 : fetch_word Plain.M.loaded_segments (0x3c6f0 : word) = Some W_3c6f0.
Proof. vm_refl. Qed.
Lemma D_3c6f0 : decode_any W_3c6f0 = Some (OpImm ALU_ADD 10 10 2949, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6f4 : bv 32 := 0x4e41b0ef.
Lemma F_3c6f4 : fetch_word Plain.M.loaded_segments (0x3c6f4 : word) = Some W_3c6f4.
Proof. vm_refl. Qed.
Lemma D_3c6f4 : decode_any W_3c6f4 = Some (Jal 1 111844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6f8 : bv 32 := 0x0310000f.
Lemma F_3c6f8 : fetch_word Plain.M.loaded_segments (0x3c6f8 : word) = Some W_3c6f8.
Proof. vm_refl. Qed.
Lemma D_3c6f8 : decode_any W_3c6f8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c6fc : bv 32 := 0x00100593.
Lemma F_3c6fc : fetch_word Plain.M.loaded_segments (0x3c6fc : word) = Some W_3c6fc.
Proof. vm_refl. Qed.
Lemma D_3c6fc : decode_any W_3c6fc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c700 : bv 32 := 0x00b50023.
Lemma F_3c700 : fetch_word Plain.M.loaded_segments (0x3c700 : word) = Some W_3c700.
Proof. vm_refl. Qed.
Lemma D_3c700 : decode_any W_3c700 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c704 : bv 32 := 0x00b500a3.
Lemma F_3c704 : fetch_word Plain.M.loaded_segments (0x3c704 : word) = Some W_3c704.
Proof. vm_refl. Qed.
Lemma D_3c704 : decode_any W_3c704 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c708 : bv 32 := 0x00008067.
Lemma F_3c708 : fetch_word Plain.M.loaded_segments (0x3c708 : word) = Some W_3c708.
Proof. vm_refl. Qed.
Lemma D_3c708 : decode_any W_3c708 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
