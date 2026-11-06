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
Definition W_6ab14 : bv 32 := 0x08852603.
Lemma F_6ab14 : fetch_word Plain.M.loaded_segments (0x6ab14 : word) = Some W_6ab14.
Proof. vm_refl. Qed.
Lemma D_6ab14 : decode_any W_6ab14 = Some (Load SZ4 true 12 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab18 : bv 32 := 0x00056583.
Lemma F_6ab18 : fetch_word Plain.M.loaded_segments (0x6ab18 : word) = Some W_6ab18.
Proof. vm_refl. Qed.
Lemma D_6ab18 : decode_any W_6ab18 = Some (Load SZ4 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab1c : bv 32 := 0xfff60693.
Lemma F_6ab1c : fetch_word Plain.M.loaded_segments (0x6ab1c : word) = Some W_6ab1c.
Proof. vm_refl. Qed.
Lemma D_6ab1c : decode_any W_6ab1c = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab20 : bv 32 := 0x00c6e633.
Lemma F_6ab20 : fetch_word Plain.M.loaded_segments (0x6ab20 : word) = Some W_6ab20.
Proof. vm_refl. Qed.
Lemma D_6ab20 : decode_any W_6ab20 = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab24 : bv 32 := 0x0085f693.
Lemma F_6ab24 : fetch_word Plain.M.loaded_segments (0x6ab24 : word) = Some W_6ab24.
Proof. vm_refl. Qed.
Lemma D_6ab24 : decode_any W_6ab24 = Some (OpImm ALU_AND 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab28 : bv 32 := 0x08c52423.
Lemma F_6ab28 : fetch_word Plain.M.loaded_segments (0x6ab28 : word) = Some W_6ab28.
Proof. vm_refl. Qed.
Lemma D_6ab28 : decode_any W_6ab28 = Some (Store SZ4 10 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab2c : bv 32 := 0x02069663.
Lemma F_6ab2c : fetch_word Plain.M.loaded_segments (0x6ab2c : word) = Some W_6ab2c.
Proof. vm_refl. Qed.
Lemma D_6ab2c : decode_any W_6ab2c = Some (Branch BC_NE 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab30 : bv 32 := 0x05853603.
Lemma F_6ab30 : fetch_word Plain.M.loaded_segments (0x6ab30 : word) = Some W_6ab30.
Proof. vm_refl. Qed.
Lemma D_6ab30 : decode_any W_6ab30 = Some (Load SZ8 true 12 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab34 : bv 32 := 0x06053683.
Lemma F_6ab34 : fetch_word Plain.M.loaded_segments (0x6ab34 : word) = Some W_6ab34.
Proof. vm_refl. Qed.
Lemma D_6ab34 : decode_any W_6ab34 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab38 : bv 32 := 0x02c53c23.
Lemma F_6ab38 : fetch_word Plain.M.loaded_segments (0x6ab38 : word) = Some W_6ab38.
Proof. vm_refl. Qed.
Lemma D_6ab38 : decode_any W_6ab38 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab3c : bv 32 := 0x00d606b3.
Lemma F_6ab3c : fetch_word Plain.M.loaded_segments (0x6ab3c : word) = Some W_6ab3c.
Proof. vm_refl. Qed.
Lemma D_6ab3c : decode_any W_6ab3c = Some (Op ALU_ADD 13 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab40 : bv 32 := 0x00053423.
Lemma F_6ab40 : fetch_word Plain.M.loaded_segments (0x6ab40 : word) = Some W_6ab40.
Proof. vm_refl. Qed.
Lemma D_6ab40 : decode_any W_6ab40 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab44 : bv 32 := 0x00053823.
Lemma F_6ab44 : fetch_word Plain.M.loaded_segments (0x6ab44 : word) = Some W_6ab44.
Proof. vm_refl. Qed.
Lemma D_6ab44 : decode_any W_6ab44 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab48 : bv 32 := 0x02d53023.
Lemma F_6ab48 : fetch_word Plain.M.loaded_segments (0x6ab48 : word) = Some W_6ab48.
Proof. vm_refl. Qed.
Lemma D_6ab48 : decode_any W_6ab48 = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab4c : bv 32 := 0x02c53423.
Lemma F_6ab4c : fetch_word Plain.M.loaded_segments (0x6ab4c : word) = Some W_6ab4c.
Proof. vm_refl. Qed.
Lemma D_6ab4c : decode_any W_6ab4c = Some (Store SZ8 10 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab50 : bv 32 := 0x00000513.
Lemma F_6ab50 : fetch_word Plain.M.loaded_segments (0x6ab50 : word) = Some W_6ab50.
Proof. vm_refl. Qed.
Lemma D_6ab50 : decode_any W_6ab50 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab54 : bv 32 := 0x00008067.
Lemma F_6ab54 : fetch_word Plain.M.loaded_segments (0x6ab54 : word) = Some W_6ab54.
Proof. vm_refl. Qed.
Lemma D_6ab54 : decode_any W_6ab54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab58 : bv 32 := 0x0205e593.
Lemma F_6ab58 : fetch_word Plain.M.loaded_segments (0x6ab58 : word) = Some W_6ab58.
Proof. vm_refl. Qed.
Lemma D_6ab58 : decode_any W_6ab58 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab5c : bv 32 := 0x00b52023.
Lemma F_6ab5c : fetch_word Plain.M.loaded_segments (0x6ab5c : word) = Some W_6ab5c.
Proof. vm_refl. Qed.
Lemma D_6ab5c : decode_any W_6ab5c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab60 : bv 32 := 0xfff00513.
Lemma F_6ab60 : fetch_word Plain.M.loaded_segments (0x6ab60 : word) = Some W_6ab60.
Proof. vm_refl. Qed.
Lemma D_6ab60 : decode_any W_6ab60 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab64 : bv 32 := 0x00008067.
Lemma F_6ab64 : fetch_word Plain.M.loaded_segments (0x6ab64 : word) = Some W_6ab64.
Proof. vm_refl. Qed.
Lemma D_6ab64 : decode_any W_6ab64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab68 : bv 32 := 0xff010113.
Lemma F_6ab68 : fetch_word Plain.M.loaded_segments (0x6ab68 : word) = Some W_6ab68.
Proof. vm_refl. Qed.
Lemma D_6ab68 : decode_any W_6ab68 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab6c : bv 32 := 0x00113423.
Lemma F_6ab6c : fetch_word Plain.M.loaded_segments (0x6ab6c : word) = Some W_6ab6c.
Proof. vm_refl. Qed.
Lemma D_6ab6c : decode_any W_6ab6c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab70 : bv 32 := 0x00813023.
Lemma F_6ab70 : fetch_word Plain.M.loaded_segments (0x6ab70 : word) = Some W_6ab70.
Proof. vm_refl. Qed.
Lemma D_6ab70 : decode_any W_6ab70 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab74 : bv 32 := 0x388000ef.
Lemma F_6ab74 : fetch_word Plain.M.loaded_segments (0x6ab74 : word) = Some W_6ab74.
Proof. vm_refl. Qed.
Lemma D_6ab74 : decode_any W_6ab74 = Some (Jal 1 904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab78 : bv 32 := 0x00053403.
Lemma F_6ab78 : fetch_word Plain.M.loaded_segments (0x6ab78 : word) = Some W_6ab78.
Proof. vm_refl. Qed.
Lemma D_6ab78 : decode_any W_6ab78 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab7c : bv 32 := 0x12041663.
Lemma F_6ab7c : fetch_word Plain.M.loaded_segments (0x6ab7c : word) = Some W_6ab7c.
Proof. vm_refl. Qed.
Lemma D_6ab7c : decode_any W_6ab7c = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab80 : bv 32 := 0x00048517.
Lemma F_6ab80 : fetch_word Plain.M.loaded_segments (0x6ab80 : word) = Some W_6ab80.
Proof. vm_refl. Qed.
Lemma D_6ab80 : decode_any W_6ab80 = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab84 : bv 32 := 0x18053403.
Lemma F_6ab84 : fetch_word Plain.M.loaded_segments (0x6ab84 : word) = Some W_6ab84.
Proof. vm_refl. Qed.
Lemma D_6ab84 : decode_any W_6ab84 = Some (Load SZ8 true 8 10 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab88 : bv 32 := 0x04040a63.
Lemma F_6ab88 : fetch_word Plain.M.loaded_segments (0x6ab88 : word) = Some W_6ab88.
Proof. vm_refl. Qed.
Lemma D_6ab88 : decode_any W_6ab88 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab8c : bv 32 := 0x08c42503.
Lemma F_6ab8c : fetch_word Plain.M.loaded_segments (0x6ab8c : word) = Some W_6ab8c.
Proof. vm_refl. Qed.
Lemma D_6ab8c : decode_any W_6ab8c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab90 : bv 32 := 0x00054663.
Lemma F_6ab90 : fetch_word Plain.M.loaded_segments (0x6ab90 : word) = Some W_6ab90.
Proof. vm_refl. Qed.
Lemma D_6ab90 : decode_any W_6ab90 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab94 : bv 32 := 0x00040513.
Lemma F_6ab94 : fetch_word Plain.M.loaded_segments (0x6ab94 : word) = Some W_6ab94.
Proof. vm_refl. Qed.
Lemma D_6ab94 : decode_any W_6ab94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab98 : bv 32 := 0xb9dff0ef.
Lemma F_6ab98 : fetch_word Plain.M.loaded_segments (0x6ab98 : word) = Some W_6ab98.
Proof. vm_refl. Qed.
Lemma D_6ab98 : decode_any W_6ab98 = Some (Jal 1 2096028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ab9c : bv 32 := 0x02843503.
Lemma F_6ab9c : fetch_word Plain.M.loaded_segments (0x6ab9c : word) = Some W_6ab9c.
Proof. vm_refl. Qed.
Lemma D_6ab9c : decode_any W_6ab9c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aba0 : bv 32 := 0x03843583.
Lemma F_6aba0 : fetch_word Plain.M.loaded_segments (0x6aba0 : word) = Some W_6aba0.
Proof. vm_refl. Qed.
Lemma D_6aba0 : decode_any W_6aba0 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aba4 : bv 32 := 0x00b50c63.
Lemma F_6aba4 : fetch_word Plain.M.loaded_segments (0x6aba4 : word) = Some W_6aba4.
Proof. vm_refl. Qed.
Lemma D_6aba4 : decode_any W_6aba4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aba8 : bv 32 := 0x04843683.
Lemma F_6aba8 : fetch_word Plain.M.loaded_segments (0x6aba8 : word) = Some W_6aba8.
Proof. vm_refl. Qed.
Lemma D_6aba8 : decode_any W_6aba8 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abac : bv 32 := 0x00040513.
Lemma F_6abac : fetch_word Plain.M.loaded_segments (0x6abac : word) = Some W_6abac.
Proof. vm_refl. Qed.
Lemma D_6abac : decode_any W_6abac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abb0 : bv 32 := 0x00000593.
Lemma F_6abb0 : fetch_word Plain.M.loaded_segments (0x6abb0 : word) = Some W_6abb0.
Proof. vm_refl. Qed.
Lemma D_6abb0 : decode_any W_6abb0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abb4 : bv 32 := 0x00000613.
Lemma F_6abb4 : fetch_word Plain.M.loaded_segments (0x6abb4 : word) = Some W_6abb4.
Proof. vm_refl. Qed.
Lemma D_6abb4 : decode_any W_6abb4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abb8 : bv 32 := 0x000680e7.
Lemma F_6abb8 : fetch_word Plain.M.loaded_segments (0x6abb8 : word) = Some W_6abb8.
Proof. vm_refl. Qed.
Lemma D_6abb8 : decode_any W_6abb8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abbc : bv 32 := 0x00843503.
Lemma F_6abbc : fetch_word Plain.M.loaded_segments (0x6abbc : word) = Some W_6abbc.
Proof. vm_refl. Qed.
Lemma D_6abbc : decode_any W_6abbc = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abc0 : bv 32 := 0x01043583.
Lemma F_6abc0 : fetch_word Plain.M.loaded_segments (0x6abc0 : word) = Some W_6abc0.
Proof. vm_refl. Qed.
Lemma D_6abc0 : decode_any W_6abc0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abc4 : bv 32 := 0x00b50c63.
Lemma F_6abc4 : fetch_word Plain.M.loaded_segments (0x6abc4 : word) = Some W_6abc4.
Proof. vm_refl. Qed.
Lemma D_6abc4 : decode_any W_6abc4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abc8 : bv 32 := 0x05043683.
Lemma F_6abc8 : fetch_word Plain.M.loaded_segments (0x6abc8 : word) = Some W_6abc8.
Proof. vm_refl. Qed.
Lemma D_6abc8 : decode_any W_6abc8 = Some (Load SZ8 true 13 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abcc : bv 32 := 0x40b505b3.
Lemma F_6abcc : fetch_word Plain.M.loaded_segments (0x6abcc : word) = Some W_6abcc.
Proof. vm_refl. Qed.
Lemma D_6abcc : decode_any W_6abcc = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abd0 : bv 32 := 0x00100613.
Lemma F_6abd0 : fetch_word Plain.M.loaded_segments (0x6abd0 : word) = Some W_6abd0.
Proof. vm_refl. Qed.
Lemma D_6abd0 : decode_any W_6abd0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abd4 : bv 32 := 0x00040513.
Lemma F_6abd4 : fetch_word Plain.M.loaded_segments (0x6abd4 : word) = Some W_6abd4.
Proof. vm_refl. Qed.
Lemma D_6abd4 : decode_any W_6abd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abd8 : bv 32 := 0x000680e7.
Lemma F_6abd8 : fetch_word Plain.M.loaded_segments (0x6abd8 : word) = Some W_6abd8.
Proof. vm_refl. Qed.
Lemma D_6abd8 : decode_any W_6abd8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abdc : bv 32 := 0x00016517.
Lemma F_6abdc : fetch_word Plain.M.loaded_segments (0x6abdc : word) = Some W_6abdc.
Proof. vm_refl. Qed.
Lemma D_6abdc : decode_any W_6abdc = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abe0 : bv 32 := 0x01c53403.
Lemma F_6abe0 : fetch_word Plain.M.loaded_segments (0x6abe0 : word) = Some W_6abe0.
Proof. vm_refl. Qed.
Lemma D_6abe0 : decode_any W_6abe0 = Some (Load SZ8 true 8 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abe4 : bv 32 := 0x04040a63.
Lemma F_6abe4 : fetch_word Plain.M.loaded_segments (0x6abe4 : word) = Some W_6abe4.
Proof. vm_refl. Qed.
Lemma D_6abe4 : decode_any W_6abe4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abe8 : bv 32 := 0x08c42503.
Lemma F_6abe8 : fetch_word Plain.M.loaded_segments (0x6abe8 : word) = Some W_6abe8.
Proof. vm_refl. Qed.
Lemma D_6abe8 : decode_any W_6abe8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abec : bv 32 := 0x00054663.
Lemma F_6abec : fetch_word Plain.M.loaded_segments (0x6abec : word) = Some W_6abec.
Proof. vm_refl. Qed.
Lemma D_6abec : decode_any W_6abec = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abf0 : bv 32 := 0x00040513.
Lemma F_6abf0 : fetch_word Plain.M.loaded_segments (0x6abf0 : word) = Some W_6abf0.
Proof. vm_refl. Qed.
Lemma D_6abf0 : decode_any W_6abf0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abf4 : bv 32 := 0xb41ff0ef.
Lemma F_6abf4 : fetch_word Plain.M.loaded_segments (0x6abf4 : word) = Some W_6abf4.
Proof. vm_refl. Qed.
Lemma D_6abf4 : decode_any W_6abf4 = Some (Jal 1 2095936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abf8 : bv 32 := 0x02843503.
Lemma F_6abf8 : fetch_word Plain.M.loaded_segments (0x6abf8 : word) = Some W_6abf8.
Proof. vm_refl. Qed.
Lemma D_6abf8 : decode_any W_6abf8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6abfc : bv 32 := 0x03843583.
Lemma F_6abfc : fetch_word Plain.M.loaded_segments (0x6abfc : word) = Some W_6abfc.
Proof. vm_refl. Qed.
Lemma D_6abfc : decode_any W_6abfc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac00 : bv 32 := 0x00b50c63.
Lemma F_6ac00 : fetch_word Plain.M.loaded_segments (0x6ac00 : word) = Some W_6ac00.
Proof. vm_refl. Qed.
Lemma D_6ac00 : decode_any W_6ac00 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac04 : bv 32 := 0x04843683.
Lemma F_6ac04 : fetch_word Plain.M.loaded_segments (0x6ac04 : word) = Some W_6ac04.
Proof. vm_refl. Qed.
Lemma D_6ac04 : decode_any W_6ac04 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac08 : bv 32 := 0x00040513.
Lemma F_6ac08 : fetch_word Plain.M.loaded_segments (0x6ac08 : word) = Some W_6ac08.
Proof. vm_refl. Qed.
Lemma D_6ac08 : decode_any W_6ac08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac0c : bv 32 := 0x00000593.
Lemma F_6ac0c : fetch_word Plain.M.loaded_segments (0x6ac0c : word) = Some W_6ac0c.
Proof. vm_refl. Qed.
Lemma D_6ac0c : decode_any W_6ac0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac10 : bv 32 := 0x00000613.
Lemma F_6ac10 : fetch_word Plain.M.loaded_segments (0x6ac10 : word) = Some W_6ac10.
Proof. vm_refl. Qed.
Lemma D_6ac10 : decode_any W_6ac10 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac14 : bv 32 := 0x000680e7.
Lemma F_6ac14 : fetch_word Plain.M.loaded_segments (0x6ac14 : word) = Some W_6ac14.
Proof. vm_refl. Qed.
Lemma D_6ac14 : decode_any W_6ac14 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac18 : bv 32 := 0x00843503.
Lemma F_6ac18 : fetch_word Plain.M.loaded_segments (0x6ac18 : word) = Some W_6ac18.
Proof. vm_refl. Qed.
Lemma D_6ac18 : decode_any W_6ac18 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac1c : bv 32 := 0x01043583.
Lemma F_6ac1c : fetch_word Plain.M.loaded_segments (0x6ac1c : word) = Some W_6ac1c.
Proof. vm_refl. Qed.
Lemma D_6ac1c : decode_any W_6ac1c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac20 : bv 32 := 0x00b50c63.
Lemma F_6ac20 : fetch_word Plain.M.loaded_segments (0x6ac20 : word) = Some W_6ac20.
Proof. vm_refl. Qed.
Lemma D_6ac20 : decode_any W_6ac20 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac24 : bv 32 := 0x05043683.
Lemma F_6ac24 : fetch_word Plain.M.loaded_segments (0x6ac24 : word) = Some W_6ac24.
Proof. vm_refl. Qed.
Lemma D_6ac24 : decode_any W_6ac24 = Some (Load SZ8 true 13 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac28 : bv 32 := 0x40b505b3.
Lemma F_6ac28 : fetch_word Plain.M.loaded_segments (0x6ac28 : word) = Some W_6ac28.
Proof. vm_refl. Qed.
Lemma D_6ac28 : decode_any W_6ac28 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac2c : bv 32 := 0x00100613.
Lemma F_6ac2c : fetch_word Plain.M.loaded_segments (0x6ac2c : word) = Some W_6ac2c.
Proof. vm_refl. Qed.
Lemma D_6ac2c : decode_any W_6ac2c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac30 : bv 32 := 0x00040513.
Lemma F_6ac30 : fetch_word Plain.M.loaded_segments (0x6ac30 : word) = Some W_6ac30.
Proof. vm_refl. Qed.
Lemma D_6ac30 : decode_any W_6ac30 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac34 : bv 32 := 0x000680e7.
Lemma F_6ac34 : fetch_word Plain.M.loaded_segments (0x6ac34 : word) = Some W_6ac34.
Proof. vm_refl. Qed.
Lemma D_6ac34 : decode_any W_6ac34 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac38 : bv 32 := 0x00016517.
Lemma F_6ac38 : fetch_word Plain.M.loaded_segments (0x6ac38 : word) = Some W_6ac38.
Proof. vm_refl. Qed.
Lemma D_6ac38 : decode_any W_6ac38 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac3c : bv 32 := 0xed053403.
Lemma F_6ac3c : fetch_word Plain.M.loaded_segments (0x6ac3c : word) = Some W_6ac3c.
Proof. vm_refl. Qed.
Lemma D_6ac3c : decode_any W_6ac3c = Some (Load SZ8 true 8 10 3792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac40 : bv 32 := 0x0a040e63.
Lemma F_6ac40 : fetch_word Plain.M.loaded_segments (0x6ac40 : word) = Some W_6ac40.
Proof. vm_refl. Qed.
Lemma D_6ac40 : decode_any W_6ac40 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac44 : bv 32 := 0x08c42503.
Lemma F_6ac44 : fetch_word Plain.M.loaded_segments (0x6ac44 : word) = Some W_6ac44.
Proof. vm_refl. Qed.
Lemma D_6ac44 : decode_any W_6ac44 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac48 : bv 32 := 0x00054663.
Lemma F_6ac48 : fetch_word Plain.M.loaded_segments (0x6ac48 : word) = Some W_6ac48.
Proof. vm_refl. Qed.
Lemma D_6ac48 : decode_any W_6ac48 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac4c : bv 32 := 0x00040513.
Lemma F_6ac4c : fetch_word Plain.M.loaded_segments (0x6ac4c : word) = Some W_6ac4c.
Proof. vm_refl. Qed.
Lemma D_6ac4c : decode_any W_6ac4c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac50 : bv 32 := 0xae5ff0ef.
Lemma F_6ac50 : fetch_word Plain.M.loaded_segments (0x6ac50 : word) = Some W_6ac50.
Proof. vm_refl. Qed.
Lemma D_6ac50 : decode_any W_6ac50 = Some (Jal 1 2095844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac54 : bv 32 := 0x02843503.
Lemma F_6ac54 : fetch_word Plain.M.loaded_segments (0x6ac54 : word) = Some W_6ac54.
Proof. vm_refl. Qed.
Lemma D_6ac54 : decode_any W_6ac54 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac58 : bv 32 := 0x03843583.
Lemma F_6ac58 : fetch_word Plain.M.loaded_segments (0x6ac58 : word) = Some W_6ac58.
Proof. vm_refl. Qed.
Lemma D_6ac58 : decode_any W_6ac58 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac5c : bv 32 := 0x00b50c63.
Lemma F_6ac5c : fetch_word Plain.M.loaded_segments (0x6ac5c : word) = Some W_6ac5c.
Proof. vm_refl. Qed.
Lemma D_6ac5c : decode_any W_6ac5c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac60 : bv 32 := 0x04843683.
Lemma F_6ac60 : fetch_word Plain.M.loaded_segments (0x6ac60 : word) = Some W_6ac60.
Proof. vm_refl. Qed.
Lemma D_6ac60 : decode_any W_6ac60 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac64 : bv 32 := 0x00040513.
Lemma F_6ac64 : fetch_word Plain.M.loaded_segments (0x6ac64 : word) = Some W_6ac64.
Proof. vm_refl. Qed.
Lemma D_6ac64 : decode_any W_6ac64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac68 : bv 32 := 0x00000593.
Lemma F_6ac68 : fetch_word Plain.M.loaded_segments (0x6ac68 : word) = Some W_6ac68.
Proof. vm_refl. Qed.
Lemma D_6ac68 : decode_any W_6ac68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac6c : bv 32 := 0x00000613.
Lemma F_6ac6c : fetch_word Plain.M.loaded_segments (0x6ac6c : word) = Some W_6ac6c.
Proof. vm_refl. Qed.
Lemma D_6ac6c : decode_any W_6ac6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac70 : bv 32 := 0x000680e7.
Lemma F_6ac70 : fetch_word Plain.M.loaded_segments (0x6ac70 : word) = Some W_6ac70.
Proof. vm_refl. Qed.
Lemma D_6ac70 : decode_any W_6ac70 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac74 : bv 32 := 0x00843503.
Lemma F_6ac74 : fetch_word Plain.M.loaded_segments (0x6ac74 : word) = Some W_6ac74.
Proof. vm_refl. Qed.
Lemma D_6ac74 : decode_any W_6ac74 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac78 : bv 32 := 0x01043583.
Lemma F_6ac78 : fetch_word Plain.M.loaded_segments (0x6ac78 : word) = Some W_6ac78.
Proof. vm_refl. Qed.
Lemma D_6ac78 : decode_any W_6ac78 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac7c : bv 32 := 0x08b50063.
Lemma F_6ac7c : fetch_word Plain.M.loaded_segments (0x6ac7c : word) = Some W_6ac7c.
Proof. vm_refl. Qed.
Lemma D_6ac7c : decode_any W_6ac7c = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac80 : bv 32 := 0x05043303.
Lemma F_6ac80 : fetch_word Plain.M.loaded_segments (0x6ac80 : word) = Some W_6ac80.
Proof. vm_refl. Qed.
Lemma D_6ac80 : decode_any W_6ac80 = Some (Load SZ8 true 6 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac84 : bv 32 := 0x40b505b3.
Lemma F_6ac84 : fetch_word Plain.M.loaded_segments (0x6ac84 : word) = Some W_6ac84.
Proof. vm_refl. Qed.
Lemma D_6ac84 : decode_any W_6ac84 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac88 : bv 32 := 0x00100613.
Lemma F_6ac88 : fetch_word Plain.M.loaded_segments (0x6ac88 : word) = Some W_6ac88.
Proof. vm_refl. Qed.
Lemma D_6ac88 : decode_any W_6ac88 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac8c : bv 32 := 0x00040513.
Lemma F_6ac8c : fetch_word Plain.M.loaded_segments (0x6ac8c : word) = Some W_6ac8c.
Proof. vm_refl. Qed.
Lemma D_6ac8c : decode_any W_6ac8c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac90 : bv 32 := 0x00813083.
Lemma F_6ac90 : fetch_word Plain.M.loaded_segments (0x6ac90 : word) = Some W_6ac90.
Proof. vm_refl. Qed.
Lemma D_6ac90 : decode_any W_6ac90 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac94 : bv 32 := 0x00013403.
Lemma F_6ac94 : fetch_word Plain.M.loaded_segments (0x6ac94 : word) = Some W_6ac94.
Proof. vm_refl. Qed.
Lemma D_6ac94 : decode_any W_6ac94 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac98 : bv 32 := 0x01010113.
Lemma F_6ac98 : fetch_word Plain.M.loaded_segments (0x6ac98 : word) = Some W_6ac98.
Proof. vm_refl. Qed.
Lemma D_6ac98 : decode_any W_6ac98 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac9c : bv 32 := 0x00030067.
Lemma F_6ac9c : fetch_word Plain.M.loaded_segments (0x6ac9c : word) = Some W_6ac9c.
Proof. vm_refl. Qed.
Lemma D_6ac9c : decode_any W_6ac9c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aca0 : bv 32 := 0x07043403.
Lemma F_6aca0 : fetch_word Plain.M.loaded_segments (0x6aca0 : word) = Some W_6aca0.
Proof. vm_refl. Qed.
Lemma D_6aca0 : decode_any W_6aca0 = Some (Load SZ8 true 8 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aca4 : bv 32 := 0xec040ee3.
Lemma F_6aca4 : fetch_word Plain.M.loaded_segments (0x6aca4 : word) = Some W_6aca4.
Proof. vm_refl. Qed.
Lemma D_6aca4 : decode_any W_6aca4 = Some (Branch BC_EQ 8 0 7900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aca8 : bv 32 := 0x08c42503.
Lemma F_6aca8 : fetch_word Plain.M.loaded_segments (0x6aca8 : word) = Some W_6aca8.
Proof. vm_refl. Qed.
Lemma D_6aca8 : decode_any W_6aca8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acac : bv 32 := 0x00054663.
Lemma F_6acac : fetch_word Plain.M.loaded_segments (0x6acac : word) = Some W_6acac.
Proof. vm_refl. Qed.
Lemma D_6acac : decode_any W_6acac = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acb0 : bv 32 := 0x00040513.
Lemma F_6acb0 : fetch_word Plain.M.loaded_segments (0x6acb0 : word) = Some W_6acb0.
Proof. vm_refl. Qed.
Lemma D_6acb0 : decode_any W_6acb0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acb4 : bv 32 := 0xa81ff0ef.
Lemma F_6acb4 : fetch_word Plain.M.loaded_segments (0x6acb4 : word) = Some W_6acb4.
Proof. vm_refl. Qed.
Lemma D_6acb4 : decode_any W_6acb4 = Some (Jal 1 2095744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acb8 : bv 32 := 0x02843503.
Lemma F_6acb8 : fetch_word Plain.M.loaded_segments (0x6acb8 : word) = Some W_6acb8.
Proof. vm_refl. Qed.
Lemma D_6acb8 : decode_any W_6acb8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acbc : bv 32 := 0x03843583.
Lemma F_6acbc : fetch_word Plain.M.loaded_segments (0x6acbc : word) = Some W_6acbc.
Proof. vm_refl. Qed.
Lemma D_6acbc : decode_any W_6acbc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acc0 : bv 32 := 0x00b50c63.
Lemma F_6acc0 : fetch_word Plain.M.loaded_segments (0x6acc0 : word) = Some W_6acc0.
Proof. vm_refl. Qed.
Lemma D_6acc0 : decode_any W_6acc0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acc4 : bv 32 := 0x04843683.
Lemma F_6acc4 : fetch_word Plain.M.loaded_segments (0x6acc4 : word) = Some W_6acc4.
Proof. vm_refl. Qed.
Lemma D_6acc4 : decode_any W_6acc4 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acc8 : bv 32 := 0x00040513.
Lemma F_6acc8 : fetch_word Plain.M.loaded_segments (0x6acc8 : word) = Some W_6acc8.
Proof. vm_refl. Qed.
Lemma D_6acc8 : decode_any W_6acc8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6accc : bv 32 := 0x00000593.
Lemma F_6accc : fetch_word Plain.M.loaded_segments (0x6accc : word) = Some W_6accc.
Proof. vm_refl. Qed.
Lemma D_6accc : decode_any W_6accc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acd0 : bv 32 := 0x00000613.
Lemma F_6acd0 : fetch_word Plain.M.loaded_segments (0x6acd0 : word) = Some W_6acd0.
Proof. vm_refl. Qed.
Lemma D_6acd0 : decode_any W_6acd0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acd4 : bv 32 := 0x000680e7.
Lemma F_6acd4 : fetch_word Plain.M.loaded_segments (0x6acd4 : word) = Some W_6acd4.
Proof. vm_refl. Qed.
Lemma D_6acd4 : decode_any W_6acd4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acd8 : bv 32 := 0x00843503.
Lemma F_6acd8 : fetch_word Plain.M.loaded_segments (0x6acd8 : word) = Some W_6acd8.
Proof. vm_refl. Qed.
Lemma D_6acd8 : decode_any W_6acd8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acdc : bv 32 := 0x01043583.
Lemma F_6acdc : fetch_word Plain.M.loaded_segments (0x6acdc : word) = Some W_6acdc.
Proof. vm_refl. Qed.
Lemma D_6acdc : decode_any W_6acdc = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ace0 : bv 32 := 0xfcb500e3.
Lemma F_6ace0 : fetch_word Plain.M.loaded_segments (0x6ace0 : word) = Some W_6ace0.
Proof. vm_refl. Qed.
Lemma D_6ace0 : decode_any W_6ace0 = Some (Branch BC_EQ 10 11 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ace4 : bv 32 := 0x05043683.
Lemma F_6ace4 : fetch_word Plain.M.loaded_segments (0x6ace4 : word) = Some W_6ace4.
Proof. vm_refl. Qed.
Lemma D_6ace4 : decode_any W_6ace4 = Some (Load SZ8 true 13 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ace8 : bv 32 := 0x40b505b3.
Lemma F_6ace8 : fetch_word Plain.M.loaded_segments (0x6ace8 : word) = Some W_6ace8.
Proof. vm_refl. Qed.
Lemma D_6ace8 : decode_any W_6ace8 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acec : bv 32 := 0x00100613.
Lemma F_6acec : fetch_word Plain.M.loaded_segments (0x6acec : word) = Some W_6acec.
Proof. vm_refl. Qed.
Lemma D_6acec : decode_any W_6acec = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acf0 : bv 32 := 0x00040513.
Lemma F_6acf0 : fetch_word Plain.M.loaded_segments (0x6acf0 : word) = Some W_6acf0.
Proof. vm_refl. Qed.
Lemma D_6acf0 : decode_any W_6acf0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acf4 : bv 32 := 0x000680e7.
Lemma F_6acf4 : fetch_word Plain.M.loaded_segments (0x6acf4 : word) = Some W_6acf4.
Proof. vm_refl. Qed.
Lemma D_6acf4 : decode_any W_6acf4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acf8 : bv 32 := 0xfa9ff06f.
Lemma F_6acf8 : fetch_word Plain.M.loaded_segments (0x6acf8 : word) = Some W_6acf8.
Proof. vm_refl. Qed.
Lemma D_6acf8 : decode_any W_6acf8 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acfc : bv 32 := 0x00813083.
Lemma F_6acfc : fetch_word Plain.M.loaded_segments (0x6acfc : word) = Some W_6acfc.
Proof. vm_refl. Qed.
Lemma D_6acfc : decode_any W_6acfc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad00 : bv 32 := 0x00013403.
Lemma F_6ad00 : fetch_word Plain.M.loaded_segments (0x6ad00 : word) = Some W_6ad00.
Proof. vm_refl. Qed.
Lemma D_6ad00 : decode_any W_6ad00 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad04 : bv 32 := 0x01010113.
Lemma F_6ad04 : fetch_word Plain.M.loaded_segments (0x6ad04 : word) = Some W_6ad04.
Proof. vm_refl. Qed.
Lemma D_6ad04 : decode_any W_6ad04 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad08 : bv 32 := 0x00008067.
Lemma F_6ad08 : fetch_word Plain.M.loaded_segments (0x6ad08 : word) = Some W_6ad08.
Proof. vm_refl. Qed.
Lemma D_6ad08 : decode_any W_6ad08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad0c : bv 32 := 0xfc010113.
Lemma F_6ad0c : fetch_word Plain.M.loaded_segments (0x6ad0c : word) = Some W_6ad0c.
Proof. vm_refl. Qed.
Lemma D_6ad0c : decode_any W_6ad0c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad10 : bv 32 := 0x02113c23.
Lemma F_6ad10 : fetch_word Plain.M.loaded_segments (0x6ad10 : word) = Some W_6ad10.
Proof. vm_refl. Qed.
Lemma D_6ad10 : decode_any W_6ad10 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad14 : bv 32 := 0x02813823.
Lemma F_6ad14 : fetch_word Plain.M.loaded_segments (0x6ad14 : word) = Some W_6ad14.
Proof. vm_refl. Qed.
Lemma D_6ad14 : decode_any W_6ad14 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad18 : bv 32 := 0x02913423.
Lemma F_6ad18 : fetch_word Plain.M.loaded_segments (0x6ad18 : word) = Some W_6ad18.
Proof. vm_refl. Qed.
Lemma D_6ad18 : decode_any W_6ad18 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad1c : bv 32 := 0x03213023.
Lemma F_6ad1c : fetch_word Plain.M.loaded_segments (0x6ad1c : word) = Some W_6ad1c.
Proof. vm_refl. Qed.
Lemma D_6ad1c : decode_any W_6ad1c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad20 : bv 32 := 0x01313c23.
Lemma F_6ad20 : fetch_word Plain.M.loaded_segments (0x6ad20 : word) = Some W_6ad20.
Proof. vm_refl. Qed.
Lemma D_6ad20 : decode_any W_6ad20 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad24 : bv 32 := 0x01413823.
Lemma F_6ad24 : fetch_word Plain.M.loaded_segments (0x6ad24 : word) = Some W_6ad24.
Proof. vm_refl. Qed.
Lemma D_6ad24 : decode_any W_6ad24 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad28 : bv 32 := 0x01513423.
Lemma F_6ad28 : fetch_word Plain.M.loaded_segments (0x6ad28 : word) = Some W_6ad28.
Proof. vm_refl. Qed.
Lemma D_6ad28 : decode_any W_6ad28 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad2c : bv 32 := 0x00060413.
Lemma F_6ad2c : fetch_word Plain.M.loaded_segments (0x6ad2c : word) = Some W_6ad2c.
Proof. vm_refl. Qed.
Lemma D_6ad2c : decode_any W_6ad2c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad30 : bv 32 := 0x00058493.
Lemma F_6ad30 : fetch_word Plain.M.loaded_segments (0x6ad30 : word) = Some W_6ad30.
Proof. vm_refl. Qed.
Lemma D_6ad30 : decode_any W_6ad30 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad34 : bv 32 := 0x02063583.
Lemma F_6ad34 : fetch_word Plain.M.loaded_segments (0x6ad34 : word) = Some W_6ad34.
Proof. vm_refl. Qed.
Lemma D_6ad34 : decode_any W_6ad34 = Some (Load SZ8 true 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad38 : bv 32 := 0x00050913.
Lemma F_6ad38 : fetch_word Plain.M.loaded_segments (0x6ad38 : word) = Some W_6ad38.
Proof. vm_refl. Qed.
Lemma D_6ad38 : decode_any W_6ad38 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad3c : bv 32 := 0x08058263.
Lemma F_6ad3c : fetch_word Plain.M.loaded_segments (0x6ad3c : word) = Some W_6ad3c.
Proof. vm_refl. Qed.
Lemma D_6ad3c : decode_any W_6ad3c = Some (Branch BC_EQ 11 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad40 : bv 32 := 0x02843503.
Lemma F_6ad40 : fetch_word Plain.M.loaded_segments (0x6ad40 : word) = Some W_6ad40.
Proof. vm_refl. Qed.
Lemma D_6ad40 : decode_any W_6ad40 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad44 : bv 32 := 0x40a585b3.
Lemma F_6ad44 : fetch_word Plain.M.loaded_segments (0x6ad44 : word) = Some W_6ad44.
Proof. vm_refl. Qed.
Lemma D_6ad44 : decode_any W_6ad44 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad48 : bv 32 := 0x0295fc63.
Lemma F_6ad48 : fetch_word Plain.M.loaded_segments (0x6ad48 : word) = Some W_6ad48.
Proof. vm_refl. Qed.
Lemma D_6ad48 : decode_any W_6ad48 = Some (Branch BC_GEU 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad4c : bv 32 := 0x04843303.
Lemma F_6ad4c : fetch_word Plain.M.loaded_segments (0x6ad4c : word) = Some W_6ad4c.
Proof. vm_refl. Qed.
Lemma D_6ad4c : decode_any W_6ad4c = Some (Load SZ8 true 6 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad50 : bv 32 := 0x00040513.
Lemma F_6ad50 : fetch_word Plain.M.loaded_segments (0x6ad50 : word) = Some W_6ad50.
Proof. vm_refl. Qed.
Lemma D_6ad50 : decode_any W_6ad50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad54 : bv 32 := 0x00090593.
Lemma F_6ad54 : fetch_word Plain.M.loaded_segments (0x6ad54 : word) = Some W_6ad54.
Proof. vm_refl. Qed.
Lemma D_6ad54 : decode_any W_6ad54 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad58 : bv 32 := 0x00048613.
Lemma F_6ad58 : fetch_word Plain.M.loaded_segments (0x6ad58 : word) = Some W_6ad58.
Proof. vm_refl. Qed.
Lemma D_6ad58 : decode_any W_6ad58 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad5c : bv 32 := 0x03813083.
Lemma F_6ad5c : fetch_word Plain.M.loaded_segments (0x6ad5c : word) = Some W_6ad5c.
Proof. vm_refl. Qed.
Lemma D_6ad5c : decode_any W_6ad5c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad60 : bv 32 := 0x03013403.
Lemma F_6ad60 : fetch_word Plain.M.loaded_segments (0x6ad60 : word) = Some W_6ad60.
Proof. vm_refl. Qed.
Lemma D_6ad60 : decode_any W_6ad60 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad64 : bv 32 := 0x02813483.
Lemma F_6ad64 : fetch_word Plain.M.loaded_segments (0x6ad64 : word) = Some W_6ad64.
Proof. vm_refl. Qed.
Lemma D_6ad64 : decode_any W_6ad64 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad68 : bv 32 := 0x02013903.
Lemma F_6ad68 : fetch_word Plain.M.loaded_segments (0x6ad68 : word) = Some W_6ad68.
Proof. vm_refl. Qed.
Lemma D_6ad68 : decode_any W_6ad68 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad6c : bv 32 := 0x01813983.
Lemma F_6ad6c : fetch_word Plain.M.loaded_segments (0x6ad6c : word) = Some W_6ad6c.
Proof. vm_refl. Qed.
Lemma D_6ad6c : decode_any W_6ad6c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad70 : bv 32 := 0x01013a03.
Lemma F_6ad70 : fetch_word Plain.M.loaded_segments (0x6ad70 : word) = Some W_6ad70.
Proof. vm_refl. Qed.
Lemma D_6ad70 : decode_any W_6ad70 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad74 : bv 32 := 0x00813a83.
Lemma F_6ad74 : fetch_word Plain.M.loaded_segments (0x6ad74 : word) = Some W_6ad74.
Proof. vm_refl. Qed.
Lemma D_6ad74 : decode_any W_6ad74 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad78 : bv 32 := 0x04010113.
Lemma F_6ad78 : fetch_word Plain.M.loaded_segments (0x6ad78 : word) = Some W_6ad78.
Proof. vm_refl. Qed.
Lemma D_6ad78 : decode_any W_6ad78 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad7c : bv 32 := 0x00030067.
Lemma F_6ad7c : fetch_word Plain.M.loaded_segments (0x6ad7c : word) = Some W_6ad7c.
Proof. vm_refl. Qed.
Lemma D_6ad7c : decode_any W_6ad7c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad80 : bv 32 := 0x09042583.
Lemma F_6ad80 : fetch_word Plain.M.loaded_segments (0x6ad80 : word) = Some W_6ad80.
Proof. vm_refl. Qed.
Lemma D_6ad80 : decode_any W_6ad80 = Some (Load SZ4 true 11 8 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad84 : bv 32 := 0x00000993.
Lemma F_6ad84 : fetch_word Plain.M.loaded_segments (0x6ad84 : word) = Some W_6ad84.
Proof. vm_refl. Qed.
Lemma D_6ad84 : decode_any W_6ad84 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad88 : bv 32 := 0x0605ce63.
Lemma F_6ad88 : fetch_word Plain.M.loaded_segments (0x6ad88 : word) = Some W_6ad88.
Proof. vm_refl. Qed.
Lemma D_6ad88 : decode_any W_6ad88 = Some (Branch BC_LT 11 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad8c : bv 32 := 0x06048c63.
Lemma F_6ad8c : fetch_word Plain.M.loaded_segments (0x6ad8c : word) = Some W_6ad8c.
Proof. vm_refl. Qed.
Lemma D_6ad8c : decode_any W_6ad8c = Some (Branch BC_EQ 9 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad90 : bv 32 := 0x00000a13.
Lemma F_6ad90 : fetch_word Plain.M.loaded_segments (0x6ad90 : word) = Some W_6ad90.
Proof. vm_refl. Qed.
Lemma D_6ad90 : decode_any W_6ad90 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad94 : bv 32 := 0x00990ab3.
Lemma F_6ad94 : fetch_word Plain.M.loaded_segments (0x6ad94 : word) = Some W_6ad94.
Proof. vm_refl. Qed.
Lemma D_6ad94 : decode_any W_6ad94 = Some (Op ALU_ADD 21 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad98 : bv 32 := 0xfff00593.
Lemma F_6ad98 : fetch_word Plain.M.loaded_segments (0x6ad98 : word) = Some W_6ad98.
Proof. vm_refl. Qed.
Lemma D_6ad98 : decode_any W_6ad98 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ad9c : bv 32 := 0x00a00613.
Lemma F_6ad9c : fetch_word Plain.M.loaded_segments (0x6ad9c : word) = Some W_6ad9c.
Proof. vm_refl. Qed.
Lemma D_6ad9c : decode_any W_6ad9c = Some (OpImm ALU_ADD 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ada0 : bv 32 := 0x00ba86b3.
Lemma F_6ada0 : fetch_word Plain.M.loaded_segments (0x6ada0 : word) = Some W_6ada0.
Proof. vm_refl. Qed.
Lemma D_6ada0 : decode_any W_6ada0 = Some (Op ALU_ADD 13 21 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ada4 : bv 32 := 0x0006c683.
Lemma F_6ada4 : fetch_word Plain.M.loaded_segments (0x6ada4 : word) = Some W_6ada4.
Proof. vm_refl. Qed.
Lemma D_6ada4 : decode_any W_6ada4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ada8 : bv 32 := 0x02c68a63.
Lemma F_6ada8 : fetch_word Plain.M.loaded_segments (0x6ada8 : word) = Some W_6ada8.
Proof. vm_refl. Qed.
Lemma D_6ada8 : decode_any W_6ada8 = Some (Branch BC_EQ 13 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adac : bv 32 := 0x001a0a13.
Lemma F_6adac : fetch_word Plain.M.loaded_segments (0x6adac : word) = Some W_6adac.
Proof. vm_refl. Qed.
Lemma D_6adac : decode_any W_6adac = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adb0 : bv 32 := 0xfff58593.
Lemma F_6adb0 : fetch_word Plain.M.loaded_segments (0x6adb0 : word) = Some W_6adb0.
Proof. vm_refl. Qed.
Lemma D_6adb0 : decode_any W_6adb0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adb4 : bv 32 := 0xff4496e3.
Lemma F_6adb4 : fetch_word Plain.M.loaded_segments (0x6adb4 : word) = Some W_6adb4.
Proof. vm_refl. Qed.
Lemma D_6adb4 : decode_any W_6adb4 = Some (Branch BC_NE 9 20 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adb8 : bv 32 := 0x00000993.
Lemma F_6adb8 : fetch_word Plain.M.loaded_segments (0x6adb8 : word) = Some W_6adb8.
Proof. vm_refl. Qed.
Lemma D_6adb8 : decode_any W_6adb8 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adbc : bv 32 := 0x0480006f.
Lemma F_6adbc : fetch_word Plain.M.loaded_segments (0x6adbc : word) = Some W_6adbc.
Proof. vm_refl. Qed.
Lemma D_6adbc : decode_any W_6adbc = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adc0 : bv 32 := 0x00040513.
Lemma F_6adc0 : fetch_word Plain.M.loaded_segments (0x6adc0 : word) = Some W_6adc0.
Proof. vm_refl. Qed.
Lemma D_6adc0 : decode_any W_6adc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adc4 : bv 32 := 0xd51ff0ef.
Lemma F_6adc4 : fetch_word Plain.M.loaded_segments (0x6adc4 : word) = Some W_6adc4.
Proof. vm_refl. Qed.
Lemma D_6adc4 : decode_any W_6adc4 = Some (Jal 1 2096464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adc8 : bv 32 := 0x00050663.
Lemma F_6adc8 : fetch_word Plain.M.loaded_segments (0x6adc8 : word) = Some W_6adc8.
Proof. vm_refl. Qed.
Lemma D_6adc8 : decode_any W_6adc8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adcc : bv 32 := 0x00000513.
Lemma F_6adcc : fetch_word Plain.M.loaded_segments (0x6adcc : word) = Some W_6adcc.
Proof. vm_refl. Qed.
Lemma D_6adcc : decode_any W_6adcc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6add0 : bv 32 := 0x0500006f.
Lemma F_6add0 : fetch_word Plain.M.loaded_segments (0x6add0 : word) = Some W_6add0.
Proof. vm_refl. Qed.
Lemma D_6add0 : decode_any W_6add0 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6add4 : bv 32 := 0x02043583.
Lemma F_6add4 : fetch_word Plain.M.loaded_segments (0x6add4 : word) = Some W_6add4.
Proof. vm_refl. Qed.
Lemma D_6add4 : decode_any W_6add4 = Some (Load SZ8 true 11 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6add8 : bv 32 := 0xf69ff06f.
Lemma F_6add8 : fetch_word Plain.M.loaded_segments (0x6add8 : word) = Some W_6add8.
Proof. vm_refl. Qed.
Lemma D_6add8 : decode_any W_6add8 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6addc : bv 32 := 0x04843683.
Lemma F_6addc : fetch_word Plain.M.loaded_segments (0x6addc : word) = Some W_6addc.
Proof. vm_refl. Qed.
Lemma D_6addc : decode_any W_6addc = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ade0 : bv 32 := 0x414489b3.
Lemma F_6ade0 : fetch_word Plain.M.loaded_segments (0x6ade0 : word) = Some W_6ade0.
Proof. vm_refl. Qed.
Lemma D_6ade0 : decode_any W_6ade0 = Some (Op ALU_SUB 19 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ade4 : bv 32 := 0x00040513.
Lemma F_6ade4 : fetch_word Plain.M.loaded_segments (0x6ade4 : word) = Some W_6ade4.
Proof. vm_refl. Qed.
Lemma D_6ade4 : decode_any W_6ade4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ade8 : bv 32 := 0x00090593.
Lemma F_6ade8 : fetch_word Plain.M.loaded_segments (0x6ade8 : word) = Some W_6ade8.
Proof. vm_refl. Qed.
Lemma D_6ade8 : decode_any W_6ade8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adec : bv 32 := 0x00098613.
Lemma F_6adec : fetch_word Plain.M.loaded_segments (0x6adec : word) = Some W_6adec.
Proof. vm_refl. Qed.
Lemma D_6adec : decode_any W_6adec = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adf0 : bv 32 := 0x000680e7.
Lemma F_6adf0 : fetch_word Plain.M.loaded_segments (0x6adf0 : word) = Some W_6adf0.
Proof. vm_refl. Qed.
Lemma D_6adf0 : decode_any W_6adf0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adf4 : bv 32 := 0x03356663.
Lemma F_6adf4 : fetch_word Plain.M.loaded_segments (0x6adf4 : word) = Some W_6adf4.
Proof. vm_refl. Qed.
Lemma D_6adf4 : decode_any W_6adf4 = Some (Branch BC_LTU 10 19 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adf8 : bv 32 := 0x02843503.
Lemma F_6adf8 : fetch_word Plain.M.loaded_segments (0x6adf8 : word) = Some W_6adf8.
Proof. vm_refl. Qed.
Lemma D_6adf8 : decode_any W_6adf8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6adfc : bv 32 := 0x414a8933.
Lemma F_6adfc : fetch_word Plain.M.loaded_segments (0x6adfc : word) = Some W_6adfc.
Proof. vm_refl. Qed.
Lemma D_6adfc : decode_any W_6adfc = Some (Op ALU_SUB 18 21 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae00 : bv 32 := 0x000a0493.
Lemma F_6ae00 : fetch_word Plain.M.loaded_segments (0x6ae00 : word) = Some W_6ae00.
Proof. vm_refl. Qed.
Lemma D_6ae00 : decode_any W_6ae00 = Some (OpImm ALU_ADD 9 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae04 : bv 32 := 0x00090593.
Lemma F_6ae04 : fetch_word Plain.M.loaded_segments (0x6ae04 : word) = Some W_6ae04.
Proof. vm_refl. Qed.
Lemma D_6ae04 : decode_any W_6ae04 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae08 : bv 32 := 0x00048613.
Lemma F_6ae08 : fetch_word Plain.M.loaded_segments (0x6ae08 : word) = Some W_6ae08.
Proof. vm_refl. Qed.
Lemma D_6ae08 : decode_any W_6ae08 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae0c : bv 32 := 0x4180a0ef.
Lemma F_6ae0c : fetch_word Plain.M.loaded_segments (0x6ae0c : word) = Some W_6ae0c.
Proof. vm_refl. Qed.
Lemma D_6ae0c : decode_any W_6ae0c = Some (Jal 1 42008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae10 : bv 32 := 0x02843503.
Lemma F_6ae10 : fetch_word Plain.M.loaded_segments (0x6ae10 : word) = Some W_6ae10.
Proof. vm_refl. Qed.
Lemma D_6ae10 : decode_any W_6ae10 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae14 : bv 32 := 0x00950533.
Lemma F_6ae14 : fetch_word Plain.M.loaded_segments (0x6ae14 : word) = Some W_6ae14.
Proof. vm_refl. Qed.
Lemma D_6ae14 : decode_any W_6ae14 = Some (Op ALU_ADD 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae18 : bv 32 := 0x02a43423.
Lemma F_6ae18 : fetch_word Plain.M.loaded_segments (0x6ae18 : word) = Some W_6ae18.
Proof. vm_refl. Qed.
Lemma D_6ae18 : decode_any W_6ae18 = Some (Store SZ8 8 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae1c : bv 32 := 0x00998533.
Lemma F_6ae1c : fetch_word Plain.M.loaded_segments (0x6ae1c : word) = Some W_6ae1c.
Proof. vm_refl. Qed.
Lemma D_6ae1c : decode_any W_6ae1c = Some (Op ALU_ADD 10 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae20 : bv 32 := 0x03813083.
Lemma F_6ae20 : fetch_word Plain.M.loaded_segments (0x6ae20 : word) = Some W_6ae20.
Proof. vm_refl. Qed.
Lemma D_6ae20 : decode_any W_6ae20 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae24 : bv 32 := 0x03013403.
Lemma F_6ae24 : fetch_word Plain.M.loaded_segments (0x6ae24 : word) = Some W_6ae24.
Proof. vm_refl. Qed.
Lemma D_6ae24 : decode_any W_6ae24 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae28 : bv 32 := 0x02813483.
Lemma F_6ae28 : fetch_word Plain.M.loaded_segments (0x6ae28 : word) = Some W_6ae28.
Proof. vm_refl. Qed.
Lemma D_6ae28 : decode_any W_6ae28 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae2c : bv 32 := 0x02013903.
Lemma F_6ae2c : fetch_word Plain.M.loaded_segments (0x6ae2c : word) = Some W_6ae2c.
Proof. vm_refl. Qed.
Lemma D_6ae2c : decode_any W_6ae2c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae30 : bv 32 := 0x01813983.
Lemma F_6ae30 : fetch_word Plain.M.loaded_segments (0x6ae30 : word) = Some W_6ae30.
Proof. vm_refl. Qed.
Lemma D_6ae30 : decode_any W_6ae30 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae34 : bv 32 := 0x01013a03.
Lemma F_6ae34 : fetch_word Plain.M.loaded_segments (0x6ae34 : word) = Some W_6ae34.
Proof. vm_refl. Qed.
Lemma D_6ae34 : decode_any W_6ae34 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae38 : bv 32 := 0x00813a83.
Lemma F_6ae38 : fetch_word Plain.M.loaded_segments (0x6ae38 : word) = Some W_6ae38.
Proof. vm_refl. Qed.
Lemma D_6ae38 : decode_any W_6ae38 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae3c : bv 32 := 0x04010113.
Lemma F_6ae3c : fetch_word Plain.M.loaded_segments (0x6ae3c : word) = Some W_6ae3c.
Proof. vm_refl. Qed.
Lemma D_6ae3c : decode_any W_6ae3c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae40 : bv 32 := 0x00008067.
Lemma F_6ae40 : fetch_word Plain.M.loaded_segments (0x6ae40 : word) = Some W_6ae40.
Proof. vm_refl. Qed.
Lemma D_6ae40 : decode_any W_6ae40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae44 : bv 32 := 0xfc010113.
Lemma F_6ae44 : fetch_word Plain.M.loaded_segments (0x6ae44 : word) = Some W_6ae44.
Proof. vm_refl. Qed.
Lemma D_6ae44 : decode_any W_6ae44 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae48 : bv 32 := 0x02113c23.
Lemma F_6ae48 : fetch_word Plain.M.loaded_segments (0x6ae48 : word) = Some W_6ae48.
Proof. vm_refl. Qed.
Lemma D_6ae48 : decode_any W_6ae48 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae4c : bv 32 := 0x02813823.
Lemma F_6ae4c : fetch_word Plain.M.loaded_segments (0x6ae4c : word) = Some W_6ae4c.
Proof. vm_refl. Qed.
Lemma D_6ae4c : decode_any W_6ae4c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae50 : bv 32 := 0x02913423.
Lemma F_6ae50 : fetch_word Plain.M.loaded_segments (0x6ae50 : word) = Some W_6ae50.
Proof. vm_refl. Qed.
Lemma D_6ae50 : decode_any W_6ae50 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae54 : bv 32 := 0x03213023.
Lemma F_6ae54 : fetch_word Plain.M.loaded_segments (0x6ae54 : word) = Some W_6ae54.
Proof. vm_refl. Qed.
Lemma D_6ae54 : decode_any W_6ae54 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae58 : bv 32 := 0x01313c23.
Lemma F_6ae58 : fetch_word Plain.M.loaded_segments (0x6ae58 : word) = Some W_6ae58.
Proof. vm_refl. Qed.
Lemma D_6ae58 : decode_any W_6ae58 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae5c : bv 32 := 0x01413823.
Lemma F_6ae5c : fetch_word Plain.M.loaded_segments (0x6ae5c : word) = Some W_6ae5c.
Proof. vm_refl. Qed.
Lemma D_6ae5c : decode_any W_6ae5c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae60 : bv 32 := 0x01513423.
Lemma F_6ae60 : fetch_word Plain.M.loaded_segments (0x6ae60 : word) = Some W_6ae60.
Proof. vm_refl. Qed.
Lemma D_6ae60 : decode_any W_6ae60 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae64 : bv 32 := 0x00068993.
Lemma F_6ae64 : fetch_word Plain.M.loaded_segments (0x6ae64 : word) = Some W_6ae64.
Proof. vm_refl. Qed.
Lemma D_6ae64 : decode_any W_6ae64 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae68 : bv 32 := 0x00060413.
Lemma F_6ae68 : fetch_word Plain.M.loaded_segments (0x6ae68 : word) = Some W_6ae68.
Proof. vm_refl. Qed.
Lemma D_6ae68 : decode_any W_6ae68 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae6c : bv 32 := 0x00058493.
Lemma F_6ae6c : fetch_word Plain.M.loaded_segments (0x6ae6c : word) = Some W_6ae6c.
Proof. vm_refl. Qed.
Lemma D_6ae6c : decode_any W_6ae6c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae70 : bv 32 := 0x08c6a583.
Lemma F_6ae70 : fetch_word Plain.M.loaded_segments (0x6ae70 : word) = Some W_6ae70.
Proof. vm_refl. Qed.
Lemma D_6ae70 : decode_any W_6ae70 = Some (Load SZ4 true 11 13 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae74 : bv 32 := 0x02960933.
Lemma F_6ae74 : fetch_word Plain.M.loaded_segments (0x6ae74 : word) = Some W_6ae74.
Proof. vm_refl. Qed.
Lemma D_6ae74 : decode_any W_6ae74 = Some (Mul M_MUL 18 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae78 : bv 32 := 0x0405c463.
Lemma F_6ae78 : fetch_word Plain.M.loaded_segments (0x6ae78 : word) = Some W_6ae78.
Proof. vm_refl. Qed.
Lemma D_6ae78 : decode_any W_6ae78 = Some (Branch BC_LT 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae7c : bv 32 := 0x00050a13.
Lemma F_6ae7c : fetch_word Plain.M.loaded_segments (0x6ae7c : word) = Some W_6ae7c.
Proof. vm_refl. Qed.
Lemma D_6ae7c : decode_any W_6ae7c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae80 : bv 32 := 0x00098513.
Lemma F_6ae80 : fetch_word Plain.M.loaded_segments (0x6ae80 : word) = Some W_6ae80.
Proof. vm_refl. Qed.
Lemma D_6ae80 : decode_any W_6ae80 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae84 : bv 32 := 0x8b1ff0ef.
Lemma F_6ae84 : fetch_word Plain.M.loaded_segments (0x6ae84 : word) = Some W_6ae84.
Proof. vm_refl. Qed.
Lemma D_6ae84 : decode_any W_6ae84 = Some (Jal 1 2095280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae88 : bv 32 := 0x00050a93.
Lemma F_6ae88 : fetch_word Plain.M.loaded_segments (0x6ae88 : word) = Some W_6ae88.
Proof. vm_refl. Qed.
Lemma D_6ae88 : decode_any W_6ae88 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae8c : bv 32 := 0x000a0513.
Lemma F_6ae8c : fetch_word Plain.M.loaded_segments (0x6ae8c : word) = Some W_6ae8c.
Proof. vm_refl. Qed.
Lemma D_6ae8c : decode_any W_6ae8c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae90 : bv 32 := 0x00090593.
Lemma F_6ae90 : fetch_word Plain.M.loaded_segments (0x6ae90 : word) = Some W_6ae90.
Proof. vm_refl. Qed.
Lemma D_6ae90 : decode_any W_6ae90 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae94 : bv 32 := 0x00098613.
Lemma F_6ae94 : fetch_word Plain.M.loaded_segments (0x6ae94 : word) = Some W_6ae94.
Proof. vm_refl. Qed.
Lemma D_6ae94 : decode_any W_6ae94 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae98 : bv 32 := 0xe75ff0ef.
Lemma F_6ae98 : fetch_word Plain.M.loaded_segments (0x6ae98 : word) = Some W_6ae98.
Proof. vm_refl. Qed.
Lemma D_6ae98 : decode_any W_6ae98 = Some (Jal 1 2096756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ae9c : bv 32 := 0x00050a13.
Lemma F_6ae9c : fetch_word Plain.M.loaded_segments (0x6ae9c : word) = Some W_6ae9c.
Proof. vm_refl. Qed.
Lemma D_6ae9c : decode_any W_6ae9c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aea0 : bv 32 := 0x000a8663.
Lemma F_6aea0 : fetch_word Plain.M.loaded_segments (0x6aea0 : word) = Some W_6aea0.
Proof. vm_refl. Qed.
Lemma D_6aea0 : decode_any W_6aea0 = Some (Branch BC_EQ 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aea4 : bv 32 := 0x00098513.
Lemma F_6aea4 : fetch_word Plain.M.loaded_segments (0x6aea4 : word) = Some W_6aea4.
Proof. vm_refl. Qed.
Lemma D_6aea4 : decode_any W_6aea4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aea8 : bv 32 := 0x989ff0ef.
Lemma F_6aea8 : fetch_word Plain.M.loaded_segments (0x6aea8 : word) = Some W_6aea8.
Proof. vm_refl. Qed.
Lemma D_6aea8 : decode_any W_6aea8 = Some (Jal 1 2095496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aeac : bv 32 := 0x032a1463.
Lemma F_6aeac : fetch_word Plain.M.loaded_segments (0x6aeac : word) = Some W_6aeac.
Proof. vm_refl. Qed.
Lemma D_6aeac : decode_any W_6aeac = Some (Branch BC_NE 20 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aeb0 : bv 32 := 0x0014b513.
Lemma F_6aeb0 : fetch_word Plain.M.loaded_segments (0x6aeb0 : word) = Some W_6aeb0.
Proof. vm_refl. Qed.
Lemma D_6aeb0 : decode_any W_6aeb0 = Some (OpImm ALU_SLTU 10 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aeb4 : bv 32 := 0xfff50513.
Lemma F_6aeb4 : fetch_word Plain.M.loaded_segments (0x6aeb4 : word) = Some W_6aeb4.
Proof. vm_refl. Qed.
Lemma D_6aeb4 : decode_any W_6aeb4 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aeb8 : bv 32 := 0x00857533.
Lemma F_6aeb8 : fetch_word Plain.M.loaded_segments (0x6aeb8 : word) = Some W_6aeb8.
Proof. vm_refl. Qed.
Lemma D_6aeb8 : decode_any W_6aeb8 = Some (Op ALU_AND 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aebc : bv 32 := 0x01c0006f.
Lemma F_6aebc : fetch_word Plain.M.loaded_segments (0x6aebc : word) = Some W_6aebc.
Proof. vm_refl. Qed.
Lemma D_6aebc : decode_any W_6aebc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aec0 : bv 32 := 0x00090593.
Lemma F_6aec0 : fetch_word Plain.M.loaded_segments (0x6aec0 : word) = Some W_6aec0.
Proof. vm_refl. Qed.
Lemma D_6aec0 : decode_any W_6aec0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aec4 : bv 32 := 0x00098613.
Lemma F_6aec4 : fetch_word Plain.M.loaded_segments (0x6aec4 : word) = Some W_6aec4.
Proof. vm_refl. Qed.
Lemma D_6aec4 : decode_any W_6aec4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aec8 : bv 32 := 0xe45ff0ef.
Lemma F_6aec8 : fetch_word Plain.M.loaded_segments (0x6aec8 : word) = Some W_6aec8.
Proof. vm_refl. Qed.
Lemma D_6aec8 : decode_any W_6aec8 = Some (Jal 1 2096708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aecc : bv 32 := 0x00050a13.
Lemma F_6aecc : fetch_word Plain.M.loaded_segments (0x6aecc : word) = Some W_6aecc.
Proof. vm_refl. Qed.
Lemma D_6aecc : decode_any W_6aecc = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aed0 : bv 32 := 0xff2500e3.
Lemma F_6aed0 : fetch_word Plain.M.loaded_segments (0x6aed0 : word) = Some W_6aed0.
Proof. vm_refl. Qed.
Lemma D_6aed0 : decode_any W_6aed0 = Some (Branch BC_EQ 10 18 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aed4 : bv 32 := 0x029a5533.
Lemma F_6aed4 : fetch_word Plain.M.loaded_segments (0x6aed4 : word) = Some W_6aed4.
Proof. vm_refl. Qed.
Lemma D_6aed4 : decode_any W_6aed4 = Some (Mul M_DIVU 10 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aed8 : bv 32 := 0x03813083.
Lemma F_6aed8 : fetch_word Plain.M.loaded_segments (0x6aed8 : word) = Some W_6aed8.
Proof. vm_refl. Qed.
Lemma D_6aed8 : decode_any W_6aed8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aedc : bv 32 := 0x03013403.
Lemma F_6aedc : fetch_word Plain.M.loaded_segments (0x6aedc : word) = Some W_6aedc.
Proof. vm_refl. Qed.
Lemma D_6aedc : decode_any W_6aedc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aee0 : bv 32 := 0x02813483.
Lemma F_6aee0 : fetch_word Plain.M.loaded_segments (0x6aee0 : word) = Some W_6aee0.
Proof. vm_refl. Qed.
Lemma D_6aee0 : decode_any W_6aee0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aee4 : bv 32 := 0x02013903.
Lemma F_6aee4 : fetch_word Plain.M.loaded_segments (0x6aee4 : word) = Some W_6aee4.
Proof. vm_refl. Qed.
Lemma D_6aee4 : decode_any W_6aee4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aee8 : bv 32 := 0x01813983.
Lemma F_6aee8 : fetch_word Plain.M.loaded_segments (0x6aee8 : word) = Some W_6aee8.
Proof. vm_refl. Qed.
Lemma D_6aee8 : decode_any W_6aee8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aeec : bv 32 := 0x01013a03.
Lemma F_6aeec : fetch_word Plain.M.loaded_segments (0x6aeec : word) = Some W_6aeec.
Proof. vm_refl. Qed.
Lemma D_6aeec : decode_any W_6aeec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aef0 : bv 32 := 0x00813a83.
Lemma F_6aef0 : fetch_word Plain.M.loaded_segments (0x6aef0 : word) = Some W_6aef0.
Proof. vm_refl. Qed.
Lemma D_6aef0 : decode_any W_6aef0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aef4 : bv 32 := 0x04010113.
Lemma F_6aef4 : fetch_word Plain.M.loaded_segments (0x6aef4 : word) = Some W_6aef4.
Proof. vm_refl. Qed.
Lemma D_6aef4 : decode_any W_6aef4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aef8 : bv 32 := 0x00008067.
Lemma F_6aef8 : fetch_word Plain.M.loaded_segments (0x6aef8 : word) = Some W_6aef8.
Proof. vm_refl. Qed.
Lemma D_6aef8 : decode_any W_6aef8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aefc : bv 32 := 0xff010113.
Lemma F_6aefc : fetch_word Plain.M.loaded_segments (0x6aefc : word) = Some W_6aefc.
Proof. vm_refl. Qed.
Lemma D_6aefc : decode_any W_6aefc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af00 : bv 32 := 0x00113423.
Lemma F_6af00 : fetch_word Plain.M.loaded_segments (0x6af00 : word) = Some W_6af00.
Proof. vm_refl. Qed.
Lemma D_6af00 : decode_any W_6af00 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af04 : bv 32 := 0x00813023.
Lemma F_6af04 : fetch_word Plain.M.loaded_segments (0x6af04 : word) = Some W_6af04.
Proof. vm_refl. Qed.
Lemma D_6af04 : decode_any W_6af04 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af08 : bv 32 := 0x00048517.
Lemma F_6af08 : fetch_word Plain.M.loaded_segments (0x6af08 : word) = Some W_6af08.
Proof. vm_refl. Qed.
Lemma D_6af08 : decode_any W_6af08 = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af0c : bv 32 := 0xe0050413.
Lemma F_6af0c : fetch_word Plain.M.loaded_segments (0x6af0c : word) = Some W_6af0c.
Proof. vm_refl. Qed.
Lemma D_6af0c : decode_any W_6af0c = Some (OpImm ALU_ADD 8 10 3584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af10 : bv 32 := 0x00040513.
Lemma F_6af10 : fetch_word Plain.M.loaded_segments (0x6af10 : word) = Some W_6af10.
Proof. vm_refl. Qed.
Lemma D_6af10 : decode_any W_6af10 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af14 : bv 32 := 0x54d0a0ef.
Lemma F_6af14 : fetch_word Plain.M.loaded_segments (0x6af14 : word) = Some W_6af14.
Proof. vm_refl. Qed.
Lemma D_6af14 : decode_any W_6af14 = Some (Jal 1 44364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af18 : bv 32 := 0x00840513.
Lemma F_6af18 : fetch_word Plain.M.loaded_segments (0x6af18 : word) = Some W_6af18.
Proof. vm_refl. Qed.
Lemma D_6af18 : decode_any W_6af18 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af1c : bv 32 := 0x00813083.
Lemma F_6af1c : fetch_word Plain.M.loaded_segments (0x6af1c : word) = Some W_6af1c.
Proof. vm_refl. Qed.
Lemma D_6af1c : decode_any W_6af1c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af20 : bv 32 := 0x00013403.
Lemma F_6af20 : fetch_word Plain.M.loaded_segments (0x6af20 : word) = Some W_6af20.
Proof. vm_refl. Qed.
Lemma D_6af20 : decode_any W_6af20 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af24 : bv 32 := 0x01010113.
Lemma F_6af24 : fetch_word Plain.M.loaded_segments (0x6af24 : word) = Some W_6af24.
Proof. vm_refl. Qed.
Lemma D_6af24 : decode_any W_6af24 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af28 : bv 32 := 0x00008067.
Lemma F_6af28 : fetch_word Plain.M.loaded_segments (0x6af28 : word) = Some W_6af28.
Proof. vm_refl. Qed.
Lemma D_6af28 : decode_any W_6af28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af2c : bv 32 := 0x00048517.
Lemma F_6af2c : fetch_word Plain.M.loaded_segments (0x6af2c : word) = Some W_6af2c.
Proof. vm_refl. Qed.
Lemma D_6af2c : decode_any W_6af2c = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af30 : bv 32 := 0xddc50513.
Lemma F_6af30 : fetch_word Plain.M.loaded_segments (0x6af30 : word) = Some W_6af30.
Proof. vm_refl. Qed.
Lemma D_6af30 : decode_any W_6af30 = Some (OpImm ALU_ADD 10 10 3548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af34 : bv 32 := 0x7b50a06f.
Lemma F_6af34 : fetch_word Plain.M.loaded_segments (0x6af34 : word) = Some W_6af34.
Proof. vm_refl. Qed.
Lemma D_6af34 : decode_any W_6af34 = Some (Jal 0 44980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af38 : bv 32 := 0xfb010113.
Lemma F_6af38 : fetch_word Plain.M.loaded_segments (0x6af38 : word) = Some W_6af38.
Proof. vm_refl. Qed.
Lemma D_6af38 : decode_any W_6af38 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af3c : bv 32 := 0x00113c23.
Lemma F_6af3c : fetch_word Plain.M.loaded_segments (0x6af3c : word) = Some W_6af3c.
Proof. vm_refl. Qed.
Lemma D_6af3c : decode_any W_6af3c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af40 : bv 32 := 0x00813823.
Lemma F_6af40 : fetch_word Plain.M.loaded_segments (0x6af40 : word) = Some W_6af40.
Proof. vm_refl. Qed.
Lemma D_6af40 : decode_any W_6af40 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af44 : bv 32 := 0x05113423.
Lemma F_6af44 : fetch_word Plain.M.loaded_segments (0x6af44 : word) = Some W_6af44.
Proof. vm_refl. Qed.
Lemma D_6af44 : decode_any W_6af44 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af48 : bv 32 := 0x00015897.
Lemma F_6af48 : fetch_word Plain.M.loaded_segments (0x6af48 : word) = Some W_6af48.
Proof. vm_refl. Qed.
Lemma D_6af48 : decode_any W_6af48 = Some (Auipc 17 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af4c : bv 32 := 0x8c08b403.
Lemma F_6af4c : fetch_word Plain.M.loaded_segments (0x6af4c : word) = Some W_6af4c.
Proof. vm_refl. Qed.
Lemma D_6af4c : decode_any W_6af4c = Some (Load SZ8 true 8 17 2240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af50 : bv 32 := 0x02d13423.
Lemma F_6af50 : fetch_word Plain.M.loaded_segments (0x6af50 : word) = Some W_6af50.
Proof. vm_refl. Qed.
Lemma D_6af50 : decode_any W_6af50 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af54 : bv 32 := 0x02e13823.
Lemma F_6af54 : fetch_word Plain.M.loaded_segments (0x6af54 : word) = Some W_6af54.
Proof. vm_refl. Qed.
Lemma D_6af54 : decode_any W_6af54 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af58 : bv 32 := 0x02f13c23.
Lemma F_6af58 : fetch_word Plain.M.loaded_segments (0x6af58 : word) = Some W_6af58.
Proof. vm_refl. Qed.
Lemma D_6af58 : decode_any W_6af58 = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af5c : bv 32 := 0x05013023.
Lemma F_6af5c : fetch_word Plain.M.loaded_segments (0x6af5c : word) = Some W_6af5c.
Proof. vm_refl. Qed.
Lemma D_6af5c : decode_any W_6af5c = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af60 : bv 32 := 0x00043683.
Lemma F_6af60 : fetch_word Plain.M.loaded_segments (0x6af60 : word) = Some W_6af60.
Proof. vm_refl. Qed.
Lemma D_6af60 : decode_any W_6af60 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af64 : bv 32 := 0x02810713.
Lemma F_6af64 : fetch_word Plain.M.loaded_segments (0x6af64 : word) = Some W_6af64.
Proof. vm_refl. Qed.
Lemma D_6af64 : decode_any W_6af64 = Some (OpImm ALU_ADD 14 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af68 : bv 32 := 0x00d13423.
Lemma F_6af68 : fetch_word Plain.M.loaded_segments (0x6af68 : word) = Some W_6af68.
Proof. vm_refl. Qed.
Lemma D_6af68 : decode_any W_6af68 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af6c : bv 32 := 0x00e13023.
Lemma F_6af6c : fetch_word Plain.M.loaded_segments (0x6af6c : word) = Some W_6af6c.
Proof. vm_refl. Qed.
Lemma D_6af6c : decode_any W_6af6c = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af70 : bv 32 := 0x02810693.
Lemma F_6af70 : fetch_word Plain.M.loaded_segments (0x6af70 : word) = Some W_6af70.
Proof. vm_refl. Qed.
Lemma D_6af70 : decode_any W_6af70 = Some (OpImm ALU_ADD 13 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af74 : bv 32 := 0x525040ef.
Lemma F_6af74 : fetch_word Plain.M.loaded_segments (0x6af74 : word) = Some W_6af74.
Proof. vm_refl. Qed.
Lemma D_6af74 : decode_any W_6af74 = Some (Jal 1 19748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af78 : bv 32 := 0x00043583.
Lemma F_6af78 : fetch_word Plain.M.loaded_segments (0x6af78 : word) = Some W_6af78.
Proof. vm_refl. Qed.
Lemma D_6af78 : decode_any W_6af78 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af7c : bv 32 := 0x00813603.
Lemma F_6af7c : fetch_word Plain.M.loaded_segments (0x6af7c : word) = Some W_6af7c.
Proof. vm_refl. Qed.
Lemma D_6af7c : decode_any W_6af7c = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af80 : bv 32 := 0x00c59a63.
Lemma F_6af80 : fetch_word Plain.M.loaded_segments (0x6af80 : word) = Some W_6af80.
Proof. vm_refl. Qed.
Lemma D_6af80 : decode_any W_6af80 = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af84 : bv 32 := 0x01813083.
Lemma F_6af84 : fetch_word Plain.M.loaded_segments (0x6af84 : word) = Some W_6af84.
Proof. vm_refl. Qed.
Lemma D_6af84 : decode_any W_6af84 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af88 : bv 32 := 0x01013403.
Lemma F_6af88 : fetch_word Plain.M.loaded_segments (0x6af88 : word) = Some W_6af88.
Proof. vm_refl. Qed.
Lemma D_6af88 : decode_any W_6af88 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af8c : bv 32 := 0x05010113.
Lemma F_6af8c : fetch_word Plain.M.loaded_segments (0x6af8c : word) = Some W_6af8c.
Proof. vm_refl. Qed.
Lemma D_6af8c : decode_any W_6af8c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af90 : bv 32 := 0x00008067.
Lemma F_6af90 : fetch_word Plain.M.loaded_segments (0x6af90 : word) = Some W_6af90.
Proof. vm_refl. Qed.
Lemma D_6af90 : decode_any W_6af90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af94 : bv 32 := 0xdd0fc0ef.
Lemma F_6af94 : fetch_word Plain.M.loaded_segments (0x6af94 : word) = Some W_6af94.
Proof. vm_refl. Qed.
Lemma D_6af94 : decode_any W_6af94 = Some (Jal 1 2082256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af98 : bv 32 := 0x00008067.
Lemma F_6af98 : fetch_word Plain.M.loaded_segments (0x6af98 : word) = Some W_6af98.
Proof. vm_refl. Qed.
Lemma D_6af98 : decode_any W_6af98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6af9c : bv 32 := 0xff010113.
Lemma F_6af9c : fetch_word Plain.M.loaded_segments (0x6af9c : word) = Some W_6af9c.
Proof. vm_refl. Qed.
Lemma D_6af9c : decode_any W_6af9c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afa0 : bv 32 := 0x00113423.
Lemma F_6afa0 : fetch_word Plain.M.loaded_segments (0x6afa0 : word) = Some W_6afa0.
Proof. vm_refl. Qed.
Lemma D_6afa0 : decode_any W_6afa0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afa4 : bv 32 := 0x07852503.
Lemma F_6afa4 : fetch_word Plain.M.loaded_segments (0x6afa4 : word) = Some W_6afa4.
Proof. vm_refl. Qed.
Lemma D_6afa4 : decode_any W_6afa4 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afa8 : bv 32 := 0xff1ff0ef.
Lemma F_6afa8 : fetch_word Plain.M.loaded_segments (0x6afa8 : word) = Some W_6afa8.
Proof. vm_refl. Qed.
Lemma D_6afa8 : decode_any W_6afa8 = Some (Jal 1 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afac : bv 32 := 0x03900893.
Lemma F_6afac : fetch_word Plain.M.loaded_segments (0x6afac : word) = Some W_6afac.
Proof. vm_refl. Qed.
Lemma D_6afac : decode_any W_6afac = Some (OpImm ALU_ADD 17 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afb0 : bv 32 := 0x00000073.
Lemma F_6afb0 : fetch_word Plain.M.loaded_segments (0x6afb0 : word) = Some W_6afb0.
Proof. vm_refl. Qed.
Lemma D_6afb0 : decode_any W_6afb0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6afb0 : is_ecall W_6afb0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6afb4 : bv 32 := 0xc1dfc0ef.
Lemma F_6afb4 : fetch_word Plain.M.loaded_segments (0x6afb4 : word) = Some W_6afb4.
Proof. vm_refl. Qed.
Lemma D_6afb4 : decode_any W_6afb4 = Some (Jal 1 2083868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afb8 : bv 32 := 0x0005051b.
Lemma F_6afb8 : fetch_word Plain.M.loaded_segments (0x6afb8 : word) = Some W_6afb8.
Proof. vm_refl. Qed.
Lemma D_6afb8 : decode_any W_6afb8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afbc : bv 32 := 0x00813083.
Lemma F_6afbc : fetch_word Plain.M.loaded_segments (0x6afbc : word) = Some W_6afbc.
Proof. vm_refl. Qed.
Lemma D_6afbc : decode_any W_6afbc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afc0 : bv 32 := 0x01010113.
Lemma F_6afc0 : fetch_word Plain.M.loaded_segments (0x6afc0 : word) = Some W_6afc0.
Proof. vm_refl. Qed.
Lemma D_6afc0 : decode_any W_6afc0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afc4 : bv 32 := 0x00008067.
Lemma F_6afc4 : fetch_word Plain.M.loaded_segments (0x6afc4 : word) = Some W_6afc4.
Proof. vm_refl. Qed.
Lemma D_6afc4 : decode_any W_6afc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
