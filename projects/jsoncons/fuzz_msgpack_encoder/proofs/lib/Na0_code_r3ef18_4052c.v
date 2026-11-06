(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5ae20 : bv 32 := 0xfd010113.
Lemma F_5ae20 : fetch_word Asan.M.loaded_segments (0x5ae70 : word) = Some W_5ae20.
Proof. vm_refl. Qed.
Lemma D_5ae20 : decode_any W_5ae20 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae24 : bv 32 := 0x02113423.
Lemma F_5ae24 : fetch_word Asan.M.loaded_segments (0x5ae74 : word) = Some W_5ae24.
Proof. vm_refl. Qed.
Lemma D_5ae24 : decode_any W_5ae24 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae28 : bv 32 := 0x02813023.
Lemma F_5ae28 : fetch_word Asan.M.loaded_segments (0x5ae78 : word) = Some W_5ae28.
Proof. vm_refl. Qed.
Lemma D_5ae28 : decode_any W_5ae28 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae2c : bv 32 := 0x00913c23.
Lemma F_5ae2c : fetch_word Asan.M.loaded_segments (0x5ae7c : word) = Some W_5ae2c.
Proof. vm_refl. Qed.
Lemma D_5ae2c : decode_any W_5ae2c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae30 : bv 32 := 0x01213823.
Lemma F_5ae30 : fetch_word Asan.M.loaded_segments (0x5ae80 : word) = Some W_5ae30.
Proof. vm_refl. Qed.
Lemma D_5ae30 : decode_any W_5ae30 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae34 : bv 32 := 0x01313423.
Lemma F_5ae34 : fetch_word Asan.M.loaded_segments (0x5ae84 : word) = Some W_5ae34.
Proof. vm_refl. Qed.
Lemma D_5ae34 : decode_any W_5ae34 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae38 : bv 32 := 0x09850713.
Lemma F_5ae38 : fetch_word Asan.M.loaded_segments (0x5ae88 : word) = Some W_5ae38.
Proof. vm_refl. Qed.
Lemma D_5ae38 : decode_any W_5ae38 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae3c : bv 32 := 0x0ff00793.
Lemma F_5ae3c : fetch_word Asan.M.loaded_segments (0x5ae8c : word) = Some W_5ae3c.
Proof. vm_refl. Qed.
Lemma D_5ae3c : decode_any W_5ae3c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae40 : bv 32 := 0xffc77813.
Lemma F_5ae40 : fetch_word Asan.M.loaded_segments (0x5ae90 : word) = Some W_5ae40.
Proof. vm_refl. Qed.
Lemma D_5ae40 : decode_any W_5ae40 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae44 : bv 32 := 0x00100893.
Lemma F_5ae44 : fetch_word Asan.M.loaded_segments (0x5ae94 : word) = Some W_5ae44.
Proof. vm_refl. Qed.
Lemma D_5ae44 : decode_any W_5ae44 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae48 : bv 32 := 0x140822af.
Lemma F_5ae48 : fetch_word Asan.M.loaded_segments (0x5ae98 : word) = Some W_5ae48.
Proof. vm_refl. Qed.
Lemma D_5ae48 : decode_any W_5ae48 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae4c : bv 32 := 0x00088313.
Lemma F_5ae4c : fetch_word Asan.M.loaded_segments (0x5ae9c : word) = Some W_5ae4c.
Proof. vm_refl. Qed.
Lemma D_5ae4c : decode_any W_5ae4c = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae50 : bv 32 := 0x0062c333.
Lemma F_5ae50 : fetch_word Asan.M.loaded_segments (0x5aea0 : word) = Some W_5ae50.
Proof. vm_refl. Qed.
Lemma D_5ae50 : decode_any W_5ae50 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae54 : bv 32 := 0x00f37333.
Lemma F_5ae54 : fetch_word Asan.M.loaded_segments (0x5aea4 : word) = Some W_5ae54.
Proof. vm_refl. Qed.
Lemma D_5ae54 : decode_any W_5ae54 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae58 : bv 32 := 0x0062c333.
Lemma F_5ae58 : fetch_word Asan.M.loaded_segments (0x5aea8 : word) = Some W_5ae58.
Proof. vm_refl. Qed.
Lemma D_5ae58 : decode_any W_5ae58 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae5c : bv 32 := 0x1868232f.
Lemma F_5ae5c : fetch_word Asan.M.loaded_segments (0x5aeac : word) = Some W_5ae5c.
Proof. vm_refl. Qed.
Lemma D_5ae5c : decode_any W_5ae5c = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae60 : bv 32 := 0xfe0314e3.
Lemma F_5ae60 : fetch_word Asan.M.loaded_segments (0x5aeb0 : word) = Some W_5ae60.
Proof. vm_refl. Qed.
Lemma D_5ae60 : decode_any W_5ae60 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae64 : bv 32 := 0x0ff2f793.
Lemma F_5ae64 : fetch_word Asan.M.loaded_segments (0x5aeb4 : word) = Some W_5ae64.
Proof. vm_refl. Qed.
Lemma D_5ae64 : decode_any W_5ae64 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae68 : bv 32 := 0x10079663.
Lemma F_5ae68 : fetch_word Asan.M.loaded_segments (0x5aeb8 : word) = Some W_5ae68.
Proof. vm_refl. Qed.
Lemma D_5ae68 : decode_any W_5ae68 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae6c : bv 32 := 0x0a050713.
Lemma F_5ae6c : fetch_word Asan.M.loaded_segments (0x5aebc : word) = Some W_5ae6c.
Proof. vm_refl. Qed.
Lemma D_5ae6c : decode_any W_5ae6c = Some (OpImm ALU_ADD 14 10 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae70 : bv 32 := 0x12b70a63.
Lemma F_5ae70 : fetch_word Asan.M.loaded_segments (0x5aec0 : word) = Some W_5ae70.
Proof. vm_refl. Qed.
Lemma D_5ae70 : decode_any W_5ae70 = Some (Branch BC_EQ 14 11 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae74 : bv 32 := 0x0005b783.
Lemma F_5ae74 : fetch_word Asan.M.loaded_segments (0x5aec4 : word) = Some W_5ae74.
Proof. vm_refl. Qed.
Lemma D_5ae74 : decode_any W_5ae74 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae78 : bv 32 := 0x04078863.
Lemma F_5ae78 : fetch_word Asan.M.loaded_segments (0x5aec8 : word) = Some W_5ae78.
Proof. vm_refl. Qed.
Lemma D_5ae78 : decode_any W_5ae78 = Some (Branch BC_EQ 15 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae7c : bv 32 := 0x00073803.
Lemma F_5ae7c : fetch_word Asan.M.loaded_segments (0x5aecc : word) = Some W_5ae7c.
Proof. vm_refl. Qed.
Lemma D_5ae7c : decode_any W_5ae7c = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae80 : bv 32 := 0x02080263.
Lemma F_5ae80 : fetch_word Asan.M.loaded_segments (0x5aed0 : word) = Some W_5ae80.
Proof. vm_refl. Qed.
Lemma D_5ae80 : decode_any W_5ae80 = Some (Branch BC_EQ 16 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae84 : bv 32 := 0x0b053703.
Lemma F_5ae84 : fetch_word Asan.M.loaded_segments (0x5aed4 : word) = Some W_5ae84.
Proof. vm_refl. Qed.
Lemma D_5ae84 : decode_any W_5ae84 = Some (Load SZ8 true 14 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae88 : bv 32 := 0x0085b883.
Lemma F_5ae88 : fetch_word Asan.M.loaded_segments (0x5aed8 : word) = Some W_5ae88.
Proof. vm_refl. Qed.
Lemma D_5ae88 : decode_any W_5ae88 = Some (Load SZ8 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae8c : bv 32 := 0x0105b283.
Lemma F_5ae8c : fetch_word Asan.M.loaded_segments (0x5aedc : word) = Some W_5ae8c.
Proof. vm_refl. Qed.
Lemma D_5ae8c : decode_any W_5ae8c = Some (Load SZ8 true 5 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae90 : bv 32 := 0x00f807b3.
Lemma F_5ae90 : fetch_word Asan.M.loaded_segments (0x5aee0 : word) = Some W_5ae90.
Proof. vm_refl. Qed.
Lemma D_5ae90 : decode_any W_5ae90 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae94 : bv 32 := 0x01173023.
Lemma F_5ae94 : fetch_word Asan.M.loaded_segments (0x5aee4 : word) = Some W_5ae94.
Proof. vm_refl. Qed.
Lemma D_5ae94 : decode_any W_5ae94 = Some (Store SZ8 14 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae98 : bv 32 := 0x0af53023.
Lemma F_5ae98 : fetch_word Asan.M.loaded_segments (0x5aee8 : word) = Some W_5ae98.
Proof. vm_refl. Qed.
Lemma D_5ae98 : decode_any W_5ae98 = Some (Store SZ8 10 15 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ae9c : bv 32 := 0x0a553823.
Lemma F_5ae9c : fetch_word Asan.M.loaded_segments (0x5aeec : word) = Some W_5ae9c.
Proof. vm_refl. Qed.
Lemma D_5ae9c : decode_any W_5ae9c = Some (Store SZ8 10 5 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aea0 : bv 32 := 0x01c0006f.
Lemma F_5aea0 : fetch_word Asan.M.loaded_segments (0x5aef0 : word) = Some W_5aea0.
Proof. vm_refl. Qed.
Lemma D_5aea0 : decode_any W_5aea0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aea4 : bv 32 := 0x0105b783.
Lemma F_5aea4 : fetch_word Asan.M.loaded_segments (0x5aef4 : word) = Some W_5aea4.
Proof. vm_refl. Qed.
Lemma D_5aea4 : decode_any W_5aea4 = Some (Load SZ8 true 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aea8 : bv 32 := 0x00f73823.
Lemma F_5aea8 : fetch_word Asan.M.loaded_segments (0x5aef8 : word) = Some W_5aea8.
Proof. vm_refl. Qed.
Lemma D_5aea8 : decode_any W_5aea8 = Some (Store SZ8 14 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aeac : bv 32 := 0x0085b783.
Lemma F_5aeac : fetch_word Asan.M.loaded_segments (0x5aefc : word) = Some W_5aeac.
Proof. vm_refl. Qed.
Lemma D_5aeac : decode_any W_5aeac = Some (Load SZ8 true 15 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aeb0 : bv 32 := 0x00f73423.
Lemma F_5aeb0 : fetch_word Asan.M.loaded_segments (0x5af00 : word) = Some W_5aeb0.
Proof. vm_refl. Qed.
Lemma D_5aeb0 : decode_any W_5aeb0 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aeb4 : bv 32 := 0x0005b783.
Lemma F_5aeb4 : fetch_word Asan.M.loaded_segments (0x5af04 : word) = Some W_5aeb4.
Proof. vm_refl. Qed.
Lemma D_5aeb4 : decode_any W_5aeb4 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aeb8 : bv 32 := 0x00f73023.
Lemma F_5aeb8 : fetch_word Asan.M.loaded_segments (0x5af08 : word) = Some W_5aeb8.
Proof. vm_refl. Qed.
Lemma D_5aeb8 : decode_any W_5aeb8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aebc : bv 32 := 0x0005b023.
Lemma F_5aebc : fetch_word Asan.M.loaded_segments (0x5af0c : word) = Some W_5aebc.
Proof. vm_refl. Qed.
Lemma D_5aebc : decode_any W_5aebc = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aec0 : bv 32 := 0x0005b423.
Lemma F_5aec0 : fetch_word Asan.M.loaded_segments (0x5af10 : word) = Some W_5aec0.
Proof. vm_refl. Qed.
Lemma D_5aec0 : decode_any W_5aec0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aec4 : bv 32 := 0x0005b823.
Lemma F_5aec4 : fetch_word Asan.M.loaded_segments (0x5af14 : word) = Some W_5aec4.
Proof. vm_refl. Qed.
Lemma D_5aec4 : decode_any W_5aec4 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aec8 : bv 32 := 0x0185b703.
Lemma F_5aec8 : fetch_word Asan.M.loaded_segments (0x5af18 : word) = Some W_5aec8.
Proof. vm_refl. Qed.
Lemma D_5aec8 : decode_any W_5aec8 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aecc : bv 32 := 0x0b853783.
Lemma F_5aecc : fetch_word Asan.M.loaded_segments (0x5af1c : word) = Some W_5aecc.
Proof. vm_refl. Qed.
Lemma D_5aecc : decode_any W_5aecc = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aed0 : bv 32 := 0x00e78733.
Lemma F_5aed0 : fetch_word Asan.M.loaded_segments (0x5af20 : word) = Some W_5aed0.
Proof. vm_refl. Qed.
Lemma D_5aed0 : decode_any W_5aed0 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aed4 : bv 32 := 0x0ae53c23.
Lemma F_5aed4 : fetch_word Asan.M.loaded_segments (0x5af24 : word) = Some W_5aed4.
Proof. vm_refl. Qed.
Lemma D_5aed4 : decode_any W_5aed4 = Some (Store SZ8 10 14 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aed8 : bv 32 := 0x0005bc23.
Lemma F_5aed8 : fetch_word Asan.M.loaded_segments (0x5af28 : word) = Some W_5aed8.
Proof. vm_refl. Qed.
Lemma D_5aed8 : decode_any W_5aed8 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aedc : bv 32 := 0x0310000f.
Lemma F_5aedc : fetch_word Asan.M.loaded_segments (0x5af2c : word) = Some W_5aedc.
Proof. vm_refl. Qed.
Lemma D_5aedc : decode_any W_5aedc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aee0 : bv 32 := 0x08050c23.
Lemma F_5aee0 : fetch_word Asan.M.loaded_segments (0x5af30 : word) = Some W_5aee0.
Proof. vm_refl. Qed.
Lemma D_5aee0 : decode_any W_5aee0 = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aee4 : bv 32 := 0x0b853583.
Lemma F_5aee4 : fetch_word Asan.M.loaded_segments (0x5af34 : word) = Some W_5aee4.
Proof. vm_refl. Qed.
Lemma D_5aee4 : decode_any W_5aee4 = Some (Load SZ8 true 11 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aee8 : bv 32 := 0x04053703.
Lemma F_5aee8 : fetch_word Asan.M.loaded_segments (0x5af38 : word) = Some W_5aee8.
Proof. vm_refl. Qed.
Lemma D_5aee8 : decode_any W_5aee8 = Some (Load SZ8 true 14 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aeec : bv 32 := 0x04b77663.
Lemma F_5aeec : fetch_word Asan.M.loaded_segments (0x5af3c : word) = Some W_5aeec.
Proof. vm_refl. Qed.
Lemma D_5aeec : decode_any W_5aeec = Some (Branch BC_GEU 14 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aef0 : bv 32 := 0x09950593.
Lemma F_5aef0 : fetch_word Asan.M.loaded_segments (0x5af40 : word) = Some W_5aef0.
Proof. vm_refl. Qed.
Lemma D_5aef0 : decode_any W_5aef0 = Some (OpImm ALU_ADD 11 10 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aef4 : bv 32 := 0x0ff00713.
Lemma F_5aef4 : fetch_word Asan.M.loaded_segments (0x5af44 : word) = Some W_5aef4.
Proof. vm_refl. Qed.
Lemma D_5aef4 : decode_any W_5aef4 = Some (OpImm ALU_ADD 14 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aef8 : bv 32 := 0x00100793.
Lemma F_5aef8 : fetch_word Asan.M.loaded_segments (0x5af48 : word) = Some W_5aef8.
Proof. vm_refl. Qed.
Lemma D_5aef8 : decode_any W_5aef8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aefc : bv 32 := 0xffc5f813.
Lemma F_5aefc : fetch_word Asan.M.loaded_segments (0x5af4c : word) = Some W_5aefc.
Proof. vm_refl. Qed.
Lemma D_5aefc : decode_any W_5aefc = Some (OpImm ALU_AND 16 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af00 : bv 32 := 0x0035f593.
Lemma F_5af00 : fetch_word Asan.M.loaded_segments (0x5af50 : word) = Some W_5af00.
Proof. vm_refl. Qed.
Lemma D_5af00 : decode_any W_5af00 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af04 : bv 32 := 0x00359593.
Lemma F_5af04 : fetch_word Asan.M.loaded_segments (0x5af54 : word) = Some W_5af04.
Proof. vm_refl. Qed.
Lemma D_5af04 : decode_any W_5af04 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af08 : bv 32 := 0x00b7173b.
Lemma F_5af08 : fetch_word Asan.M.loaded_segments (0x5af58 : word) = Some W_5af08.
Proof. vm_refl. Qed.
Lemma D_5af08 : decode_any W_5af08 = Some (Op32 ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af0c : bv 32 := 0x00b797bb.
Lemma F_5af0c : fetch_word Asan.M.loaded_segments (0x5af5c : word) = Some W_5af0c.
Proof. vm_refl. Qed.
Lemma D_5af0c : decode_any W_5af0c = Some (Op32 ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af10 : bv 32 := 0x140828af.
Lemma F_5af10 : fetch_word Asan.M.loaded_segments (0x5af60 : word) = Some W_5af10.
Proof. vm_refl. Qed.
Lemma D_5af10 : decode_any W_5af10 = Some (Lr AW true false 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af14 : bv 32 := 0x00078293.
Lemma F_5af14 : fetch_word Asan.M.loaded_segments (0x5af64 : word) = Some W_5af14.
Proof. vm_refl. Qed.
Lemma D_5af14 : decode_any W_5af14 = Some (OpImm ALU_ADD 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af18 : bv 32 := 0x0058c2b3.
Lemma F_5af18 : fetch_word Asan.M.loaded_segments (0x5af68 : word) = Some W_5af18.
Proof. vm_refl. Qed.
Lemma D_5af18 : decode_any W_5af18 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af1c : bv 32 := 0x00e2f2b3.
Lemma F_5af1c : fetch_word Asan.M.loaded_segments (0x5af6c : word) = Some W_5af1c.
Proof. vm_refl. Qed.
Lemma D_5af1c : decode_any W_5af1c = Some (Op ALU_AND 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af20 : bv 32 := 0x0058c2b3.
Lemma F_5af20 : fetch_word Asan.M.loaded_segments (0x5af70 : word) = Some W_5af20.
Proof. vm_refl. Qed.
Lemma D_5af20 : decode_any W_5af20 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af24 : bv 32 := 0x185822af.
Lemma F_5af24 : fetch_word Asan.M.loaded_segments (0x5af74 : word) = Some W_5af24.
Proof. vm_refl. Qed.
Lemma D_5af24 : decode_any W_5af24 = Some (Sc AW false false 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af28 : bv 32 := 0xfe0294e3.
Lemma F_5af28 : fetch_word Asan.M.loaded_segments (0x5af78 : word) = Some W_5af28.
Proof. vm_refl. Qed.
Lemma D_5af28 : decode_any W_5af28 = Some (Branch BC_NE 5 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af2c : bv 32 := 0x00b8d5bb.
Lemma F_5af2c : fetch_word Asan.M.loaded_segments (0x5af7c : word) = Some W_5af2c.
Proof. vm_refl. Qed.
Lemma D_5af2c : decode_any W_5af2c = Some (Op32 ALU_SRL 11 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af30 : bv 32 := 0x0ff5f593.
Lemma F_5af30 : fetch_word Asan.M.loaded_segments (0x5af80 : word) = Some W_5af30.
Proof. vm_refl. Qed.
Lemma D_5af30 : decode_any W_5af30 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af34 : bv 32 := 0x02058063.
Lemma F_5af34 : fetch_word Asan.M.loaded_segments (0x5af84 : word) = Some W_5af34.
Proof. vm_refl. Qed.
Lemma D_5af34 : decode_any W_5af34 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af38 : bv 32 := 0x02813083.
Lemma F_5af38 : fetch_word Asan.M.loaded_segments (0x5af88 : word) = Some W_5af38.
Proof. vm_refl. Qed.
Lemma D_5af38 : decode_any W_5af38 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af3c : bv 32 := 0x02013403.
Lemma F_5af3c : fetch_word Asan.M.loaded_segments (0x5af8c : word) = Some W_5af3c.
Proof. vm_refl. Qed.
Lemma D_5af3c : decode_any W_5af3c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af40 : bv 32 := 0x01813483.
Lemma F_5af40 : fetch_word Asan.M.loaded_segments (0x5af90 : word) = Some W_5af40.
Proof. vm_refl. Qed.
Lemma D_5af40 : decode_any W_5af40 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af44 : bv 32 := 0x01013903.
Lemma F_5af44 : fetch_word Asan.M.loaded_segments (0x5af94 : word) = Some W_5af44.
Proof. vm_refl. Qed.
Lemma D_5af44 : decode_any W_5af44 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af48 : bv 32 := 0x00813983.
Lemma F_5af48 : fetch_word Asan.M.loaded_segments (0x5af98 : word) = Some W_5af48.
Proof. vm_refl. Qed.
Lemma D_5af48 : decode_any W_5af48 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af4c : bv 32 := 0x03010113.
Lemma F_5af4c : fetch_word Asan.M.loaded_segments (0x5af9c : word) = Some W_5af4c.
Proof. vm_refl. Qed.
Lemma D_5af4c : decode_any W_5af4c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af50 : bv 32 := 0x00008067.
Lemma F_5af50 : fetch_word Asan.M.loaded_segments (0x5afa0 : word) = Some W_5af50.
Proof. vm_refl. Qed.
Lemma D_5af50 : decode_any W_5af50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af54 : bv 32 := 0x04853583.
Lemma F_5af54 : fetch_word Asan.M.loaded_segments (0x5afa4 : word) = Some W_5af54.
Proof. vm_refl. Qed.
Lemma D_5af54 : decode_any W_5af54 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af58 : bv 32 := 0x02813083.
Lemma F_5af58 : fetch_word Asan.M.loaded_segments (0x5afa8 : word) = Some W_5af58.
Proof. vm_refl. Qed.
Lemma D_5af58 : decode_any W_5af58 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af5c : bv 32 := 0x02013403.
Lemma F_5af5c : fetch_word Asan.M.loaded_segments (0x5afac : word) = Some W_5af5c.
Proof. vm_refl. Qed.
Lemma D_5af5c : decode_any W_5af5c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af60 : bv 32 := 0x01813483.
Lemma F_5af60 : fetch_word Asan.M.loaded_segments (0x5afb0 : word) = Some W_5af60.
Proof. vm_refl. Qed.
Lemma D_5af60 : decode_any W_5af60 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af64 : bv 32 := 0x01013903.
Lemma F_5af64 : fetch_word Asan.M.loaded_segments (0x5afb4 : word) = Some W_5af64.
Proof. vm_refl. Qed.
Lemma D_5af64 : decode_any W_5af64 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af68 : bv 32 := 0x00813983.
Lemma F_5af68 : fetch_word Asan.M.loaded_segments (0x5afb8 : word) = Some W_5af68.
Proof. vm_refl. Qed.
Lemma D_5af68 : decode_any W_5af68 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af6c : bv 32 := 0x03010113.
Lemma F_5af6c : fetch_word Asan.M.loaded_segments (0x5afbc : word) = Some W_5af6c.
Proof. vm_refl. Qed.
Lemma D_5af6c : decode_any W_5af6c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5af70 : bv 32 := 0x0540006f.
Lemma F_5af70 : fetch_word Asan.M.loaded_segments (0x5afc0 : word) = Some W_5af70.
Proof. vm_refl. Qed.
Lemma D_5af70 : decode_any W_5af70 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afc4 : bv 32 := 0xfb010113.
Lemma F_5afc4 : fetch_word Asan.M.loaded_segments (0x5b014 : word) = Some W_5afc4.
Proof. vm_refl. Qed.
Lemma D_5afc4 : decode_any W_5afc4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afc8 : bv 32 := 0x04113423.
Lemma F_5afc8 : fetch_word Asan.M.loaded_segments (0x5b018 : word) = Some W_5afc8.
Proof. vm_refl. Qed.
Lemma D_5afc8 : decode_any W_5afc8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afcc : bv 32 := 0x04813023.
Lemma F_5afcc : fetch_word Asan.M.loaded_segments (0x5b01c : word) = Some W_5afcc.
Proof. vm_refl. Qed.
Lemma D_5afcc : decode_any W_5afcc = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afd0 : bv 32 := 0x02913c23.
Lemma F_5afd0 : fetch_word Asan.M.loaded_segments (0x5b020 : word) = Some W_5afd0.
Proof. vm_refl. Qed.
Lemma D_5afd0 : decode_any W_5afd0 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afd4 : bv 32 := 0x03213823.
Lemma F_5afd4 : fetch_word Asan.M.loaded_segments (0x5b024 : word) = Some W_5afd4.
Proof. vm_refl. Qed.
Lemma D_5afd4 : decode_any W_5afd4 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afd8 : bv 32 := 0x03313423.
Lemma F_5afd8 : fetch_word Asan.M.loaded_segments (0x5b028 : word) = Some W_5afd8.
Proof. vm_refl. Qed.
Lemma D_5afd8 : decode_any W_5afd8 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afdc : bv 32 := 0x03413023.
Lemma F_5afdc : fetch_word Asan.M.loaded_segments (0x5b02c : word) = Some W_5afdc.
Proof. vm_refl. Qed.
Lemma D_5afdc : decode_any W_5afdc = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afe0 : bv 32 := 0x00013023.
Lemma F_5afe0 : fetch_word Asan.M.loaded_segments (0x5b030 : word) = Some W_5afe0.
Proof. vm_refl. Qed.
Lemma D_5afe0 : decode_any W_5afe0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afe4 : bv 32 := 0x00013423.
Lemma F_5afe4 : fetch_word Asan.M.loaded_segments (0x5b034 : word) = Some W_5afe4.
Proof. vm_refl. Qed.
Lemma D_5afe4 : decode_any W_5afe4 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afe8 : bv 32 := 0x00013823.
Lemma F_5afe8 : fetch_word Asan.M.loaded_segments (0x5b038 : word) = Some W_5afe8.
Proof. vm_refl. Qed.
Lemma D_5afe8 : decode_any W_5afe8 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5afec : bv 32 := 0x00013c23.
Lemma F_5afec : fetch_word Asan.M.loaded_segments (0x5b03c : word) = Some W_5afec.
Proof. vm_refl. Qed.
Lemma D_5afec : decode_any W_5afec = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aff0 : bv 32 := 0x09850713.
Lemma F_5aff0 : fetch_word Asan.M.loaded_segments (0x5b040 : word) = Some W_5aff0.
Proof. vm_refl. Qed.
Lemma D_5aff0 : decode_any W_5aff0 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aff4 : bv 32 := 0x0ff00793.
Lemma F_5aff4 : fetch_word Asan.M.loaded_segments (0x5b044 : word) = Some W_5aff4.
Proof. vm_refl. Qed.
Lemma D_5aff4 : decode_any W_5aff4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aff8 : bv 32 := 0xffc77813.
Lemma F_5aff8 : fetch_word Asan.M.loaded_segments (0x5b048 : word) = Some W_5aff8.
Proof. vm_refl. Qed.
Lemma D_5aff8 : decode_any W_5aff8 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5affc : bv 32 := 0x00100893.
Lemma F_5affc : fetch_word Asan.M.loaded_segments (0x5b04c : word) = Some W_5affc.
Proof. vm_refl. Qed.
Lemma D_5affc : decode_any W_5affc = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b000 : bv 32 := 0x140822af.
Lemma F_5b000 : fetch_word Asan.M.loaded_segments (0x5b050 : word) = Some W_5b000.
Proof. vm_refl. Qed.
Lemma D_5b000 : decode_any W_5b000 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b004 : bv 32 := 0x00088313.
Lemma F_5b004 : fetch_word Asan.M.loaded_segments (0x5b054 : word) = Some W_5b004.
Proof. vm_refl. Qed.
Lemma D_5b004 : decode_any W_5b004 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b008 : bv 32 := 0x0062c333.
Lemma F_5b008 : fetch_word Asan.M.loaded_segments (0x5b058 : word) = Some W_5b008.
Proof. vm_refl. Qed.
Lemma D_5b008 : decode_any W_5b008 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b00c : bv 32 := 0x00f37333.
Lemma F_5b00c : fetch_word Asan.M.loaded_segments (0x5b05c : word) = Some W_5b00c.
Proof. vm_refl. Qed.
Lemma D_5b00c : decode_any W_5b00c = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b010 : bv 32 := 0x0062c333.
Lemma F_5b010 : fetch_word Asan.M.loaded_segments (0x5b060 : word) = Some W_5b010.
Proof. vm_refl. Qed.
Lemma D_5b010 : decode_any W_5b010 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b014 : bv 32 := 0x1868232f.
Lemma F_5b014 : fetch_word Asan.M.loaded_segments (0x5b064 : word) = Some W_5b014.
Proof. vm_refl. Qed.
Lemma D_5b014 : decode_any W_5b014 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b018 : bv 32 := 0xfe0314e3.
Lemma F_5b018 : fetch_word Asan.M.loaded_segments (0x5b068 : word) = Some W_5b018.
Proof. vm_refl. Qed.
Lemma D_5b018 : decode_any W_5b018 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b01c : bv 32 := 0x0ff2f793.
Lemma F_5b01c : fetch_word Asan.M.loaded_segments (0x5b06c : word) = Some W_5b01c.
Proof. vm_refl. Qed.
Lemma D_5b01c : decode_any W_5b01c = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b020 : bv 32 := 0x12079a63.
Lemma F_5b020 : fetch_word Asan.M.loaded_segments (0x5b070 : word) = Some W_5b020.
Proof. vm_refl. Qed.
Lemma D_5b020 : decode_any W_5b020 = Some (Branch BC_NE 15 0 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b024 : bv 32 := 0x0b853783.
Lemma F_5b024 : fetch_word Asan.M.loaded_segments (0x5b074 : word) = Some W_5b024.
Proof. vm_refl. Qed.
Lemma D_5b024 : decode_any W_5b024 = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b028 : bv 32 := 0x0a053803.
Lemma F_5b028 : fetch_word Asan.M.loaded_segments (0x5b078 : word) = Some W_5b028.
Proof. vm_refl. Qed.
Lemma D_5b028 : decode_any W_5b028 = Some (Load SZ8 true 16 10 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b02c : bv 32 := 0x00d81713.
Lemma F_5b02c : fetch_word Asan.M.loaded_segments (0x5b07c : word) = Some W_5b02c.
Proof. vm_refl. Qed.
Lemma D_5b02c : decode_any W_5b02c = Some (ShiftImm ALU_SLL 14 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b030 : bv 32 := 0x14e7ee63.
Lemma F_5b030 : fetch_word Asan.M.loaded_segments (0x5b080 : word) = Some W_5b030.
Proof. vm_refl. Qed.
Lemma D_5b030 : decode_any W_5b030 = Some (Branch BC_LTU 15 14 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b034 : bv 32 := 0x04f77663.
Lemma F_5b034 : fetch_word Asan.M.loaded_segments (0x5b084 : word) = Some W_5b034.
Proof. vm_refl. Qed.
Lemma D_5b034 : decode_any W_5b034 = Some (Branch BC_GEU 14 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b038 : bv 32 := 0x00190737.
Lemma F_5b038 : fetch_word Asan.M.loaded_segments (0x5b088 : word) = Some W_5b038.
Proof. vm_refl. Qed.
Lemma D_5b038 : decode_any W_5b038 = Some (Lui 14 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b03c : bv 32 := 0x06400893.
Lemma F_5b03c : fetch_word Asan.M.loaded_segments (0x5b08c : word) = Some W_5b03c.
Proof. vm_refl. Qed.
Lemma D_5b03c : decode_any W_5b03c = Some (OpImm ALU_ADD 17 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b040 : bv 32 := 0x02e80733.
Lemma F_5b040 : fetch_word Asan.M.loaded_segments (0x5b090 : word) = Some W_5b040.
Proof. vm_refl. Qed.
Lemma D_5b040 : decode_any W_5b040 = Some (Mul M_MUL 14 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b044 : bv 32 := 0x031787b3.
Lemma F_5b044 : fetch_word Asan.M.loaded_segments (0x5b094 : word) = Some W_5b044.
Proof. vm_refl. Qed.
Lemma D_5b044 : decode_any W_5b044 = Some (Mul M_MUL 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b048 : bv 32 := 0x02e7fc63.
Lemma F_5b048 : fetch_word Asan.M.loaded_segments (0x5b098 : word) = Some W_5b048.
Proof. vm_refl. Qed.
Lemma D_5b048 : decode_any W_5b048 = Some (Branch BC_GEU 15 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b080 : bv 32 := 0x00013703.
Lemma F_5b080 : fetch_word Asan.M.loaded_segments (0x5b0d0 : word) = Some W_5b080.
Proof. vm_refl. Qed.
Lemma D_5b080 : decode_any W_5b080 = Some (Load SZ8 true 14 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b084 : bv 32 := 0x01013783.
Lemma F_5b084 : fetch_word Asan.M.loaded_segments (0x5b0d4 : word) = Some W_5b084.
Proof. vm_refl. Qed.
Lemma D_5b084 : decode_any W_5b084 = Some (Load SZ8 true 15 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b088 : bv 32 := 0x0b853883.
Lemma F_5b088 : fetch_word Asan.M.loaded_segments (0x5b0d8 : word) = Some W_5b088.
Proof. vm_refl. Qed.
Lemma D_5b088 : decode_any W_5b088 = Some (Load SZ8 true 17 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b08c : bv 32 := 0x0915f863.
Lemma F_5b08c : fetch_word Asan.M.loaded_segments (0x5b0dc : word) = Some W_5b08c.
Proof. vm_refl. Qed.
Lemma D_5b08c : decode_any W_5b08c = Some (Branch BC_GEU 11 17 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b090 : bv 32 := 0x0a853283.
Lemma F_5b090 : fetch_word Asan.M.loaded_segments (0x5b0e0 : word) = Some W_5b090.
Proof. vm_refl. Qed.
Lemma D_5b090 : decode_any W_5b090 = Some (Load SZ8 true 5 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b094 : bv 32 := 0x02c0006f.
Lemma F_5b094 : fetch_word Asan.M.loaded_segments (0x5b0e4 : word) = Some W_5b094.
Proof. vm_refl. Qed.
Lemma D_5b094 : decode_any W_5b094 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b098 : bv 32 := 0x0067b023.
Lemma F_5b098 : fetch_word Asan.M.loaded_segments (0x5b0e8 : word) = Some W_5b098.
Proof. vm_refl. Qed.
Lemma D_5b098 : decode_any W_5b098 = Some (Store SZ8 15 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b09c : bv 32 := 0x00833783.
Lemma F_5b09c : fetch_word Asan.M.loaded_segments (0x5b0ec : word) = Some W_5b09c.
Proof. vm_refl. Qed.
Lemma D_5b09c : decode_any W_5b09c = Some (Load SZ8 true 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0a0 : bv 32 := 0x01813283.
Lemma F_5b0a0 : fetch_word Asan.M.loaded_segments (0x5b0f0 : word) = Some W_5b0a0.
Proof. vm_refl. Qed.
Lemma D_5b0a0 : decode_any W_5b0a0 = Some (Load SZ8 true 5 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0a4 : bv 32 := 0x00f287b3.
Lemma F_5b0a4 : fetch_word Asan.M.loaded_segments (0x5b0f4 : word) = Some W_5b0a4.
Proof. vm_refl. Qed.
Lemma D_5b0a4 : decode_any W_5b0a4 = Some (Op ALU_ADD 15 5 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0a8 : bv 32 := 0x00f13c23.
Lemma F_5b0a8 : fetch_word Asan.M.loaded_segments (0x5b0f8 : word) = Some W_5b0a8.
Proof. vm_refl. Qed.
Lemma D_5b0a8 : decode_any W_5b0a8 = Some (Store SZ8 2 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0ac : bv 32 := 0x0b853383.
Lemma F_5b0ac : fetch_word Asan.M.loaded_segments (0x5b0fc : word) = Some W_5b0ac.
Proof. vm_refl. Qed.
Lemma D_5b0ac : decode_any W_5b0ac = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0b0 : bv 32 := 0x00170713.
Lemma F_5b0b0 : fetch_word Asan.M.loaded_segments (0x5b100 : word) = Some W_5b0b0.
Proof. vm_refl. Qed.
Lemma D_5b0b0 : decode_any W_5b0b0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0b4 : bv 32 := 0x00088293.
Lemma F_5b0b4 : fetch_word Asan.M.loaded_segments (0x5b104 : word) = Some W_5b0b4.
Proof. vm_refl. Qed.
Lemma D_5b0b4 : decode_any W_5b0b4 = Some (OpImm ALU_ADD 5 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0b8 : bv 32 := 0x00030793.
Lemma F_5b0b8 : fetch_word Asan.M.loaded_segments (0x5b108 : word) = Some W_5b0b8.
Proof. vm_refl. Qed.
Lemma D_5b0b8 : decode_any W_5b0b8 = Some (OpImm ALU_ADD 15 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0bc : bv 32 := 0x0475fc63.
Lemma F_5b0bc : fetch_word Asan.M.loaded_segments (0x5b10c : word) = Some W_5b0bc.
Proof. vm_refl. Qed.
Lemma D_5b0bc : decode_any W_5b0bc = Some (Branch BC_GEU 11 7 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0c0 : bv 32 := 0x02080e63.
Lemma F_5b0c0 : fetch_word Asan.M.loaded_segments (0x5b110 : word) = Some W_5b0c0.
Proof. vm_refl. Qed.
Lemma D_5b0c0 : decode_any W_5b0c0 = Some (Branch BC_EQ 16 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0c4 : bv 32 := 0x0002b883.
Lemma F_5b0c4 : fetch_word Asan.M.loaded_segments (0x5b114 : word) = Some W_5b0c4.
Proof. vm_refl. Qed.
Lemma D_5b0c4 : decode_any W_5b0c4 = Some (Load SZ8 true 17 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0c8 : bv 32 := 0x0b153423.
Lemma F_5b0c8 : fetch_word Asan.M.loaded_segments (0x5b118 : word) = Some W_5b0c8.
Proof. vm_refl. Qed.
Lemma D_5b0c8 : decode_any W_5b0c8 = Some (Store SZ8 10 17 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0cc : bv 32 := 0x00089463.
Lemma F_5b0cc : fetch_word Asan.M.loaded_segments (0x5b11c : word) = Some W_5b0cc.
Proof. vm_refl. Qed.
Lemma D_5b0cc : decode_any W_5b0cc = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0d0 : bv 32 := 0x0a053823.
Lemma F_5b0d0 : fetch_word Asan.M.loaded_segments (0x5b120 : word) = Some W_5b0d0.
Proof. vm_refl. Qed.
Lemma D_5b0d0 : decode_any W_5b0d0 = Some (Store SZ8 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0d4 : bv 32 := 0xfff80813.
Lemma F_5b0d4 : fetch_word Asan.M.loaded_segments (0x5b124 : word) = Some W_5b0d4.
Proof. vm_refl. Qed.
Lemma D_5b0d4 : decode_any W_5b0d4 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0d8 : bv 32 := 0x0b053023.
Lemma F_5b0d8 : fetch_word Asan.M.loaded_segments (0x5b128 : word) = Some W_5b0d8.
Proof. vm_refl. Qed.
Lemma D_5b0d8 : decode_any W_5b0d8 = Some (Store SZ8 10 16 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0dc : bv 32 := 0x0082b303.
Lemma F_5b0dc : fetch_word Asan.M.loaded_segments (0x5b12c : word) = Some W_5b0dc.
Proof. vm_refl. Qed.
Lemma D_5b0dc : decode_any W_5b0dc = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0e0 : bv 32 := 0x0b853383.
Lemma F_5b0e0 : fetch_word Asan.M.loaded_segments (0x5b130 : word) = Some W_5b0e0.
Proof. vm_refl. Qed.
Lemma D_5b0e0 : decode_any W_5b0e0 = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0e4 : bv 32 := 0x40638333.
Lemma F_5b0e4 : fetch_word Asan.M.loaded_segments (0x5b134 : word) = Some W_5b0e4.
Proof. vm_refl. Qed.
Lemma D_5b0e4 : decode_any W_5b0e4 = Some (Op ALU_SUB 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0e8 : bv 32 := 0x0a653c23.
Lemma F_5b0e8 : fetch_word Asan.M.loaded_segments (0x5b138 : word) = Some W_5b0e8.
Proof. vm_refl. Qed.
Lemma D_5b0e8 : decode_any W_5b0e8 = Some (Store SZ8 10 6 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0ec : bv 32 := 0x00028313.
Lemma F_5b0ec : fetch_word Asan.M.loaded_segments (0x5b13c : word) = Some W_5b0ec.
Proof. vm_refl. Qed.
Lemma D_5b0ec : decode_any W_5b0ec = Some (OpImm ALU_ADD 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0f0 : bv 32 := 0x0002b023.
Lemma F_5b0f0 : fetch_word Asan.M.loaded_segments (0x5b140 : word) = Some W_5b0f0.
Proof. vm_refl. Qed.
Lemma D_5b0f0 : decode_any W_5b0f0 = Some (Store SZ8 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0f4 : bv 32 := 0xfa0712e3.
Lemma F_5b0f4 : fetch_word Asan.M.loaded_segments (0x5b144 : word) = Some W_5b0f4.
Proof. vm_refl. Qed.
Lemma D_5b0f4 : decode_any W_5b0f4 = Some (Branch BC_NE 14 0 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0f8 : bv 32 := 0x0140006f.
Lemma F_5b0f8 : fetch_word Asan.M.loaded_segments (0x5b148 : word) = Some W_5b0f8.
Proof. vm_refl. Qed.
Lemma D_5b0f8 : decode_any W_5b0f8 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b10c : bv 32 := 0x00613423.
Lemma F_5b10c : fetch_word Asan.M.loaded_segments (0x5b15c : word) = Some W_5b10c.
Proof. vm_refl. Qed.
Lemma D_5b10c : decode_any W_5b10c = Some (Store SZ8 2 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b110 : bv 32 := 0xf8dff06f.
Lemma F_5b110 : fetch_word Asan.M.loaded_segments (0x5b160 : word) = Some W_5b110.
Proof. vm_refl. Qed.
Lemma D_5b110 : decode_any W_5b110 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b114 : bv 32 := 0x00e13023.
Lemma F_5b114 : fetch_word Asan.M.loaded_segments (0x5b164 : word) = Some W_5b114.
Proof. vm_refl. Qed.
Lemma D_5b114 : decode_any W_5b114 = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b118 : bv 32 := 0x00613823.
Lemma F_5b118 : fetch_word Asan.M.loaded_segments (0x5b168 : word) = Some W_5b118.
Proof. vm_refl. Qed.
Lemma D_5b118 : decode_any W_5b118 = Some (Store SZ8 2 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b11c : bv 32 := 0x0310000f.
Lemma F_5b11c : fetch_word Asan.M.loaded_segments (0x5b16c : word) = Some W_5b11c.
Proof. vm_refl. Qed.
Lemma D_5b11c : decode_any W_5b11c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b120 : bv 32 := 0x08050c23.
Lemma F_5b120 : fetch_word Asan.M.loaded_segments (0x5b170 : word) = Some W_5b120.
Proof. vm_refl. Qed.
Lemma D_5b120 : decode_any W_5b120 = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b124 : bv 32 := 0x0310000f.
Lemma F_5b124 : fetch_word Asan.M.loaded_segments (0x5b174 : word) = Some W_5b124.
Proof. vm_refl. Qed.
Lemma D_5b124 : decode_any W_5b124 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b128 : bv 32 := 0x08050ca3.
Lemma F_5b128 : fetch_word Asan.M.loaded_segments (0x5b178 : word) = Some W_5b128.
Proof. vm_refl. Qed.
Lemma D_5b128 : decode_any W_5b128 = Some (Store SZ1 10 0 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b12c : bv 32 := 0x00010593.
Lemma F_5b12c : fetch_word Asan.M.loaded_segments (0x5b17c : word) = Some W_5b12c.
Proof. vm_refl. Qed.
Lemma D_5b12c : decode_any W_5b12c = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b130 : bv 32 := 0x1fc000ef.
Lemma F_5b130 : fetch_word Asan.M.loaded_segments (0x5b180 : word) = Some W_5b130.
Proof. vm_refl. Qed.
Lemma D_5b130 : decode_any W_5b130 = Some (Jal 1 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b134 : bv 32 := 0x04813083.
Lemma F_5b134 : fetch_word Asan.M.loaded_segments (0x5b184 : word) = Some W_5b134.
Proof. vm_refl. Qed.
Lemma D_5b134 : decode_any W_5b134 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b138 : bv 32 := 0x04013403.
Lemma F_5b138 : fetch_word Asan.M.loaded_segments (0x5b188 : word) = Some W_5b138.
Proof. vm_refl. Qed.
Lemma D_5b138 : decode_any W_5b138 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b13c : bv 32 := 0x03813483.
Lemma F_5b13c : fetch_word Asan.M.loaded_segments (0x5b18c : word) = Some W_5b13c.
Proof. vm_refl. Qed.
Lemma D_5b13c : decode_any W_5b13c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b140 : bv 32 := 0x03013903.
Lemma F_5b140 : fetch_word Asan.M.loaded_segments (0x5b190 : word) = Some W_5b140.
Proof. vm_refl. Qed.
Lemma D_5b140 : decode_any W_5b140 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b144 : bv 32 := 0x02813983.
Lemma F_5b144 : fetch_word Asan.M.loaded_segments (0x5b194 : word) = Some W_5b144.
Proof. vm_refl. Qed.
Lemma D_5b144 : decode_any W_5b144 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b148 : bv 32 := 0x02013a03.
Lemma F_5b148 : fetch_word Asan.M.loaded_segments (0x5b198 : word) = Some W_5b148.
Proof. vm_refl. Qed.
Lemma D_5b148 : decode_any W_5b148 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b14c : bv 32 := 0x05010113.
Lemma F_5b14c : fetch_word Asan.M.loaded_segments (0x5b19c : word) = Some W_5b14c.
Proof. vm_refl. Qed.
Lemma D_5b14c : decode_any W_5b14c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b150 : bv 32 := 0x00008067.
Lemma F_5b150 : fetch_word Asan.M.loaded_segments (0x5b1a0 : word) = Some W_5b150.
Proof. vm_refl. Qed.
Lemma D_5b150 : decode_any W_5b150 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b32c : bv 32 := 0xf9010113.
Lemma F_5b32c : fetch_word Asan.M.loaded_segments (0x5b37c : word) = Some W_5b32c.
Proof. vm_refl. Qed.
Lemma D_5b32c : decode_any W_5b32c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b330 : bv 32 := 0x06113423.
Lemma F_5b330 : fetch_word Asan.M.loaded_segments (0x5b380 : word) = Some W_5b330.
Proof. vm_refl. Qed.
Lemma D_5b330 : decode_any W_5b330 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b334 : bv 32 := 0x06813023.
Lemma F_5b334 : fetch_word Asan.M.loaded_segments (0x5b384 : word) = Some W_5b334.
Proof. vm_refl. Qed.
Lemma D_5b334 : decode_any W_5b334 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b338 : bv 32 := 0x04913c23.
Lemma F_5b338 : fetch_word Asan.M.loaded_segments (0x5b388 : word) = Some W_5b338.
Proof. vm_refl. Qed.
Lemma D_5b338 : decode_any W_5b338 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b33c : bv 32 := 0x05213823.
Lemma F_5b33c : fetch_word Asan.M.loaded_segments (0x5b38c : word) = Some W_5b33c.
Proof. vm_refl. Qed.
Lemma D_5b33c : decode_any W_5b33c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b340 : bv 32 := 0x05313423.
Lemma F_5b340 : fetch_word Asan.M.loaded_segments (0x5b390 : word) = Some W_5b340.
Proof. vm_refl. Qed.
Lemma D_5b340 : decode_any W_5b340 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b344 : bv 32 := 0x05413023.
Lemma F_5b344 : fetch_word Asan.M.loaded_segments (0x5b394 : word) = Some W_5b344.
Proof. vm_refl. Qed.
Lemma D_5b344 : decode_any W_5b344 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b348 : bv 32 := 0x03513c23.
Lemma F_5b348 : fetch_word Asan.M.loaded_segments (0x5b398 : word) = Some W_5b348.
Proof. vm_refl. Qed.
Lemma D_5b348 : decode_any W_5b348 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b34c : bv 32 := 0x03613823.
Lemma F_5b34c : fetch_word Asan.M.loaded_segments (0x5b39c : word) = Some W_5b34c.
Proof. vm_refl. Qed.
Lemma D_5b34c : decode_any W_5b34c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b350 : bv 32 := 0x03713423.
Lemma F_5b350 : fetch_word Asan.M.loaded_segments (0x5b3a0 : word) = Some W_5b350.
Proof. vm_refl. Qed.
Lemma D_5b350 : decode_any W_5b350 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b354 : bv 32 := 0x03813023.
Lemma F_5b354 : fetch_word Asan.M.loaded_segments (0x5b3a4 : word) = Some W_5b354.
Proof. vm_refl. Qed.
Lemma D_5b354 : decode_any W_5b354 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b358 : bv 32 := 0x01913c23.
Lemma F_5b358 : fetch_word Asan.M.loaded_segments (0x5b3a8 : word) = Some W_5b358.
Proof. vm_refl. Qed.
Lemma D_5b358 : decode_any W_5b358 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b35c : bv 32 := 0x0005b503.
Lemma F_5b35c : fetch_word Asan.M.loaded_segments (0x5b3ac : word) = Some W_5b35c.
Proof. vm_refl. Qed.
Lemma D_5b35c : decode_any W_5b35c = Some (Load SZ8 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b360 : bv 32 := 0x00c13423.
Lemma F_5b360 : fetch_word Asan.M.loaded_segments (0x5b3b0 : word) = Some W_5b360.
Proof. vm_refl. Qed.
Lemma D_5b360 : decode_any W_5b360 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b364 : bv 32 := 0x00d13823.
Lemma F_5b364 : fetch_word Asan.M.loaded_segments (0x5b3b4 : word) = Some W_5b364.
Proof. vm_refl. Qed.
Lemma D_5b364 : decode_any W_5b364 = Some (Store SZ8 2 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b368 : bv 32 := 0x0c050463.
Lemma F_5b368 : fetch_word Asan.M.loaded_segments (0x5b3b8 : word) = Some W_5b368.
Proof. vm_refl. Qed.
Lemma D_5b368 : decode_any W_5b368 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b36c : bv 32 := 0x00058413.
Lemma F_5b36c : fetch_word Asan.M.loaded_segments (0x5b3bc : word) = Some W_5b36c.
Proof. vm_refl. Qed.
Lemma D_5b36c : decode_any W_5b36c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b370 : bv 32 := 0x00101597.
Lemma F_5b370 : fetch_word Asan.M.loaded_segments (0x5b3c0 : word) = Some W_5b370.
Proof. vm_refl. Qed.
Lemma D_5b370 : decode_any W_5b370 = Some (Auipc 11 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b374 : bv 32 := 0x00100a93.
Lemma F_5b374 : fetch_word Asan.M.loaded_segments (0x5b3c4 : word) = Some W_5b374.
Proof. vm_refl. Qed.
Lemma D_5b374 : decode_any W_5b374 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b378 : bv 32 := 0x05858493.
Lemma F_5b378 : fetch_word Asan.M.loaded_segments (0x5b3c8 : word) = Some W_5b378.
Proof. vm_refl. Qed.
Lemma D_5b378 : decode_any W_5b378 = Some (OpImm ALU_ADD 9 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b37c : bv 32 := 0x025a9a93.
Lemma F_5b37c : fetch_word Asan.M.loaded_segments (0x5b3cc : word) = Some W_5b37c.
Proof. vm_refl. Qed.
Lemma D_5b37c : decode_any W_5b37c = Some (ShiftImm ALU_SLL 21 21 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b380 : bv 32 := 0x04048913.
Lemma F_5b380 : fetch_word Asan.M.loaded_segments (0x5b3d0 : word) = Some W_5b380.
Proof. vm_refl. Qed.
Lemma D_5b380 : decode_any W_5b380 = Some (OpImm ALU_ADD 18 9 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b384 : bv 32 := 0x2b048993.
Lemma F_5b384 : fetch_word Asan.M.loaded_segments (0x5b3d4 : word) = Some W_5b384.
Proof. vm_refl. Qed.
Lemma D_5b384 : decode_any W_5b384 = Some (OpImm ALU_ADD 19 9 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b388 : bv 32 := 0x01c0006f.
Lemma F_5b388 : fetch_word Asan.M.loaded_segments (0x5b3d8 : word) = Some W_5b388.
Proof. vm_refl. Qed.
Lemma D_5b388 : decode_any W_5b388 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3a4 : bv 32 := 0x00843a03.
Lemma F_5b3a4 : fetch_word Asan.M.loaded_segments (0x5b3f4 : word) = Some W_5b3a4.
Proof. vm_refl. Qed.
Lemma D_5b3a4 : decode_any W_5b3a4 = Some (Load SZ8 true 20 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3a8 : bv 32 := 0x000a3583.
Lemma F_5b3a8 : fetch_word Asan.M.loaded_segments (0x5b3f8 : word) = Some W_5b3a8.
Proof. vm_refl. Qed.
Lemma D_5b3a8 : decode_any W_5b3a8 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3ac : bv 32 := 0x00b43423.
Lemma F_5b3ac : fetch_word Asan.M.loaded_segments (0x5b3fc : word) = Some W_5b3ac.
Proof. vm_refl. Qed.
Lemma D_5b3ac : decode_any W_5b3ac = Some (Store SZ8 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3b0 : bv 32 := 0x00059463.
Lemma F_5b3b0 : fetch_word Asan.M.loaded_segments (0x5b400 : word) = Some W_5b3b0.
Proof. vm_refl. Qed.
Lemma D_5b3b0 : decode_any W_5b3b0 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3b4 : bv 32 := 0x00043823.
Lemma F_5b3b4 : fetch_word Asan.M.loaded_segments (0x5b404 : word) = Some W_5b3b4.
Proof. vm_refl. Qed.
Lemma D_5b3b4 : decode_any W_5b3b4 = Some (Store SZ8 8 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3b8 : bv 32 := 0xfff50513.
Lemma F_5b3b8 : fetch_word Asan.M.loaded_segments (0x5b408 : word) = Some W_5b3b8.
Proof. vm_refl. Qed.
Lemma D_5b3b8 : decode_any W_5b3b8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3bc : bv 32 := 0x00a43023.
Lemma F_5b3bc : fetch_word Asan.M.loaded_segments (0x5b40c : word) = Some W_5b3bc.
Proof. vm_refl. Qed.
Lemma D_5b3bc : decode_any W_5b3bc = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3c0 : bv 32 := 0x008a3503.
Lemma F_5b3c0 : fetch_word Asan.M.loaded_segments (0x5b410 : word) = Some W_5b3c0.
Proof. vm_refl. Qed.
Lemma D_5b3c0 : decode_any W_5b3c0 = Some (Load SZ8 true 10 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3c4 : bv 32 := 0x01843583.
Lemma F_5b3c4 : fetch_word Asan.M.loaded_segments (0x5b414 : word) = Some W_5b3c4.
Proof. vm_refl. Qed.
Lemma D_5b3c4 : decode_any W_5b3c4 = Some (Load SZ8 true 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3c8 : bv 32 := 0x40a585b3.
Lemma F_5b3c8 : fetch_word Asan.M.loaded_segments (0x5b418 : word) = Some W_5b3c8.
Proof. vm_refl. Qed.
Lemma D_5b3c8 : decode_any W_5b3c8 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3cc : bv 32 := 0x00b43c23.
Lemma F_5b3cc : fetch_word Asan.M.loaded_segments (0x5b41c : word) = Some W_5b3cc.
Proof. vm_refl. Qed.
Lemma D_5b3cc : decode_any W_5b3cc = Some (Store SZ8 8 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3d0 : bv 32 := 0x010a3b03.
Lemma F_5b3d0 : fetch_word Asan.M.loaded_segments (0x5b420 : word) = Some W_5b3d0.
Proof. vm_refl. Qed.
Lemma D_5b3d0 : decode_any W_5b3d0 = Some (Load SZ8 true 22 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3d4 : bv 32 := 0x020b0463.
Lemma F_5b3d4 : fetch_word Asan.M.loaded_segments (0x5b424 : word) = Some W_5b3d4.
Proof. vm_refl. Qed.
Lemma D_5b3d4 : decode_any W_5b3d4 = Some (Branch BC_EQ 22 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3d8 : bv 32 := 0x098a0b93.
Lemma F_5b3d8 : fetch_word Asan.M.loaded_segments (0x5b428 : word) = Some W_5b3d8.
Proof. vm_refl. Qed.
Lemma D_5b3d8 : decode_any W_5b3d8 = Some (OpImm ALU_ADD 23 20 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3dc : bv 32 := 0x010b0c13.
Lemma F_5b3dc : fetch_word Asan.M.loaded_segments (0x5b42c : word) = Some W_5b3dc.
Proof. vm_refl. Qed.
Lemma D_5b3dc : decode_any W_5b3dc = Some (OpImm ALU_ADD 24 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3e0 : bv 32 := 0x01000c93.
Lemma F_5b3e0 : fetch_word Asan.M.loaded_segments (0x5b430 : word) = Some W_5b3e0.
Proof. vm_refl. Qed.
Lemma D_5b3e0 : decode_any W_5b3e0 = Some (OpImm ALU_ADD 25 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3e4 : bv 32 := 0xf80bb583.
Lemma F_5b3e4 : fetch_word Asan.M.loaded_segments (0x5b434 : word) = Some W_5b3e4.
Proof. vm_refl. Qed.
Lemma D_5b3e4 : decode_any W_5b3e4 = Some (Load SZ8 true 11 23 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3e8 : bv 32 := 0x00810513.
Lemma F_5b3e8 : fetch_word Asan.M.loaded_segments (0x5b438 : word) = Some W_5b3e8.
Proof. vm_refl. Qed.
Lemma D_5b3e8 : decode_any W_5b3e8 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3ec : bv 32 := 0x078000ef.
Lemma F_5b3ec : fetch_word Asan.M.loaded_segments (0x5b43c : word) = Some W_5b3ec.
Proof. vm_refl. Qed.
Lemma D_5b3ec : decode_any W_5b3ec = Some (Jal 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3f0 : bv 32 := 0x001c8c93.
Lemma F_5b3f0 : fetch_word Asan.M.loaded_segments (0x5b440 : word) = Some W_5b3f0.
Proof. vm_refl. Qed.
Lemma D_5b3f0 : decode_any W_5b3f0 = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3f4 : bv 32 := 0x008b8b93.
Lemma F_5b3f4 : fetch_word Asan.M.loaded_segments (0x5b444 : word) = Some W_5b3f4.
Proof. vm_refl. Qed.
Lemma D_5b3f4 : decode_any W_5b3f4 = Some (OpImm ALU_ADD 23 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3f8 : bv 32 := 0xff8c96e3.
Lemma F_5b3f8 : fetch_word Asan.M.loaded_segments (0x5b448 : word) = Some W_5b3f8.
Proof. vm_refl. Qed.
Lemma D_5b3f8 : decode_any W_5b3f8 = Some (Branch BC_NE 25 24 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3fc : bv 32 := 0x0204b583.
Lemma F_5b3fc : fetch_word Asan.M.loaded_segments (0x5b44c : word) = Some W_5b3fc.
Proof. vm_refl. Qed.
Lemma D_5b3fc : decode_any W_5b3fc = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b400 : bv 32 := 0xf8ba66e3.
Lemma F_5b400 : fetch_word Asan.M.loaded_segments (0x5b450 : word) = Some W_5b400.
Proof. vm_refl. Qed.
Lemma D_5b400 : decode_any W_5b400 = Some (Branch BC_LTU 20 11 8076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b404 : bv 32 := 0x01558533.
Lemma F_5b404 : fetch_word Asan.M.loaded_segments (0x5b454 : word) = Some W_5b404.
Proof. vm_refl. Qed.
Lemma D_5b404 : decode_any W_5b404 = Some (Op ALU_ADD 10 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b408 : bv 32 := 0xf8aa72e3.
Lemma F_5b408 : fetch_word Asan.M.loaded_segments (0x5b458 : word) = Some W_5b408.
Proof. vm_refl. Qed.
Lemma D_5b408 : decode_any W_5b408 = Some (Branch BC_GEU 20 10 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b40c : bv 32 := 0x00813503.
Lemma F_5b40c : fetch_word Asan.M.loaded_segments (0x5b45c : word) = Some W_5b40c.
Proof. vm_refl. Qed.
Lemma D_5b40c : decode_any W_5b40c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b410 : bv 32 := 0x40ba05b3.
Lemma F_5b410 : fetch_word Asan.M.loaded_segments (0x5b460 : word) = Some W_5b410.
Proof. vm_refl. Qed.
Lemma D_5b410 : decode_any W_5b410 = Some (Op ALU_SUB 11 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b414 : bv 32 := 0x01b59593.
Lemma F_5b414 : fetch_word Asan.M.loaded_segments (0x5b464 : word) = Some W_5b414.
Proof. vm_refl. Qed.
Lemma D_5b414 : decode_any W_5b414 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b418 : bv 32 := 0x03b5d613.
Lemma F_5b418 : fetch_word Asan.M.loaded_segments (0x5b468 : word) = Some W_5b418.
Proof. vm_refl. Qed.
Lemma D_5b418 : decode_any W_5b418 = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b41c : bv 32 := 0x00048593.
Lemma F_5b41c : fetch_word Asan.M.loaded_segments (0x5b46c : word) = Some W_5b41c.
Proof. vm_refl. Qed.
Lemma D_5b41c : decode_any W_5b41c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b420 : bv 32 := 0x000a0693.
Lemma F_5b420 : fetch_word Asan.M.loaded_segments (0x5b470 : word) = Some W_5b420.
Proof. vm_refl. Qed.
Lemma D_5b420 : decode_any W_5b420 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b424 : bv 32 := 0x444000ef.
Lemma F_5b424 : fetch_word Asan.M.loaded_segments (0x5b474 : word) = Some W_5b424.
Proof. vm_refl. Qed.
Lemma D_5b424 : decode_any W_5b424 = Some (Jal 1 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b428 : bv 32 := 0x00043503.
Lemma F_5b428 : fetch_word Asan.M.loaded_segments (0x5b478 : word) = Some W_5b428.
Proof. vm_refl. Qed.
Lemma D_5b428 : decode_any W_5b428 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b42c : bv 32 := 0xf6051ce3.
Lemma F_5b42c : fetch_word Asan.M.loaded_segments (0x5b47c : word) = Some W_5b42c.
Proof. vm_refl. Qed.
Lemma D_5b42c : decode_any W_5b42c = Some (Branch BC_NE 10 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b430 : bv 32 := 0x06813083.
Lemma F_5b430 : fetch_word Asan.M.loaded_segments (0x5b480 : word) = Some W_5b430.
Proof. vm_refl. Qed.
Lemma D_5b430 : decode_any W_5b430 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b434 : bv 32 := 0x06013403.
Lemma F_5b434 : fetch_word Asan.M.loaded_segments (0x5b484 : word) = Some W_5b434.
Proof. vm_refl. Qed.
Lemma D_5b434 : decode_any W_5b434 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b438 : bv 32 := 0x05813483.
Lemma F_5b438 : fetch_word Asan.M.loaded_segments (0x5b488 : word) = Some W_5b438.
Proof. vm_refl. Qed.
Lemma D_5b438 : decode_any W_5b438 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b43c : bv 32 := 0x05013903.
Lemma F_5b43c : fetch_word Asan.M.loaded_segments (0x5b48c : word) = Some W_5b43c.
Proof. vm_refl. Qed.
Lemma D_5b43c : decode_any W_5b43c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b440 : bv 32 := 0x04813983.
Lemma F_5b440 : fetch_word Asan.M.loaded_segments (0x5b490 : word) = Some W_5b440.
Proof. vm_refl. Qed.
Lemma D_5b440 : decode_any W_5b440 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b444 : bv 32 := 0x04013a03.
Lemma F_5b444 : fetch_word Asan.M.loaded_segments (0x5b494 : word) = Some W_5b444.
Proof. vm_refl. Qed.
Lemma D_5b444 : decode_any W_5b444 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b448 : bv 32 := 0x03813a83.
Lemma F_5b448 : fetch_word Asan.M.loaded_segments (0x5b498 : word) = Some W_5b448.
Proof. vm_refl. Qed.
Lemma D_5b448 : decode_any W_5b448 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b44c : bv 32 := 0x03013b03.
Lemma F_5b44c : fetch_word Asan.M.loaded_segments (0x5b49c : word) = Some W_5b44c.
Proof. vm_refl. Qed.
Lemma D_5b44c : decode_any W_5b44c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b450 : bv 32 := 0x02813b83.
Lemma F_5b450 : fetch_word Asan.M.loaded_segments (0x5b4a0 : word) = Some W_5b450.
Proof. vm_refl. Qed.
Lemma D_5b450 : decode_any W_5b450 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b454 : bv 32 := 0x02013c03.
Lemma F_5b454 : fetch_word Asan.M.loaded_segments (0x5b4a4 : word) = Some W_5b454.
Proof. vm_refl. Qed.
Lemma D_5b454 : decode_any W_5b454 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b458 : bv 32 := 0x01813c83.
Lemma F_5b458 : fetch_word Asan.M.loaded_segments (0x5b4a8 : word) = Some W_5b458.
Proof. vm_refl. Qed.
Lemma D_5b458 : decode_any W_5b458 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b45c : bv 32 := 0x07010113.
Lemma F_5b45c : fetch_word Asan.M.loaded_segments (0x5b4ac : word) = Some W_5b45c.
Proof. vm_refl. Qed.
Lemma D_5b45c : decode_any W_5b45c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b460 : bv 32 := 0x00008067.
Lemma F_5b460 : fetch_word Asan.M.loaded_segments (0x5b4b0 : word) = Some W_5b460.
Proof. vm_refl. Qed.
Lemma D_5b460 : decode_any W_5b460 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b464 : bv 32 := 0xfd010113.
Lemma F_5b464 : fetch_word Asan.M.loaded_segments (0x5b4b4 : word) = Some W_5b464.
Proof. vm_refl. Qed.
Lemma D_5b464 : decode_any W_5b464 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b468 : bv 32 := 0x02113423.
Lemma F_5b468 : fetch_word Asan.M.loaded_segments (0x5b4b8 : word) = Some W_5b468.
Proof. vm_refl. Qed.
Lemma D_5b468 : decode_any W_5b468 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b46c : bv 32 := 0x02813023.
Lemma F_5b46c : fetch_word Asan.M.loaded_segments (0x5b4bc : word) = Some W_5b46c.
Proof. vm_refl. Qed.
Lemma D_5b46c : decode_any W_5b46c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b470 : bv 32 := 0x00913c23.
Lemma F_5b470 : fetch_word Asan.M.loaded_segments (0x5b4c0 : word) = Some W_5b470.
Proof. vm_refl. Qed.
Lemma D_5b470 : decode_any W_5b470 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b474 : bv 32 := 0x01213823.
Lemma F_5b474 : fetch_word Asan.M.loaded_segments (0x5b4c4 : word) = Some W_5b474.
Proof. vm_refl. Qed.
Lemma D_5b474 : decode_any W_5b474 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b478 : bv 32 := 0x01313423.
Lemma F_5b478 : fetch_word Asan.M.loaded_segments (0x5b4c8 : word) = Some W_5b478.
Proof. vm_refl. Qed.
Lemma D_5b478 : decode_any W_5b478 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b47c : bv 32 := 0x01413023.
Lemma F_5b47c : fetch_word Asan.M.loaded_segments (0x5b4cc : word) = Some W_5b47c.
Proof. vm_refl. Qed.
Lemma D_5b47c : decode_any W_5b47c = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b480 : bv 32 := 0x00058493.
Lemma F_5b480 : fetch_word Asan.M.loaded_segments (0x5b4d0 : word) = Some W_5b480.
Proof. vm_refl. Qed.
Lemma D_5b480 : decode_any W_5b480 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b484 : bv 32 := 0x00050413.
Lemma F_5b484 : fetch_word Asan.M.loaded_segments (0x5b4d4 : word) = Some W_5b484.
Proof. vm_refl. Qed.
Lemma D_5b484 : decode_any W_5b484 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b488 : bv 32 := 0x00101517.
Lemma F_5b488 : fetch_word Asan.M.loaded_segments (0x5b4d8 : word) = Some W_5b488.
Proof. vm_refl. Qed.
Lemma D_5b488 : decode_any W_5b488 = Some (Auipc 10 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b48c : bv 32 := 0xf4050993.
Lemma F_5b48c : fetch_word Asan.M.loaded_segments (0x5b4dc : word) = Some W_5b48c.
Proof. vm_refl. Qed.
Lemma D_5b48c : decode_any W_5b48c = Some (OpImm ALU_ADD 19 10 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b490 : bv 32 := 0x0209b503.
Lemma F_5b490 : fetch_word Asan.M.loaded_segments (0x5b4e0 : word) = Some W_5b490.
Proof. vm_refl. Qed.
Lemma D_5b490 : decode_any W_5b490 = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b494 : bv 32 := 0x00100a13.
Lemma F_5b494 : fetch_word Asan.M.loaded_segments (0x5b4e4 : word) = Some W_5b494.
Proof. vm_refl. Qed.
Lemma D_5b494 : decode_any W_5b494 = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b498 : bv 32 := 0x025a1a13.
Lemma F_5b498 : fetch_word Asan.M.loaded_segments (0x5b4e8 : word) = Some W_5b498.
Proof. vm_refl. Qed.
Lemma D_5b498 : decode_any W_5b498 = Some (ShiftImm ALU_SLL 20 20 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b49c : bv 32 := 0x02a5ea63.
Lemma F_5b49c : fetch_word Asan.M.loaded_segments (0x5b4ec : word) = Some W_5b49c.
Proof. vm_refl. Qed.
Lemma D_5b49c : decode_any W_5b49c = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4a0 : bv 32 := 0x014505b3.
Lemma F_5b4a0 : fetch_word Asan.M.loaded_segments (0x5b4f0 : word) = Some W_5b4a0.
Proof. vm_refl. Qed.
Lemma D_5b4a0 : decode_any W_5b4a0 = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4a4 : bv 32 := 0x02b4f663.
Lemma F_5b4a4 : fetch_word Asan.M.loaded_segments (0x5b4f4 : word) = Some W_5b4a4.
Proof. vm_refl. Qed.
Lemma D_5b4a4 : decode_any W_5b4a4 = Some (Branch BC_GEU 9 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4a8 : bv 32 := 0x40a48733.
Lemma F_5b4a8 : fetch_word Asan.M.loaded_segments (0x5b4f8 : word) = Some W_5b4a8.
Proof. vm_refl. Qed.
Lemma D_5b4a8 : decode_any W_5b4a8 = Some (Op ALU_SUB 14 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4ac : bv 32 := 0x02075693.
Lemma F_5b4ac : fetch_word Asan.M.loaded_segments (0x5b4fc : word) = Some W_5b4ac.
Proof. vm_refl. Qed.
Lemma D_5b4ac : decode_any W_5b4ac = Some (ShiftImm ALU_SRL 13 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4b0 : bv 32 := 0x01f6f613.
Lemma F_5b4b0 : fetch_word Asan.M.loaded_segments (0x5b500 : word) = Some W_5b4b0.
Proof. vm_refl. Qed.
Lemma D_5b4b0 : decode_any W_5b4b0 = Some (OpImm ALU_AND 12 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4b4 : bv 32 := 0x01f00793.
Lemma F_5b4b4 : fetch_word Asan.M.loaded_segments (0x5b504 : word) = Some W_5b4b4.
Proof. vm_refl. Qed.
Lemma D_5b4b4 : decode_any W_5b4b4 = Some (OpImm ALU_ADD 15 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4b8 : bv 32 := 0x1ef60663.
Lemma F_5b4b8 : fetch_word Asan.M.loaded_segments (0x5b508 : word) = Some W_5b4b8.
Proof. vm_refl. Qed.
Lemma D_5b4b8 : decode_any W_5b4b8 = Some (Branch BC_EQ 12 15 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4bc : bv 32 := 0x01100793.
Lemma F_5b4bc : fetch_word Asan.M.loaded_segments (0x5b50c : word) = Some W_5b4bc.
Proof. vm_refl. Qed.
Lemma D_5b4bc : decode_any W_5b4bc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4c0 : bv 32 := 0x02f67863.
Lemma F_5b4c0 : fetch_word Asan.M.loaded_segments (0x5b510 : word) = Some W_5b4c0.
Proof. vm_refl. Qed.
Lemma D_5b4c0 : decode_any W_5b4c0 = Some (Branch BC_GEU 12 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4c4 : bv 32 := 0x1c060a63.
Lemma F_5b4c4 : fetch_word Asan.M.loaded_segments (0x5b514 : word) = Some W_5b4c4.
Proof. vm_refl. Qed.
Lemma D_5b4c4 : decode_any W_5b4c4 = Some (Branch BC_EQ 12 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4c8 : bv 32 := 0x00561793.
Lemma F_5b4c8 : fetch_word Asan.M.loaded_segments (0x5b518 : word) = Some W_5b4c8.
Proof. vm_refl. Qed.
Lemma D_5b4c8 : decode_any W_5b4c8 = Some (ShiftImm ALU_SLL 15 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4cc : bv 32 := 0x0480006f.
Lemma F_5b4cc : fetch_word Asan.M.loaded_segments (0x5b51c : word) = Some W_5b4cc.
Proof. vm_refl. Qed.
Lemma D_5b4cc : decode_any W_5b4cc = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4d0 : bv 32 := 0x04098513.
Lemma F_5b4d0 : fetch_word Asan.M.loaded_segments (0x5b520 : word) = Some W_5b4d0.
Proof. vm_refl. Qed.
Lemma D_5b4d0 : decode_any W_5b4d0 = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4d4 : bv 32 := 0x00048593.
Lemma F_5b4d4 : fetch_word Asan.M.loaded_segments (0x5b524 : word) = Some W_5b4d4.
Proof. vm_refl. Qed.
Lemma D_5b4d4 : decode_any W_5b4d4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4d8 : bv 32 := 0x210000ef.
Lemma F_5b4d8 : fetch_word Asan.M.loaded_segments (0x5b528 : word) = Some W_5b4d8.
Proof. vm_refl. Qed.
Lemma D_5b4d8 : decode_any W_5b4d8 = Some (Jal 1 528, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4dc : bv 32 := 0x00050913.
Lemma F_5b4dc : fetch_word Asan.M.loaded_segments (0x5b52c : word) = Some W_5b4dc.
Proof. vm_refl. Qed.
Lemma D_5b4dc : decode_any W_5b4dc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4e0 : bv 32 := 0x0209b503.
Lemma F_5b4e0 : fetch_word Asan.M.loaded_segments (0x5b530 : word) = Some W_5b4e0.
Proof. vm_refl. Qed.
Lemma D_5b4e0 : decode_any W_5b4e0 = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4e4 : bv 32 := 0x014505b3.
Lemma F_5b4e4 : fetch_word Asan.M.loaded_segments (0x5b534 : word) = Some W_5b4e4.
Proof. vm_refl. Qed.
Lemma D_5b4e4 : decode_any W_5b4e4 = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4e8 : bv 32 := 0x06a97663.
Lemma F_5b4e8 : fetch_word Asan.M.loaded_segments (0x5b538 : word) = Some W_5b4e8.
Proof. vm_refl. Qed.
Lemma D_5b4e8 : decode_any W_5b4e8 = Some (Branch BC_GEU 18 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4ec : bv 32 := 0x0e40006f.
Lemma F_5b4ec : fetch_word Asan.M.loaded_segments (0x5b53c : word) = Some W_5b4ec.
Proof. vm_refl. Qed.
Lemma D_5b4ec : decode_any W_5b4ec = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4f0 : bv 32 := 0xff060793.
Lemma F_5b4f0 : fetch_word Asan.M.loaded_segments (0x5b540 : word) = Some W_5b4f0.
Proof. vm_refl. Qed.
Lemma D_5b4f0 : decode_any W_5b4f0 = Some (OpImm ALU_ADD 15 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4f4 : bv 32 := 0x20000813.
Lemma F_5b4f4 : fetch_word Asan.M.loaded_segments (0x5b544 : word) = Some W_5b4f4.
Proof. vm_refl. Qed.
Lemma D_5b4f4 : decode_any W_5b4f4 = Some (OpImm ALU_ADD 16 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4f8 : bv 32 := 0x03f69893.
Lemma F_5b4f8 : fetch_word Asan.M.loaded_segments (0x5b548 : word) = Some W_5b4f8.
Proof. vm_refl. Qed.
Lemma D_5b4f8 : decode_any W_5b4f8 = Some (ShiftImm ALU_SLL 17 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b4fc : bv 32 := 0x0017d793.
Lemma F_5b4fc : fetch_word Asan.M.loaded_segments (0x5b54c : word) = Some W_5b4fc.
Proof. vm_refl. Qed.
Lemma D_5b4fc : decode_any W_5b4fc = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b500 : bv 32 := 0x00f817b3.
Lemma F_5b500 : fetch_word Asan.M.loaded_segments (0x5b550 : word) = Some W_5b500.
Proof. vm_refl. Qed.
Lemma D_5b500 : decode_any W_5b500 = Some (Op ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b504 : bv 32 := 0x0017d813.
Lemma F_5b504 : fetch_word Asan.M.loaded_segments (0x5b554 : word) = Some W_5b504.
Proof. vm_refl. Qed.
Lemma D_5b504 : decode_any W_5b504 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b508 : bv 32 := 0x43f8d893.
Lemma F_5b508 : fetch_word Asan.M.loaded_segments (0x5b558 : word) = Some W_5b508.
Proof. vm_refl. Qed.
Lemma D_5b508 : decode_any W_5b508 = Some (ShiftImm ALU_SRA 17 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b50c : bv 32 := 0x0108f833.
Lemma F_5b50c : fetch_word Asan.M.loaded_segments (0x5b55c : word) = Some W_5b50c.
Proof. vm_refl. Qed.
Lemma D_5b50c : decode_any W_5b50c = Some (Op ALU_AND 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b510 : bv 32 := 0x00f807b3.
Lemma F_5b510 : fetch_word Asan.M.loaded_segments (0x5b560 : word) = Some W_5b510.
Proof. vm_refl. Qed.
Lemma D_5b510 : decode_any W_5b510 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b514 : bv 32 := 0x02f7573b.
Lemma F_5b514 : fetch_word Asan.M.loaded_segments (0x5b564 : word) = Some W_5b514.
Proof. vm_refl. Qed.
Lemma D_5b514 : decode_any W_5b514 = Some (Mul32 M_DIVU 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b518 : bv 32 := 0x02069693.
Lemma F_5b518 : fetch_word Asan.M.loaded_segments (0x5b568 : word) = Some W_5b518.
Proof. vm_refl. Qed.
Lemma D_5b518 : decode_any W_5b518 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b51c : bv 32 := 0x0309b803.
Lemma F_5b51c : fetch_word Asan.M.loaded_segments (0x5b56c : word) = Some W_5b51c.
Proof. vm_refl. Qed.
Lemma D_5b51c : decode_any W_5b51c = Some (Load SZ8 true 16 19 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b520 : bv 32 := 0x00761613.
Lemma F_5b520 : fetch_word Asan.M.loaded_segments (0x5b570 : word) = Some W_5b520.
Proof. vm_refl. Qed.
Lemma D_5b520 : decode_any W_5b520 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b524 : bv 32 := 0x02071713.
Lemma F_5b524 : fetch_word Asan.M.loaded_segments (0x5b574 : word) = Some W_5b524.
Proof. vm_refl. Qed.
Lemma D_5b524 : decode_any W_5b524 = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b528 : bv 32 := 0x00a686b3.
Lemma F_5b528 : fetch_word Asan.M.loaded_segments (0x5b578 : word) = Some W_5b528.
Proof. vm_refl. Qed.
Lemma D_5b528 : decode_any W_5b528 = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b52c : bv 32 := 0x00c80633.
Lemma F_5b52c : fetch_word Asan.M.loaded_segments (0x5b57c : word) = Some W_5b52c.
Proof. vm_refl. Qed.
Lemma D_5b52c : decode_any W_5b52c = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b530 : bv 32 := 0x03063603.
Lemma F_5b530 : fetch_word Asan.M.loaded_segments (0x5b580 : word) = Some W_5b530.
Proof. vm_refl. Qed.
Lemma D_5b530 : decode_any W_5b530 = Some (Load SZ8 true 12 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b534 : bv 32 := 0x02075713.
Lemma F_5b534 : fetch_word Asan.M.loaded_segments (0x5b584 : word) = Some W_5b534.
Proof. vm_refl. Qed.
Lemma D_5b534 : decode_any W_5b534 = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b538 : bv 32 := 0x02e78733.
Lemma F_5b538 : fetch_word Asan.M.loaded_segments (0x5b588 : word) = Some W_5b538.
Proof. vm_refl. Qed.
Lemma D_5b538 : decode_any W_5b538 = Some (Mul M_MUL 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b53c : bv 32 := 0x00f707b3.
Lemma F_5b53c : fetch_word Asan.M.loaded_segments (0x5b58c : word) = Some W_5b53c.
Proof. vm_refl. Qed.
Lemma D_5b53c : decode_any W_5b53c = Some (Op ALU_ADD 15 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b540 : bv 32 := 0x00f63633.
Lemma F_5b540 : fetch_word Asan.M.loaded_segments (0x5b590 : word) = Some W_5b540.
Proof. vm_refl. Qed.
Lemma D_5b540 : decode_any W_5b540 = Some (Op ALU_SLTU 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b544 : bv 32 := 0x00e686b3.
Lemma F_5b544 : fetch_word Asan.M.loaded_segments (0x5b594 : word) = Some W_5b544.
Proof. vm_refl. Qed.
Lemma D_5b544 : decode_any W_5b544 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b548 : bv 32 := 0xfff60613.
Lemma F_5b548 : fetch_word Asan.M.loaded_segments (0x5b598 : word) = Some W_5b548.
Proof. vm_refl. Qed.
Lemma D_5b548 : decode_any W_5b548 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b54c : bv 32 := 0x00d67933.
Lemma F_5b54c : fetch_word Asan.M.loaded_segments (0x5b59c : word) = Some W_5b54c.
Proof. vm_refl. Qed.
Lemma D_5b54c : decode_any W_5b54c = Some (Op ALU_AND 18 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b550 : bv 32 := 0x08a96063.
Lemma F_5b550 : fetch_word Asan.M.loaded_segments (0x5b5a0 : word) = Some W_5b550.
Proof. vm_refl. Qed.
Lemma D_5b550 : decode_any W_5b550 = Some (Branch BC_LTU 18 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b554 : bv 32 := 0x06b97e63.
Lemma F_5b554 : fetch_word Asan.M.loaded_segments (0x5b5a4 : word) = Some W_5b554.
Proof. vm_refl. Qed.
Lemma D_5b554 : decode_any W_5b554 = Some (Branch BC_GEU 18 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b558 : bv 32 := 0x00990e63.
Lemma F_5b558 : fetch_word Asan.M.loaded_segments (0x5b5a8 : word) = Some W_5b558.
Proof. vm_refl. Qed.
Lemma D_5b558 : decode_any W_5b558 = Some (Branch BC_EQ 18 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b55c : bv 32 := 0xfffb5517.
Lemma F_5b55c : fetch_word Asan.M.loaded_segments (0x5b5ac : word) = Some W_5b55c.
Proof. vm_refl. Qed.
Lemma D_5b55c : decode_any W_5b55c = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b560 : bv 32 := 0xdd453703.
Lemma F_5b560 : fetch_word Asan.M.loaded_segments (0x5b5b0 : word) = Some W_5b560.
Proof. vm_refl. Qed.
Lemma D_5b560 : decode_any W_5b560 = Some (Load SZ8 true 14 10 3540, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b564 : bv 32 := 0x160936af.
Lemma F_5b564 : fetch_word Asan.M.loaded_segments (0x5b5b4 : word) = Some W_5b564.
Proof. vm_refl. Qed.
Lemma D_5b564 : decode_any W_5b564 = Some (Lr AD true true 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b568 : bv 32 := 0x16e69463.
Lemma F_5b568 : fetch_word Asan.M.loaded_segments (0x5b5b8 : word) = Some W_5b568.
Proof. vm_refl. Qed.
Lemma D_5b568 : decode_any W_5b568 = Some (Branch BC_NE 13 14 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b56c : bv 32 := 0x1a09352f.
Lemma F_5b56c : fetch_word Asan.M.loaded_segments (0x5b5bc : word) = Some W_5b56c.
Proof. vm_refl. Qed.
Lemma D_5b56c : decode_any W_5b56c = Some (Sc AD false true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b570 : bv 32 := 0xfe051ae3.
Lemma F_5b570 : fetch_word Asan.M.loaded_segments (0x5b5c0 : word) = Some W_5b570.
Proof. vm_refl. Qed.
Lemma D_5b570 : decode_any W_5b570 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b574 : bv 32 := 0xffc4f613.
Lemma F_5b574 : fetch_word Asan.M.loaded_segments (0x5b5c4 : word) = Some W_5b574.
Proof. vm_refl. Qed.
Lemma D_5b574 : decode_any W_5b574 = Some (OpImm ALU_AND 12 9 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b578 : bv 32 := 0x00349513.
Lemma F_5b578 : fetch_word Asan.M.loaded_segments (0x5b5c8 : word) = Some W_5b578.
Proof. vm_refl. Qed.
Lemma D_5b578 : decode_any W_5b578 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b57c : bv 32 := 0x0ff00593.
Lemma F_5b57c : fetch_word Asan.M.loaded_segments (0x5b5cc : word) = Some W_5b57c.
Proof. vm_refl. Qed.
Lemma D_5b57c : decode_any W_5b57c = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b580 : bv 32 := 0x00300693.
Lemma F_5b580 : fetch_word Asan.M.loaded_segments (0x5b5d0 : word) = Some W_5b580.
Proof. vm_refl. Qed.
Lemma D_5b580 : decode_any W_5b580 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b584 : bv 32 := 0x00a5973b.
Lemma F_5b584 : fetch_word Asan.M.loaded_segments (0x5b5d4 : word) = Some W_5b584.
Proof. vm_refl. Qed.
Lemma D_5b584 : decode_any W_5b584 = Some (Op32 ALU_SLL 14 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b588 : bv 32 := 0x00a696bb.
Lemma F_5b588 : fetch_word Asan.M.loaded_segments (0x5b5d8 : word) = Some W_5b588.
Proof. vm_refl. Qed.
Lemma D_5b588 : decode_any W_5b588 = Some (Op32 ALU_SLL 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b58c : bv 32 := 0x160625af.
Lemma F_5b58c : fetch_word Asan.M.loaded_segments (0x5b5dc : word) = Some W_5b58c.
Proof. vm_refl. Qed.
Lemma D_5b58c : decode_any W_5b58c = Some (Lr AW true true 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b590 : bv 32 := 0x00e5f7b3.
Lemma F_5b590 : fetch_word Asan.M.loaded_segments (0x5b5e0 : word) = Some W_5b590.
Proof. vm_refl. Qed.
Lemma D_5b590 : decode_any W_5b590 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b594 : bv 32 := 0x10d79c63.
Lemma F_5b594 : fetch_word Asan.M.loaded_segments (0x5b5e4 : word) = Some W_5b594.
Proof. vm_refl. Qed.
Lemma D_5b594 : decode_any W_5b594 = Some (Branch BC_NE 15 13 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b598 : bv 32 := 0x0005c7b3.
Lemma F_5b598 : fetch_word Asan.M.loaded_segments (0x5b5e8 : word) = Some W_5b598.
Proof. vm_refl. Qed.
Lemma D_5b598 : decode_any W_5b598 = Some (Op ALU_XOR 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b59c : bv 32 := 0x00e7f7b3.
Lemma F_5b59c : fetch_word Asan.M.loaded_segments (0x5b5ec : word) = Some W_5b59c.
Proof. vm_refl. Qed.
Lemma D_5b59c : decode_any W_5b59c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5a0 : bv 32 := 0x00f5c7b3.
Lemma F_5b5a0 : fetch_word Asan.M.loaded_segments (0x5b5f0 : word) = Some W_5b5a0.
Proof. vm_refl. Qed.
Lemma D_5b5a0 : decode_any W_5b5a0 = Some (Op ALU_XOR 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5a4 : bv 32 := 0x1af627af.
Lemma F_5b5a4 : fetch_word Asan.M.loaded_segments (0x5b5f4 : word) = Some W_5b5a4.
Proof. vm_refl. Qed.
Lemma D_5b5a4 : decode_any W_5b5a4 = Some (Sc AW false true 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5a8 : bv 32 := 0xfe0792e3.
Lemma F_5b5a8 : fetch_word Asan.M.loaded_segments (0x5b5f8 : word) = Some W_5b5a8.
Proof. vm_refl. Qed.
Lemma D_5b5a8 : decode_any W_5b5a8 = Some (Branch BC_NE 15 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5ac : bv 32 := 0x0024d583.
Lemma F_5b5ac : fetch_word Asan.M.loaded_segments (0x5b5fc : word) = Some W_5b5ac.
Proof. vm_refl. Qed.
Lemma D_5b5ac : decode_any W_5b5ac = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5b0 : bv 32 := 0x0044e603.
Lemma F_5b5b0 : fetch_word Asan.M.loaded_segments (0x5b600 : word) = Some W_5b5b0.
Proof. vm_refl. Qed.
Lemma D_5b5b0 : decode_any W_5b5b0 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5b4 : bv 32 := 0x01048513.
Lemma F_5b5b4 : fetch_word Asan.M.loaded_segments (0x5b604 : word) = Some W_5b5b4.
Proof. vm_refl. Qed.
Lemma D_5b5b4 : decode_any W_5b5b4 = Some (OpImm ALU_ADD 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5b8 : bv 32 := 0x02059593.
Lemma F_5b5b8 : fetch_word Asan.M.loaded_segments (0x5b608 : word) = Some W_5b5b8.
Proof. vm_refl. Qed.
Lemma D_5b5b8 : decode_any W_5b5b8 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5bc : bv 32 := 0x00c5e5b3.
Lemma F_5b5bc : fetch_word Asan.M.loaded_segments (0x5b60c : word) = Some W_5b5bc.
Proof. vm_refl. Qed.
Lemma D_5b5bc : decode_any W_5b5bc = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5c0 : bv 32 := 0x00758593.
Lemma F_5b5c0 : fetch_word Asan.M.loaded_segments (0x5b610 : word) = Some W_5b5c0.
Proof. vm_refl. Qed.
Lemma D_5b5c0 : decode_any W_5b5c0 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5c4 : bv 32 := 0xff85f593.
Lemma F_5b5c4 : fetch_word Asan.M.loaded_segments (0x5b614 : word) = Some W_5b5c4.
Proof. vm_refl. Qed.
Lemma D_5b5c4 : decode_any W_5b5c4 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5c8 : bv 32 := 0x0fa00613.
Lemma F_5b5c8 : fetch_word Asan.M.loaded_segments (0x5b618 : word) = Some W_5b5c8.
Proof. vm_refl. Qed.
Lemma D_5b5c8 : decode_any W_5b5c8 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5cc : bv 32 := 0x444260ef.
Lemma F_5b5cc : fetch_word Asan.M.loaded_segments (0x5b61c : word) = Some W_5b5cc.
Proof. vm_refl. Qed.
Lemma D_5b5cc : decode_any W_5b5cc = Some (Jal 1 156740, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5d0 : bv 32 := 0x3b82e0ef.
Lemma F_5b5d0 : fetch_word Asan.M.loaded_segments (0x5b620 : word) = Some W_5b5d0.
Proof. vm_refl. Qed.
Lemma D_5b5d0 : decode_any W_5b5d0 = Some (Jal 1 189368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5d4 : bv 32 := 0x0024d583.
Lemma F_5b5d4 : fetch_word Asan.M.loaded_segments (0x5b624 : word) = Some W_5b5d4.
Proof. vm_refl. Qed.
Lemma D_5b5d4 : decode_any W_5b5d4 = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5d8 : bv 32 := 0x0044e603.
Lemma F_5b5d8 : fetch_word Asan.M.loaded_segments (0x5b628 : word) = Some W_5b5d8.
Proof. vm_refl. Qed.
Lemma D_5b5d8 : decode_any W_5b5d8 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5dc : bv 32 := 0x03053683.
Lemma F_5b5dc : fetch_word Asan.M.loaded_segments (0x5b62c : word) = Some W_5b5dc.
Proof. vm_refl. Qed.
Lemma D_5b5dc : decode_any W_5b5dc = Some (Load SZ8 true 13 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e0 : bv 32 := 0x02853703.
Lemma F_5b5e0 : fetch_word Asan.M.loaded_segments (0x5b630 : word) = Some W_5b5e0.
Proof. vm_refl. Qed.
Lemma D_5b5e0 : decode_any W_5b5e0 = Some (Load SZ8 true 14 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e4 : bv 32 := 0x02059593.
Lemma F_5b5e4 : fetch_word Asan.M.loaded_segments (0x5b634 : word) = Some W_5b5e4.
Proof. vm_refl. Qed.
Lemma D_5b5e4 : decode_any W_5b5e4 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e8 : bv 32 := 0x00c5e5b3.
Lemma F_5b5e8 : fetch_word Asan.M.loaded_segments (0x5b638 : word) = Some W_5b5e8.
Proof. vm_refl. Qed.
Lemma D_5b5e8 : decode_any W_5b5e8 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5ec : bv 32 := 0x00d585b3.
Lemma F_5b5ec : fetch_word Asan.M.loaded_segments (0x5b63c : word) = Some W_5b5ec.
Proof. vm_refl. Qed.
Lemma D_5b5ec : decode_any W_5b5ec = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f0 : bv 32 := 0x00170713.
Lemma F_5b5f0 : fetch_word Asan.M.loaded_segments (0x5b640 : word) = Some W_5b5f0.
Proof. vm_refl. Qed.
Lemma D_5b5f0 : decode_any W_5b5f0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f4 : bv 32 := 0x02e53423.
Lemma F_5b5f4 : fetch_word Asan.M.loaded_segments (0x5b644 : word) = Some W_5b5f4.
Proof. vm_refl. Qed.
Lemma D_5b5f4 : decode_any W_5b5f4 = Some (Store SZ8 10 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f8 : bv 32 := 0x02b53823.
Lemma F_5b5f8 : fetch_word Asan.M.loaded_segments (0x5b648 : word) = Some W_5b5f8.
Proof. vm_refl. Qed.
Lemma D_5b5f8 : decode_any W_5b5f8 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5fc : bv 32 := 0x04090863.
Lemma F_5b5fc : fetch_word Asan.M.loaded_segments (0x5b64c : word) = Some W_5b5fc.
Proof. vm_refl. Qed.
Lemma D_5b5fc : decode_any W_5b5fc = Some (Branch BC_EQ 18 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b600 : bv 32 := 0x0209b583.
Lemma F_5b600 : fetch_word Asan.M.loaded_segments (0x5b650 : word) = Some W_5b600.
Proof. vm_refl. Qed.
Lemma D_5b600 : decode_any W_5b600 = Some (Load SZ8 true 11 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b604 : bv 32 := 0x06b96463.
Lemma F_5b604 : fetch_word Asan.M.loaded_segments (0x5b654 : word) = Some W_5b604.
Proof. vm_refl. Qed.
Lemma D_5b604 : decode_any W_5b604 = Some (Branch BC_LTU 18 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b608 : bv 32 := 0x01458a33.
Lemma F_5b608 : fetch_word Asan.M.loaded_segments (0x5b658 : word) = Some W_5b608.
Proof. vm_refl. Qed.
Lemma D_5b608 : decode_any W_5b608 = Some (Op ALU_ADD 20 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b60c : bv 32 := 0x07497063.
Lemma F_5b60c : fetch_word Asan.M.loaded_segments (0x5b65c : word) = Some W_5b60c.
Proof. vm_refl. Qed.
Lemma D_5b60c : decode_any W_5b60c = Some (Branch BC_GEU 18 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b610 : bv 32 := 0x00043503.
Lemma F_5b610 : fetch_word Asan.M.loaded_segments (0x5b660 : word) = Some W_5b610.
Proof. vm_refl. Qed.
Lemma D_5b610 : decode_any W_5b610 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b614 : bv 32 := 0x40b905b3.
Lemma F_5b614 : fetch_word Asan.M.loaded_segments (0x5b664 : word) = Some W_5b614.
Proof. vm_refl. Qed.
Lemma D_5b614 : decode_any W_5b614 = Some (Op ALU_SUB 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b618 : bv 32 := 0x01b59593.
Lemma F_5b618 : fetch_word Asan.M.loaded_segments (0x5b668 : word) = Some W_5b618.
Proof. vm_refl. Qed.
Lemma D_5b618 : decode_any W_5b618 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b61c : bv 32 := 0x03b5d613.
Lemma F_5b61c : fetch_word Asan.M.loaded_segments (0x5b66c : word) = Some W_5b61c.
Proof. vm_refl. Qed.
Lemma D_5b61c : decode_any W_5b61c = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b620 : bv 32 := 0x00101597.
Lemma F_5b620 : fetch_word Asan.M.loaded_segments (0x5b670 : word) = Some W_5b620.
Proof. vm_refl. Qed.
Lemma D_5b620 : decode_any W_5b620 = Some (Auipc 11 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b624 : bv 32 := 0xda858593.
Lemma F_5b624 : fetch_word Asan.M.loaded_segments (0x5b674 : word) = Some W_5b624.
Proof. vm_refl. Qed.
Lemma D_5b624 : decode_any W_5b624 = Some (OpImm ALU_ADD 11 11 3496, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b628 : bv 32 := 0x00090693.
Lemma F_5b628 : fetch_word Asan.M.loaded_segments (0x5b678 : word) = Some W_5b628.
Proof. vm_refl. Qed.
Lemma D_5b628 : decode_any W_5b628 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b62c : bv 32 := 0x02813083.
Lemma F_5b62c : fetch_word Asan.M.loaded_segments (0x5b67c : word) = Some W_5b62c.
Proof. vm_refl. Qed.
Lemma D_5b62c : decode_any W_5b62c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b630 : bv 32 := 0x02013403.
Lemma F_5b630 : fetch_word Asan.M.loaded_segments (0x5b680 : word) = Some W_5b630.
Proof. vm_refl. Qed.
Lemma D_5b630 : decode_any W_5b630 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b634 : bv 32 := 0x01813483.
Lemma F_5b634 : fetch_word Asan.M.loaded_segments (0x5b684 : word) = Some W_5b634.
Proof. vm_refl. Qed.
Lemma D_5b634 : decode_any W_5b634 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b638 : bv 32 := 0x01013903.
Lemma F_5b638 : fetch_word Asan.M.loaded_segments (0x5b688 : word) = Some W_5b638.
Proof. vm_refl. Qed.
Lemma D_5b638 : decode_any W_5b638 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b63c : bv 32 := 0x00813983.
Lemma F_5b63c : fetch_word Asan.M.loaded_segments (0x5b68c : word) = Some W_5b63c.
Proof. vm_refl. Qed.
Lemma D_5b63c : decode_any W_5b63c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b640 : bv 32 := 0x00013a03.
Lemma F_5b640 : fetch_word Asan.M.loaded_segments (0x5b690 : word) = Some W_5b640.
Proof. vm_refl. Qed.
Lemma D_5b640 : decode_any W_5b640 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b644 : bv 32 := 0x03010113.
Lemma F_5b644 : fetch_word Asan.M.loaded_segments (0x5b694 : word) = Some W_5b644.
Proof. vm_refl. Qed.
Lemma D_5b644 : decode_any W_5b644 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b648 : bv 32 := 0x2200006f.
Lemma F_5b648 : fetch_word Asan.M.loaded_segments (0x5b698 : word) = Some W_5b648.
Proof. vm_refl. Qed.
Lemma D_5b648 : decode_any W_5b648 = Some (Jal 0 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b66c : bv 32 := 0x04098513.
Lemma F_5b66c : fetch_word Asan.M.loaded_segments (0x5b6bc : word) = Some W_5b66c.
Proof. vm_refl. Qed.
Lemma D_5b66c : decode_any W_5b66c = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b670 : bv 32 := 0x2b098593.
Lemma F_5b670 : fetch_word Asan.M.loaded_segments (0x5b6c0 : word) = Some W_5b670.
Proof. vm_refl. Qed.
Lemma D_5b670 : decode_any W_5b670 = Some (OpImm ALU_ADD 11 19 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b674 : bv 32 := 0x00090613.
Lemma F_5b674 : fetch_word Asan.M.loaded_segments (0x5b6c4 : word) = Some W_5b674.
Proof. vm_refl. Qed.
Lemma D_5b674 : decode_any W_5b674 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b678 : bv 32 := 0x02813083.
Lemma F_5b678 : fetch_word Asan.M.loaded_segments (0x5b6c8 : word) = Some W_5b678.
Proof. vm_refl. Qed.
Lemma D_5b678 : decode_any W_5b678 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b67c : bv 32 := 0x02013403.
Lemma F_5b67c : fetch_word Asan.M.loaded_segments (0x5b6cc : word) = Some W_5b67c.
Proof. vm_refl. Qed.
Lemma D_5b67c : decode_any W_5b67c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b680 : bv 32 := 0x01813483.
Lemma F_5b680 : fetch_word Asan.M.loaded_segments (0x5b6d0 : word) = Some W_5b680.
Proof. vm_refl. Qed.
Lemma D_5b680 : decode_any W_5b680 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b684 : bv 32 := 0x01013903.
Lemma F_5b684 : fetch_word Asan.M.loaded_segments (0x5b6d4 : word) = Some W_5b684.
Proof. vm_refl. Qed.
Lemma D_5b684 : decode_any W_5b684 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b688 : bv 32 := 0x00813983.
Lemma F_5b688 : fetch_word Asan.M.loaded_segments (0x5b6d8 : word) = Some W_5b688.
Proof. vm_refl. Qed.
Lemma D_5b688 : decode_any W_5b688 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b68c : bv 32 := 0x00013a03.
Lemma F_5b68c : fetch_word Asan.M.loaded_segments (0x5b6dc : word) = Some W_5b68c.
Proof. vm_refl. Qed.
Lemma D_5b68c : decode_any W_5b68c = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b690 : bv 32 := 0x03010113.
Lemma F_5b690 : fetch_word Asan.M.loaded_segments (0x5b6e0 : word) = Some W_5b690.
Proof. vm_refl. Qed.
Lemma D_5b690 : decode_any W_5b690 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b694 : bv 32 := 0x39c0006f.
Lemma F_5b694 : fetch_word Asan.M.loaded_segments (0x5b6e4 : word) = Some W_5b694.
Proof. vm_refl. Qed.
Lemma D_5b694 : decode_any W_5b694 = Some (Jal 0 924, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6e8 : bv 32 := 0xfe010113.
Lemma F_5b6e8 : fetch_word Asan.M.loaded_segments (0x5b738 : word) = Some W_5b6e8.
Proof. vm_refl. Qed.
Lemma D_5b6e8 : decode_any W_5b6e8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6ec : bv 32 := 0x00113c23.
Lemma F_5b6ec : fetch_word Asan.M.loaded_segments (0x5b73c : word) = Some W_5b6ec.
Proof. vm_refl. Qed.
Lemma D_5b6ec : decode_any W_5b6ec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6f0 : bv 32 := 0x00813823.
Lemma F_5b6f0 : fetch_word Asan.M.loaded_segments (0x5b740 : word) = Some W_5b6f0.
Proof. vm_refl. Qed.
Lemma D_5b6f0 : decode_any W_5b6f0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6f4 : bv 32 := 0x00913423.
Lemma F_5b6f4 : fetch_word Asan.M.loaded_segments (0x5b744 : word) = Some W_5b6f4.
Proof. vm_refl. Qed.
Lemma D_5b6f4 : decode_any W_5b6f4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6f8 : bv 32 := 0x01213023.
Lemma F_5b6f8 : fetch_word Asan.M.loaded_segments (0x5b748 : word) = Some W_5b6f8.
Proof. vm_refl. Qed.
Lemma D_5b6f8 : decode_any W_5b6f8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6fc : bv 32 := 0x26850413.
Lemma F_5b6fc : fetch_word Asan.M.loaded_segments (0x5b74c : word) = Some W_5b6fc.
Proof. vm_refl. Qed.
Lemma D_5b6fc : decode_any W_5b6fc = Some (OpImm ALU_ADD 8 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b700 : bv 32 := 0x0ff00613.
Lemma F_5b700 : fetch_word Asan.M.loaded_segments (0x5b750 : word) = Some W_5b700.
Proof. vm_refl. Qed.
Lemma D_5b700 : decode_any W_5b700 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b704 : bv 32 := 0xffc47693.
Lemma F_5b704 : fetch_word Asan.M.loaded_segments (0x5b754 : word) = Some W_5b704.
Proof. vm_refl. Qed.
Lemma D_5b704 : decode_any W_5b704 = Some (OpImm ALU_AND 13 8 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b708 : bv 32 := 0x00100713.
Lemma F_5b708 : fetch_word Asan.M.loaded_segments (0x5b758 : word) = Some W_5b708.
Proof. vm_refl. Qed.
Lemma D_5b708 : decode_any W_5b708 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b70c : bv 32 := 0x1406a7af.
Lemma F_5b70c : fetch_word Asan.M.loaded_segments (0x5b75c : word) = Some W_5b70c.
Proof. vm_refl. Qed.
Lemma D_5b70c : decode_any W_5b70c = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b710 : bv 32 := 0x00070813.
Lemma F_5b710 : fetch_word Asan.M.loaded_segments (0x5b760 : word) = Some W_5b710.
Proof. vm_refl. Qed.
Lemma D_5b710 : decode_any W_5b710 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b714 : bv 32 := 0x0107c833.
Lemma F_5b714 : fetch_word Asan.M.loaded_segments (0x5b764 : word) = Some W_5b714.
Proof. vm_refl. Qed.
Lemma D_5b714 : decode_any W_5b714 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b718 : bv 32 := 0x00c87833.
Lemma F_5b718 : fetch_word Asan.M.loaded_segments (0x5b768 : word) = Some W_5b718.
Proof. vm_refl. Qed.
Lemma D_5b718 : decode_any W_5b718 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b71c : bv 32 := 0x0107c833.
Lemma F_5b71c : fetch_word Asan.M.loaded_segments (0x5b76c : word) = Some W_5b71c.
Proof. vm_refl. Qed.
Lemma D_5b71c : decode_any W_5b71c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b720 : bv 32 := 0x1906a82f.
Lemma F_5b720 : fetch_word Asan.M.loaded_segments (0x5b770 : word) = Some W_5b720.
Proof. vm_refl. Qed.
Lemma D_5b720 : decode_any W_5b720 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b724 : bv 32 := 0xfe0814e3.
Lemma F_5b724 : fetch_word Asan.M.loaded_segments (0x5b774 : word) = Some W_5b724.
Proof. vm_refl. Qed.
Lemma D_5b724 : decode_any W_5b724 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b728 : bv 32 := 0x0ff7f613.
Lemma F_5b728 : fetch_word Asan.M.loaded_segments (0x5b778 : word) = Some W_5b728.
Proof. vm_refl. Qed.
Lemma D_5b728 : decode_any W_5b728 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b72c : bv 32 := 0x08061663.
Lemma F_5b72c : fetch_word Asan.M.loaded_segments (0x5b77c : word) = Some W_5b72c.
Proof. vm_refl. Qed.
Lemma D_5b72c : decode_any W_5b72c = Some (Branch BC_NE 12 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b730 : bv 32 := 0x03853703.
Lemma F_5b730 : fetch_word Asan.M.loaded_segments (0x5b780 : word) = Some W_5b730.
Proof. vm_refl. Qed.
Lemma D_5b730 : decode_any W_5b730 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b734 : bv 32 := 0x0a070263.
Lemma F_5b734 : fetch_word Asan.M.loaded_segments (0x5b784 : word) = Some W_5b734.
Proof. vm_refl. Qed.
Lemma D_5b734 : decode_any W_5b734 = Some (Branch BC_EQ 14 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b738 : bv 32 := 0x00000693.
Lemma F_5b738 : fetch_word Asan.M.loaded_segments (0x5b788 : word) = Some W_5b738.
Proof. vm_refl. Qed.
Lemma D_5b738 : decode_any W_5b738 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b73c : bv 32 := 0x00853603.
Lemma F_5b73c : fetch_word Asan.M.loaded_segments (0x5b78c : word) = Some W_5b73c.
Proof. vm_refl. Qed.
Lemma D_5b73c : decode_any W_5b73c = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b740 : bv 32 := 0x00371713.
Lemma F_5b740 : fetch_word Asan.M.loaded_segments (0x5b790 : word) = Some W_5b740.
Proof. vm_refl. Qed.
Lemma D_5b740 : decode_any W_5b740 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b744 : bv 32 := 0x00e60733.
Lemma F_5b744 : fetch_word Asan.M.loaded_segments (0x5b794 : word) = Some W_5b744.
Proof. vm_refl. Qed.
Lemma D_5b744 : decode_any W_5b744 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b748 : bv 32 := 0x00c0006f.
Lemma F_5b748 : fetch_word Asan.M.loaded_segments (0x5b798 : word) = Some W_5b748.
Proof. vm_refl. Qed.
Lemma D_5b748 : decode_any W_5b748 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b74c : bv 32 := 0x00860613.
Lemma F_5b74c : fetch_word Asan.M.loaded_segments (0x5b79c : word) = Some W_5b74c.
Proof. vm_refl. Qed.
Lemma D_5b74c : decode_any W_5b74c = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b750 : bv 32 := 0x02e60863.
Lemma F_5b750 : fetch_word Asan.M.loaded_segments (0x5b7a0 : word) = Some W_5b750.
Proof. vm_refl. Qed.
Lemma D_5b750 : decode_any W_5b750 = Some (Branch BC_EQ 12 14 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b754 : bv 32 := 0x00063783.
Lemma F_5b754 : fetch_word Asan.M.loaded_segments (0x5b7a4 : word) = Some W_5b754.
Proof. vm_refl. Qed.
Lemma D_5b754 : decode_any W_5b754 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b758 : bv 32 := 0x40f588b3.
Lemma F_5b758 : fetch_word Asan.M.loaded_segments (0x5b7a8 : word) = Some W_5b758.
Proof. vm_refl. Qed.
Lemma D_5b758 : decode_any W_5b758 = Some (Op ALU_SUB 17 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b75c : bv 32 := 0x40d582b3.
Lemma F_5b75c : fetch_word Asan.M.loaded_segments (0x5b7ac : word) = Some W_5b75c.
Proof. vm_refl. Qed.
Lemma D_5b75c : decode_any W_5b75c = Some (Op ALU_SUB 5 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b760 : bv 32 := 0x00078813.
Lemma F_5b760 : fetch_word Asan.M.loaded_segments (0x5b7b0 : word) = Some W_5b760.
Proof. vm_refl. Qed.
Lemma D_5b760 : decode_any W_5b760 = Some (OpImm ALU_ADD 16 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b764 : bv 32 := 0x0058e863.
Lemma F_5b764 : fetch_word Asan.M.loaded_segments (0x5b7b4 : word) = Some W_5b764.
Proof. vm_refl. Qed.
Lemma D_5b764 : decode_any W_5b764 = Some (Branch BC_LTU 17 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b768 : bv 32 := 0x00068813.
Lemma F_5b768 : fetch_word Asan.M.loaded_segments (0x5b7b8 : word) = Some W_5b768.
Proof. vm_refl. Qed.
Lemma D_5b768 : decode_any W_5b768 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b76c : bv 32 := 0xfef5e0e3.
Lemma F_5b76c : fetch_word Asan.M.loaded_segments (0x5b7bc : word) = Some W_5b76c.
Proof. vm_refl. Qed.
Lemma D_5b76c : decode_any W_5b76c = Some (Branch BC_LTU 11 15 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b770 : bv 32 := 0x0080006f.
Lemma F_5b770 : fetch_word Asan.M.loaded_segments (0x5b7c0 : word) = Some W_5b770.
Proof. vm_refl. Qed.
Lemma D_5b770 : decode_any W_5b770 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b774 : bv 32 := 0xfcf5ece3.
Lemma F_5b774 : fetch_word Asan.M.loaded_segments (0x5b7c4 : word) = Some W_5b774.
Proof. vm_refl. Qed.
Lemma D_5b774 : decode_any W_5b774 = Some (Branch BC_LTU 11 15 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b778 : bv 32 := 0x00080693.
Lemma F_5b778 : fetch_word Asan.M.loaded_segments (0x5b7c8 : word) = Some W_5b778.
Proof. vm_refl. Qed.
Lemma D_5b778 : decode_any W_5b778 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b77c : bv 32 := 0xfd1ff06f.
Lemma F_5b77c : fetch_word Asan.M.loaded_segments (0x5b7cc : word) = Some W_5b77c.
Proof. vm_refl. Qed.
Lemma D_5b77c : decode_any W_5b77c = Some (Jal 0 2097104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b780 : bv 32 := 0x04068c63.
Lemma F_5b780 : fetch_word Asan.M.loaded_segments (0x5b7d0 : word) = Some W_5b780.
Proof. vm_refl. Qed.
Lemma D_5b780 : decode_any W_5b780 = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b784 : bv 32 := 0x0006b703.
Lemma F_5b784 : fetch_word Asan.M.loaded_segments (0x5b7d4 : word) = Some W_5b784.
Proof. vm_refl. Qed.
Lemma D_5b784 : decode_any W_5b784 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b788 : bv 32 := 0x06e6ea63.
Lemma F_5b788 : fetch_word Asan.M.loaded_segments (0x5b7d8 : word) = Some W_5b788.
Proof. vm_refl. Qed.
Lemma D_5b788 : decode_any W_5b788 = Some (Branch BC_LTU 13 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b78c : bv 32 := 0x0086b603.
Lemma F_5b78c : fetch_word Asan.M.loaded_segments (0x5b7dc : word) = Some W_5b78c.
Proof. vm_refl. Qed.
Lemma D_5b78c : decode_any W_5b78c = Some (Load SZ8 true 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b790 : bv 32 := 0x00e60733.
Lemma F_5b790 : fetch_word Asan.M.loaded_segments (0x5b7e0 : word) = Some W_5b790.
Proof. vm_refl. Qed.
Lemma D_5b790 : decode_any W_5b790 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b794 : bv 32 := 0x08e6f063.
Lemma F_5b794 : fetch_word Asan.M.loaded_segments (0x5b7e4 : word) = Some W_5b794.
Proof. vm_refl. Qed.
Lemma D_5b794 : decode_any W_5b794 = Some (Branch BC_GEU 13 14 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b798 : bv 32 := 0x08d5ea63.
Lemma F_5b798 : fetch_word Asan.M.loaded_segments (0x5b7e8 : word) = Some W_5b798.
Proof. vm_refl. Qed.
Lemma D_5b798 : decode_any W_5b798 = Some (Branch BC_LTU 11 13 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b79c : bv 32 := 0x02e5fe63.
Lemma F_5b79c : fetch_word Asan.M.loaded_segments (0x5b7ec : word) = Some W_5b79c.
Proof. vm_refl. Qed.
Lemma D_5b79c : decode_any W_5b79c = Some (Branch BC_GEU 11 14 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a0 : bv 32 := 0x00053503.
Lemma F_5b7a0 : fetch_word Asan.M.loaded_segments (0x5b7f0 : word) = Some W_5b7a0.
Proof. vm_refl. Qed.
Lemma D_5b7a0 : decode_any W_5b7a0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a4 : bv 32 := 0xfff50593.
Lemma F_5b7a4 : fetch_word Asan.M.loaded_segments (0x5b7f4 : word) = Some W_5b7a4.
Proof. vm_refl. Qed.
Lemma D_5b7a4 : decode_any W_5b7a4 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a8 : bv 32 := 0x00d5f5b3.
Lemma F_5b7a8 : fetch_word Asan.M.loaded_segments (0x5b7f8 : word) = Some W_5b7a8.
Proof. vm_refl. Qed.
Lemma D_5b7a8 : decode_any W_5b7a8 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7ac : bv 32 := 0x08059e63.
Lemma F_5b7ac : fetch_word Asan.M.loaded_segments (0x5b7fc : word) = Some W_5b7ac.
Proof. vm_refl. Qed.
Lemma D_5b7ac : decode_any W_5b7ac = Some (Branch BC_NE 11 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b0 : bv 32 := 0x00d50533.
Lemma F_5b7b0 : fetch_word Asan.M.loaded_segments (0x5b800 : word) = Some W_5b7b0.
Proof. vm_refl. Qed.
Lemma D_5b7b0 : decode_any W_5b7b0 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b4 : bv 32 := 0x0280006f.
Lemma F_5b7b4 : fetch_word Asan.M.loaded_segments (0x5b804 : word) = Some W_5b7b4.
Proof. vm_refl. Qed.
Lemma D_5b7b4 : decode_any W_5b7b4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7dc : bv 32 := 0x0310000f.
Lemma F_5b7dc : fetch_word Asan.M.loaded_segments (0x5b82c : word) = Some W_5b7dc.
Proof. vm_refl. Qed.
Lemma D_5b7dc : decode_any W_5b7dc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7e0 : bv 32 := 0x00040023.
Lemma F_5b7e0 : fetch_word Asan.M.loaded_segments (0x5b830 : word) = Some W_5b7e0.
Proof. vm_refl. Qed.
Lemma D_5b7e0 : decode_any W_5b7e0 = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7e4 : bv 32 := 0x01813083.
Lemma F_5b7e4 : fetch_word Asan.M.loaded_segments (0x5b834 : word) = Some W_5b7e4.
Proof. vm_refl. Qed.
Lemma D_5b7e4 : decode_any W_5b7e4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7e8 : bv 32 := 0x01013403.
Lemma F_5b7e8 : fetch_word Asan.M.loaded_segments (0x5b838 : word) = Some W_5b7e8.
Proof. vm_refl. Qed.
Lemma D_5b7e8 : decode_any W_5b7e8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7ec : bv 32 := 0x00813483.
Lemma F_5b7ec : fetch_word Asan.M.loaded_segments (0x5b83c : word) = Some W_5b7ec.
Proof. vm_refl. Qed.
Lemma D_5b7ec : decode_any W_5b7ec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7f0 : bv 32 := 0x00013903.
Lemma F_5b7f0 : fetch_word Asan.M.loaded_segments (0x5b840 : word) = Some W_5b7f0.
Proof. vm_refl. Qed.
Lemma D_5b7f0 : decode_any W_5b7f0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7f4 : bv 32 := 0x02010113.
Lemma F_5b7f4 : fetch_word Asan.M.loaded_segments (0x5b844 : word) = Some W_5b7f4.
Proof. vm_refl. Qed.
Lemma D_5b7f4 : decode_any W_5b7f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7f8 : bv 32 := 0x00008067.
Lemma F_5b7f8 : fetch_word Asan.M.loaded_segments (0x5b848 : word) = Some W_5b7f8.
Proof. vm_refl. Qed.
Lemma D_5b7f8 : decode_any W_5b7f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b868 : bv 32 := 0xfd010113.
Lemma F_5b868 : fetch_word Asan.M.loaded_segments (0x5b8b8 : word) = Some W_5b868.
Proof. vm_refl. Qed.
Lemma D_5b868 : decode_any W_5b868 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b86c : bv 32 := 0x02113423.
Lemma F_5b86c : fetch_word Asan.M.loaded_segments (0x5b8bc : word) = Some W_5b86c.
Proof. vm_refl. Qed.
Lemma D_5b86c : decode_any W_5b86c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b870 : bv 32 := 0x02813023.
Lemma F_5b870 : fetch_word Asan.M.loaded_segments (0x5b8c0 : word) = Some W_5b870.
Proof. vm_refl. Qed.
Lemma D_5b870 : decode_any W_5b870 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b874 : bv 32 := 0x00913c23.
Lemma F_5b874 : fetch_word Asan.M.loaded_segments (0x5b8c4 : word) = Some W_5b874.
Proof. vm_refl. Qed.
Lemma D_5b874 : decode_any W_5b874 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b878 : bv 32 := 0x01213823.
Lemma F_5b878 : fetch_word Asan.M.loaded_segments (0x5b8c8 : word) = Some W_5b878.
Proof. vm_refl. Qed.
Lemma D_5b878 : decode_any W_5b878 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b87c : bv 32 := 0x01313423.
Lemma F_5b87c : fetch_word Asan.M.loaded_segments (0x5b8cc : word) = Some W_5b87c.
Proof. vm_refl. Qed.
Lemma D_5b87c : decode_any W_5b87c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b880 : bv 32 := 0x01413023.
Lemma F_5b880 : fetch_word Asan.M.loaded_segments (0x5b8d0 : word) = Some W_5b880.
Proof. vm_refl. Qed.
Lemma D_5b880 : decode_any W_5b880 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b884 : bv 32 := 0x08060463.
Lemma F_5b884 : fetch_word Asan.M.loaded_segments (0x5b8d4 : word) = Some W_5b884.
Proof. vm_refl. Qed.
Lemma D_5b884 : decode_any W_5b884 = Some (Branch BC_EQ 12 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b888 : bv 32 := 0x02000713.
Lemma F_5b888 : fetch_word Asan.M.loaded_segments (0x5b8d8 : word) = Some W_5b888.
Proof. vm_refl. Qed.
Lemma D_5b888 : decode_any W_5b888 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b88c : bv 32 := 0x0ae67063.
Lemma F_5b88c : fetch_word Asan.M.loaded_segments (0x5b8dc : word) = Some W_5b88c.
Proof. vm_refl. Qed.
Lemma D_5b88c : decode_any W_5b88c = Some (Branch BC_GEU 12 14 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b890 : bv 32 := 0x05000713.
Lemma F_5b890 : fetch_word Asan.M.loaded_segments (0x5b8e0 : word) = Some W_5b890.
Proof. vm_refl. Qed.
Lemma D_5b890 : decode_any W_5b890 = Some (OpImm ALU_ADD 14 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b894 : bv 32 := 0x02e60433.
Lemma F_5b894 : fetch_word Asan.M.loaded_segments (0x5b8e4 : word) = Some W_5b894.
Proof. vm_refl. Qed.
Lemma D_5b894 : decode_any W_5b894 = Some (Mul M_MUL 8 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b898 : bv 32 := 0x00850433.
Lemma F_5b898 : fetch_word Asan.M.loaded_segments (0x5b8e8 : word) = Some W_5b898.
Proof. vm_refl. Qed.
Lemma D_5b898 : decode_any W_5b898 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b89c : bv 32 := 0x00442783.
Lemma F_5b89c : fetch_word Asan.M.loaded_segments (0x5b8ec : word) = Some W_5b89c.
Proof. vm_refl. Qed.
Lemma D_5b89c : decode_any W_5b89c = Some (Load SZ4 true 15 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8a0 : bv 32 := 0x0a078863.
Lemma F_5b8a0 : fetch_word Asan.M.loaded_segments (0x5b8f0 : word) = Some W_5b8a0.
Proof. vm_refl. Qed.
Lemma D_5b8a0 : decode_any W_5b8a0 = Some (Branch BC_EQ 15 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8a4 : bv 32 := 0x00042703.
Lemma F_5b8a4 : fetch_word Asan.M.loaded_segments (0x5b8f4 : word) = Some W_5b8a4.
Proof. vm_refl. Qed.
Lemma D_5b8a4 : decode_any W_5b8a4 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8a8 : bv 32 := 0x14f70863.
Lemma F_5b8a8 : fetch_word Asan.M.loaded_segments (0x5b8f8 : word) = Some W_5b8a8.
Proof. vm_refl. Qed.
Lemma D_5b8a8 : decode_any W_5b8a8 = Some (Branch BC_EQ 14 15 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8ac : bv 32 := 0x0205b583.
Lemma F_5b8ac : fetch_word Asan.M.loaded_segments (0x5b8fc : word) = Some W_5b8ac.
Proof. vm_refl. Qed.
Lemma D_5b8ac : decode_any W_5b8ac = Some (Load SZ8 true 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8b0 : bv 32 := 0x02061613.
Lemma F_5b8b0 : fetch_word Asan.M.loaded_segments (0x5b900 : word) = Some W_5b8b0.
Proof. vm_refl. Qed.
Lemma D_5b8b0 : decode_any W_5b8b0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8b4 : bv 32 := 0x40c686b3.
Lemma F_5b8b4 : fetch_word Asan.M.loaded_segments (0x5b904 : word) = Some W_5b8b4.
Proof. vm_refl. Qed.
Lemma D_5b8b4 : decode_any W_5b8b4 = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8b8 : bv 32 := 0x02071613.
Lemma F_5b8b8 : fetch_word Asan.M.loaded_segments (0x5b908 : word) = Some W_5b8b8.
Proof. vm_refl. Qed.
Lemma D_5b8b8 : decode_any W_5b8b8 = Some (ShiftImm ALU_SLL 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8bc : bv 32 := 0x00170713.
Lemma F_5b8bc : fetch_word Asan.M.loaded_segments (0x5b90c : word) = Some W_5b8bc.
Proof. vm_refl. Qed.
Lemma D_5b8bc : decode_any W_5b8bc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8c0 : bv 32 := 0x40b686b3.
Lemma F_5b8c0 : fetch_word Asan.M.loaded_segments (0x5b910 : word) = Some W_5b8c0.
Proof. vm_refl. Qed.
Lemma D_5b8c0 : decode_any W_5b8c0 = Some (Op ALU_SUB 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8c4 : bv 32 := 0x00843583.
Lemma F_5b8c4 : fetch_word Asan.M.loaded_segments (0x5b914 : word) = Some W_5b8c4.
Proof. vm_refl. Qed.
Lemma D_5b8c4 : decode_any W_5b8c4 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8c8 : bv 32 := 0x7ff50513.
Lemma F_5b8c8 : fetch_word Asan.M.loaded_segments (0x5b918 : word) = Some W_5b8c8.
Proof. vm_refl. Qed.
Lemma D_5b8c8 : decode_any W_5b8c8 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8cc : bv 32 := 0x01e65613.
Lemma F_5b8cc : fetch_word Asan.M.loaded_segments (0x5b91c : word) = Some W_5b8cc.
Proof. vm_refl. Qed.
Lemma D_5b8cc : decode_any W_5b8cc = Some (ShiftImm ALU_SRL 12 12 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8d0 : bv 32 := 0x21150513.
Lemma F_5b8d0 : fetch_word Asan.M.loaded_segments (0x5b920 : word) = Some W_5b8d0.
Proof. vm_refl. Qed.
Lemma D_5b8d0 : decode_any W_5b8d0 = Some (OpImm ALU_ADD 10 10 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8d4 : bv 32 := 0x00c40633.
Lemma F_5b8d4 : fetch_word Asan.M.loaded_segments (0x5b924 : word) = Some W_5b8d4.
Proof. vm_refl. Qed.
Lemma D_5b8d4 : decode_any W_5b8d4 = Some (Op ALU_ADD 12 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8d8 : bv 32 := 0x0046d693.
Lemma F_5b8d8 : fetch_word Asan.M.loaded_segments (0x5b928 : word) = Some W_5b8d8.
Proof. vm_refl. Qed.
Lemma D_5b8d8 : decode_any W_5b8d8 = Some (ShiftImm ALU_SRL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8dc : bv 32 := 0x00e42023.
Lemma F_5b8dc : fetch_word Asan.M.loaded_segments (0x5b92c : word) = Some W_5b8dc.
Proof. vm_refl. Qed.
Lemma D_5b8dc : decode_any W_5b8dc = Some (Store SZ4 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8e0 : bv 32 := 0x00d62823.
Lemma F_5b8e0 : fetch_word Asan.M.loaded_segments (0x5b930 : word) = Some W_5b8e0.
Proof. vm_refl. Qed.
Lemma D_5b8e0 : decode_any W_5b8e0 = Some (Store SZ4 12 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8e4 : bv 32 := 0x40b005b3.
Lemma F_5b8e4 : fetch_word Asan.M.loaded_segments (0x5b934 : word) = Some W_5b8e4.
Proof. vm_refl. Qed.
Lemma D_5b8e4 : decode_any W_5b8e4 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8e8 : bv 32 := 0x00b5302f.
Lemma F_5b8e8 : fetch_word Asan.M.loaded_segments (0x5b938 : word) = Some W_5b8e8.
Proof. vm_refl. Qed.
Lemma D_5b8e8 : decode_any W_5b8e8 = Some (Amo AMO_ADD AD false false 0 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8ec : bv 32 := 0x02813083.
Lemma F_5b8ec : fetch_word Asan.M.loaded_segments (0x5b93c : word) = Some W_5b8ec.
Proof. vm_refl. Qed.
Lemma D_5b8ec : decode_any W_5b8ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8f0 : bv 32 := 0x02013403.
Lemma F_5b8f0 : fetch_word Asan.M.loaded_segments (0x5b940 : word) = Some W_5b8f0.
Proof. vm_refl. Qed.
Lemma D_5b8f0 : decode_any W_5b8f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8f4 : bv 32 := 0x01813483.
Lemma F_5b8f4 : fetch_word Asan.M.loaded_segments (0x5b944 : word) = Some W_5b8f4.
Proof. vm_refl. Qed.
Lemma D_5b8f4 : decode_any W_5b8f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8f8 : bv 32 := 0x01013903.
Lemma F_5b8f8 : fetch_word Asan.M.loaded_segments (0x5b948 : word) = Some W_5b8f8.
Proof. vm_refl. Qed.
Lemma D_5b8f8 : decode_any W_5b8f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8fc : bv 32 := 0x00813983.
Lemma F_5b8fc : fetch_word Asan.M.loaded_segments (0x5b94c : word) = Some W_5b8fc.
Proof. vm_refl. Qed.
Lemma D_5b8fc : decode_any W_5b8fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b900 : bv 32 := 0x00013a03.
Lemma F_5b900 : fetch_word Asan.M.loaded_segments (0x5b950 : word) = Some W_5b900.
Proof. vm_refl. Qed.
Lemma D_5b900 : decode_any W_5b900 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b904 : bv 32 := 0x03010113.
Lemma F_5b904 : fetch_word Asan.M.loaded_segments (0x5b954 : word) = Some W_5b904.
Proof. vm_refl. Qed.
Lemma D_5b904 : decode_any W_5b904 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b908 : bv 32 := 0x00008067.
Lemma F_5b908 : fetch_word Asan.M.loaded_segments (0x5b958 : word) = Some W_5b908.
Proof. vm_refl. Qed.
Lemma D_5b908 : decode_any W_5b908 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f8 : bv 32 := 0x00050493.
Lemma F_5b9f8 : fetch_word Asan.M.loaded_segments (0x5ba48 : word) = Some W_5b9f8.
Proof. vm_refl. Qed.
Lemma D_5b9f8 : decode_any W_5b9f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9fc : bv 32 := 0x00058913.
Lemma F_5b9fc : fetch_word Asan.M.loaded_segments (0x5ba4c : word) = Some W_5b9fc.
Proof. vm_refl. Qed.
Lemma D_5b9fc : decode_any W_5b9fc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba00 : bv 32 := 0x00040593.
Lemma F_5ba00 : fetch_word Asan.M.loaded_segments (0x5ba50 : word) = Some W_5ba00.
Proof. vm_refl. Qed.
Lemma D_5ba00 : decode_any W_5ba00 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba04 : bv 32 := 0x00060993.
Lemma F_5ba04 : fetch_word Asan.M.loaded_segments (0x5ba54 : word) = Some W_5ba04.
Proof. vm_refl. Qed.
Lemma D_5ba04 : decode_any W_5ba04 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba08 : bv 32 := 0x00090613.
Lemma F_5ba08 : fetch_word Asan.M.loaded_segments (0x5ba58 : word) = Some W_5ba08.
Proof. vm_refl. Qed.
Lemma D_5ba08 : decode_any W_5ba08 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba0c : bv 32 := 0x00068a13.
Lemma F_5ba0c : fetch_word Asan.M.loaded_segments (0x5ba5c : word) = Some W_5ba0c.
Proof. vm_refl. Qed.
Lemma D_5ba0c : decode_any W_5ba0c = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba10 : bv 32 := 0x00098693.
Lemma F_5ba10 : fetch_word Asan.M.loaded_segments (0x5ba60 : word) = Some W_5ba10.
Proof. vm_refl. Qed.
Lemma D_5ba10 : decode_any W_5ba10 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba14 : bv 32 := 0x1e8000ef.
Lemma F_5ba14 : fetch_word Asan.M.loaded_segments (0x5ba64 : word) = Some W_5ba14.
Proof. vm_refl. Qed.
Lemma D_5ba14 : decode_any W_5ba14 = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba18 : bv 32 := 0x00090593.
Lemma F_5ba18 : fetch_word Asan.M.loaded_segments (0x5ba68 : word) = Some W_5ba18.
Proof. vm_refl. Qed.
Lemma D_5ba18 : decode_any W_5ba18 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba1c : bv 32 := 0x000a0693.
Lemma F_5ba1c : fetch_word Asan.M.loaded_segments (0x5ba6c : word) = Some W_5ba1c.
Proof. vm_refl. Qed.
Lemma D_5ba1c : decode_any W_5ba1c = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba20 : bv 32 := 0x00048513.
Lemma F_5ba20 : fetch_word Asan.M.loaded_segments (0x5ba70 : word) = Some W_5ba20.
Proof. vm_refl. Qed.
Lemma D_5ba20 : decode_any W_5ba20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba24 : bv 32 := 0x00098613.
Lemma F_5ba24 : fetch_word Asan.M.loaded_segments (0x5ba74 : word) = Some W_5ba24.
Proof. vm_refl. Qed.
Lemma D_5ba24 : decode_any W_5ba24 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba28 : bv 32 := 0x00042703.
Lemma F_5ba28 : fetch_word Asan.M.loaded_segments (0x5ba78 : word) = Some W_5ba28.
Proof. vm_refl. Qed.
Lemma D_5ba28 : decode_any W_5ba28 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba2c : bv 32 := 0xe81ff06f.
Lemma F_5ba2c : fetch_word Asan.M.loaded_segments (0x5ba7c : word) = Some W_5ba2c.
Proof. vm_refl. Qed.
Lemma D_5ba2c : decode_any W_5ba2c = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba30 : bv 32 := 0xfe010113.
Lemma F_5ba30 : fetch_word Asan.M.loaded_segments (0x5ba80 : word) = Some W_5ba30.
Proof. vm_refl. Qed.
Lemma D_5ba30 : decode_any W_5ba30 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba34 : bv 32 := 0x00113c23.
Lemma F_5ba34 : fetch_word Asan.M.loaded_segments (0x5ba84 : word) = Some W_5ba34.
Proof. vm_refl. Qed.
Lemma D_5ba34 : decode_any W_5ba34 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba38 : bv 32 := 0x00813823.
Lemma F_5ba38 : fetch_word Asan.M.loaded_segments (0x5ba88 : word) = Some W_5ba38.
Proof. vm_refl. Qed.
Lemma D_5ba38 : decode_any W_5ba38 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba3c : bv 32 := 0x00913423.
Lemma F_5ba3c : fetch_word Asan.M.loaded_segments (0x5ba8c : word) = Some W_5ba3c.
Proof. vm_refl. Qed.
Lemma D_5ba3c : decode_any W_5ba3c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba40 : bv 32 := 0x01213023.
Lemma F_5ba40 : fetch_word Asan.M.loaded_segments (0x5ba90 : word) = Some W_5ba40.
Proof. vm_refl. Qed.
Lemma D_5ba40 : decode_any W_5ba40 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba44 : bv 32 := 0x00053703.
Lemma F_5ba44 : fetch_word Asan.M.loaded_segments (0x5ba94 : word) = Some W_5ba44.
Proof. vm_refl. Qed.
Lemma D_5ba44 : decode_any W_5ba44 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba48 : bv 32 := 0xfff70693.
Lemma F_5ba48 : fetch_word Asan.M.loaded_segments (0x5ba98 : word) = Some W_5ba48.
Proof. vm_refl. Qed.
Lemma D_5ba48 : decode_any W_5ba48 = Some (OpImm ALU_ADD 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba4c : bv 32 := 0x00c6f6b3.
Lemma F_5ba4c : fetch_word Asan.M.loaded_segments (0x5ba9c : word) = Some W_5ba4c.
Proof. vm_refl. Qed.
Lemma D_5ba4c : decode_any W_5ba4c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba50 : bv 32 := 0x12069263.
Lemma F_5ba50 : fetch_word Asan.M.loaded_segments (0x5baa0 : word) = Some W_5ba50.
Proof. vm_refl. Qed.
Lemma D_5ba50 : decode_any W_5ba50 = Some (Branch BC_NE 13 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba54 : bv 32 := 0x26850693.
Lemma F_5ba54 : fetch_word Asan.M.loaded_segments (0x5baa4 : word) = Some W_5ba54.
Proof. vm_refl. Qed.
Lemma D_5ba54 : decode_any W_5ba54 = Some (OpImm ALU_ADD 13 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba58 : bv 32 := 0x0ff00793.
Lemma F_5ba58 : fetch_word Asan.M.loaded_segments (0x5baa8 : word) = Some W_5ba58.
Proof. vm_refl. Qed.
Lemma D_5ba58 : decode_any W_5ba58 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba5c : bv 32 := 0xffc6f813.
Lemma F_5ba5c : fetch_word Asan.M.loaded_segments (0x5baac : word) = Some W_5ba5c.
Proof. vm_refl. Qed.
Lemma D_5ba5c : decode_any W_5ba5c = Some (OpImm ALU_AND 16 13 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba60 : bv 32 := 0x00100893.
Lemma F_5ba60 : fetch_word Asan.M.loaded_segments (0x5bab0 : word) = Some W_5ba60.
Proof. vm_refl. Qed.
Lemma D_5ba60 : decode_any W_5ba60 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba64 : bv 32 := 0x140822af.
Lemma F_5ba64 : fetch_word Asan.M.loaded_segments (0x5bab4 : word) = Some W_5ba64.
Proof. vm_refl. Qed.
Lemma D_5ba64 : decode_any W_5ba64 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba68 : bv 32 := 0x00088313.
Lemma F_5ba68 : fetch_word Asan.M.loaded_segments (0x5bab8 : word) = Some W_5ba68.
Proof. vm_refl. Qed.
Lemma D_5ba68 : decode_any W_5ba68 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba6c : bv 32 := 0x0062c333.
Lemma F_5ba6c : fetch_word Asan.M.loaded_segments (0x5babc : word) = Some W_5ba6c.
Proof. vm_refl. Qed.
Lemma D_5ba6c : decode_any W_5ba6c = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba70 : bv 32 := 0x00f37333.
Lemma F_5ba70 : fetch_word Asan.M.loaded_segments (0x5bac0 : word) = Some W_5ba70.
Proof. vm_refl. Qed.
Lemma D_5ba70 : decode_any W_5ba70 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba74 : bv 32 := 0x0062c333.
Lemma F_5ba74 : fetch_word Asan.M.loaded_segments (0x5bac4 : word) = Some W_5ba74.
Proof. vm_refl. Qed.
Lemma D_5ba74 : decode_any W_5ba74 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba78 : bv 32 := 0x1868232f.
Lemma F_5ba78 : fetch_word Asan.M.loaded_segments (0x5bac8 : word) = Some W_5ba78.
Proof. vm_refl. Qed.
Lemma D_5ba78 : decode_any W_5ba78 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba7c : bv 32 := 0xfe0314e3.
Lemma F_5ba7c : fetch_word Asan.M.loaded_segments (0x5bacc : word) = Some W_5ba7c.
Proof. vm_refl. Qed.
Lemma D_5ba7c : decode_any W_5ba7c = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba80 : bv 32 := 0x0ff2f793.
Lemma F_5ba80 : fetch_word Asan.M.loaded_segments (0x5bad0 : word) = Some W_5ba80.
Proof. vm_refl. Qed.
Lemma D_5ba80 : decode_any W_5ba80 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba84 : bv 32 := 0x40e60433.
Lemma F_5ba84 : fetch_word Asan.M.loaded_segments (0x5bad4 : word) = Some W_5ba84.
Proof. vm_refl. Qed.
Lemma D_5ba84 : decode_any W_5ba84 = Some (Op ALU_SUB 8 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba88 : bv 32 := 0x10079663.
Lemma F_5ba88 : fetch_word Asan.M.loaded_segments (0x5bad8 : word) = Some W_5ba88.
Proof. vm_refl. Qed.
Lemma D_5ba88 : decode_any W_5ba88 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba8c : bv 32 := 0x01843683.
Lemma F_5ba8c : fetch_word Asan.M.loaded_segments (0x5badc : word) = Some W_5ba8c.
Proof. vm_refl. Qed.
Lemma D_5ba8c : decode_any W_5ba8c = Some (Load SZ8 true 13 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba90 : bv 32 := 0x00853783.
Lemma F_5ba90 : fetch_word Asan.M.loaded_segments (0x5bae0 : word) = Some W_5ba90.
Proof. vm_refl. Qed.
Lemma D_5ba90 : decode_any W_5ba90 = Some (Load SZ8 true 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba94 : bv 32 := 0x00369613.
Lemma F_5ba94 : fetch_word Asan.M.loaded_segments (0x5bae4 : word) = Some W_5ba94.
Proof. vm_refl. Qed.
Lemma D_5ba94 : decode_any W_5ba94 = Some (ShiftImm ALU_SLL 12 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba98 : bv 32 := 0x00c78633.
Lemma F_5ba98 : fetch_word Asan.M.loaded_segments (0x5bae8 : word) = Some W_5ba98.
Proof. vm_refl. Qed.
Lemma D_5ba98 : decode_any W_5ba98 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba9c : bv 32 := 0x00063703.
Lemma F_5ba9c : fetch_word Asan.M.loaded_segments (0x5baec : word) = Some W_5ba9c.
Proof. vm_refl. Qed.
Lemma D_5ba9c : decode_any W_5ba9c = Some (Load SZ8 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa0 : bv 32 := 0x12871263.
Lemma F_5baa0 : fetch_word Asan.M.loaded_segments (0x5baf0 : word) = Some W_5baa0.
Proof. vm_refl. Qed.
Lemma D_5baa0 : decode_any W_5baa0 = Some (Branch BC_NE 14 8 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa4 : bv 32 := 0x03853703.
Lemma F_5baa4 : fetch_word Asan.M.loaded_segments (0x5baf4 : word) = Some W_5baa4.
Proof. vm_refl. Qed.
Lemma D_5baa4 : decode_any W_5baa4 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa8 : bv 32 := 0x12e6fe63.
Lemma F_5baa8 : fetch_word Asan.M.loaded_segments (0x5baf8 : word) = Some W_5baa8.
Proof. vm_refl. Qed.
Lemma D_5baa8 : decode_any W_5baa8 = Some (Branch BC_GEU 13 14 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baac : bv 32 := 0x00371813.
Lemma F_5baac : fetch_word Asan.M.loaded_segments (0x5bafc : word) = Some W_5baac.
Proof. vm_refl. Qed.
Lemma D_5baac : decode_any W_5baac = Some (ShiftImm ALU_SLL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab0 : bv 32 := 0x00843883.
Lemma F_5bab0 : fetch_word Asan.M.loaded_segments (0x5bb00 : word) = Some W_5bab0.
Proof. vm_refl. Qed.
Lemma D_5bab0 : decode_any W_5bab0 = Some (Load SZ8 true 17 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab4 : bv 32 := 0x00f807b3.
Lemma F_5bab4 : fetch_word Asan.M.loaded_segments (0x5bb04 : word) = Some W_5bab4.
Proof. vm_refl. Qed.
Lemma D_5bab4 : decode_any W_5bab4 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab8 : bv 32 := 0x05053803.
Lemma F_5bab8 : fetch_word Asan.M.loaded_segments (0x5bb08 : word) = Some W_5bab8.
Proof. vm_refl. Qed.
Lemma D_5bab8 : decode_any W_5bab8 = Some (Load SZ8 true 16 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5babc : bv 32 := 0x05853283.
Lemma F_5babc : fetch_word Asan.M.loaded_segments (0x5bb0c : word) = Some W_5babc.
Proof. vm_refl. Qed.
Lemma D_5babc : decode_any W_5babc = Some (Load SZ8 true 5 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bac0 : bv 32 := 0xfff70713.
Lemma F_5bac0 : fetch_word Asan.M.loaded_segments (0x5bb10 : word) = Some W_5bac0.
Proof. vm_refl. Qed.
Lemma D_5bac0 : decode_any W_5bac0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bac4 : bv 32 := 0xff87b783.
Lemma F_5bac4 : fetch_word Asan.M.loaded_segments (0x5bb14 : word) = Some W_5bac4.
Proof. vm_refl. Qed.
Lemma D_5bac4 : decode_any W_5bac4 = Some (Load SZ8 true 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bac8 : bv 32 := 0x00180813.
Lemma F_5bac8 : fetch_word Asan.M.loaded_segments (0x5bb18 : word) = Some W_5bac8.
Proof. vm_refl. Qed.
Lemma D_5bac8 : decode_any W_5bac8 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bacc : bv 32 := 0x411282b3.
Lemma F_5bacc : fetch_word Asan.M.loaded_segments (0x5bb1c : word) = Some W_5bacc.
Proof. vm_refl. Qed.
Lemma D_5bacc : decode_any W_5bacc = Some (Op ALU_SUB 5 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bad0 : bv 32 := 0x02e53c23.
Lemma F_5bad0 : fetch_word Asan.M.loaded_segments (0x5bb20 : word) = Some W_5bad0.
Proof. vm_refl. Qed.
Lemma D_5bad0 : decode_any W_5bad0 = Some (Store SZ8 10 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bad4 : bv 32 := 0x04050023.
Lemma F_5bad4 : fetch_word Asan.M.loaded_segments (0x5bb24 : word) = Some W_5bad4.
Proof. vm_refl. Qed.
Lemma D_5bad4 : decode_any W_5bad4 = Some (Store SZ1 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bad8 : bv 32 := 0x05053823.
Lemma F_5bad8 : fetch_word Asan.M.loaded_segments (0x5bb28 : word) = Some W_5bad8.
Proof. vm_refl. Qed.
Lemma D_5bad8 : decode_any W_5bad8 = Some (Store SZ8 10 16 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5badc : bv 32 := 0x04553c23.
Lemma F_5badc : fetch_word Asan.M.loaded_segments (0x5bb2c : word) = Some W_5badc.
Proof. vm_refl. Qed.
Lemma D_5badc : decode_any W_5badc = Some (Store SZ8 10 5 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bae0 : bv 32 := 0x01058713.
Lemma F_5bae0 : fetch_word Asan.M.loaded_segments (0x5bb30 : word) = Some W_5bae0.
Proof. vm_refl. Qed.
Lemma D_5bae0 : decode_any W_5bae0 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bae4 : bv 32 := 0x41100833.
Lemma F_5bae4 : fetch_word Asan.M.loaded_segments (0x5bb34 : word) = Some W_5bae4.
Proof. vm_refl. Qed.
Lemma D_5bae4 : decode_any W_5bae4 = Some (Op ALU_SUB 16 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bae8 : bv 32 := 0x00f63023.
Lemma F_5bae8 : fetch_word Asan.M.loaded_segments (0x5bb38 : word) = Some W_5bae8.
Proof. vm_refl. Qed.
Lemma D_5bae8 : decode_any W_5bae8 = Some (Store SZ8 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baec : bv 32 := 0x00d7bc23.
Lemma F_5baec : fetch_word Asan.M.loaded_segments (0x5bb3c : word) = Some W_5baec.
Proof. vm_refl. Qed.
Lemma D_5baec : decode_any W_5baec = Some (Store SZ8 15 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baf0 : bv 32 := 0x0107302f.
Lemma F_5baf0 : fetch_word Asan.M.loaded_segments (0x5bb40 : word) = Some W_5baf0.
Proof. vm_refl. Qed.
Lemma D_5baf0 : decode_any W_5baf0 = Some (Amo AMO_ADD AD false false 0 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baf4 : bv 32 := 0x00843603.
Lemma F_5baf4 : fetch_word Asan.M.loaded_segments (0x5bb44 : word) = Some W_5baf4.
Proof. vm_refl. Qed.
Lemma D_5baf4 : decode_any W_5baf4 = Some (Load SZ8 true 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baf8 : bv 32 := 0x01858593.
Lemma F_5baf8 : fetch_word Asan.M.loaded_segments (0x5bb48 : word) = Some W_5baf8.
Proof. vm_refl. Qed.
Lemma D_5baf8 : decode_any W_5baf8 = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bafc : bv 32 := 0x40c00633.
Lemma F_5bafc : fetch_word Asan.M.loaded_segments (0x5bb4c : word) = Some W_5bafc.
Proof. vm_refl. Qed.
Lemma D_5bafc : decode_any W_5bafc = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb00 : bv 32 := 0x00c5b02f.
Lemma F_5bb00 : fetch_word Asan.M.loaded_segments (0x5bb50 : word) = Some W_5bb00.
Proof. vm_refl. Qed.
Lemma D_5bb00 : decode_any W_5bb00 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb04 : bv 32 := 0x0310000f.
Lemma F_5bb04 : fetch_word Asan.M.loaded_segments (0x5bb54 : word) = Some W_5bb04.
Proof. vm_refl. Qed.
Lemma D_5bb04 : decode_any W_5bb04 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb08 : bv 32 := 0x26050423.
Lemma F_5bb08 : fetch_word Asan.M.loaded_segments (0x5bb58 : word) = Some W_5bb08.
Proof. vm_refl. Qed.
Lemma D_5bb08 : decode_any W_5bb08 = Some (Store SZ1 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb0c : bv 32 := 0x00043483.
Lemma F_5bb0c : fetch_word Asan.M.loaded_segments (0x5bb5c : word) = Some W_5bb0c.
Proof. vm_refl. Qed.
Lemma D_5bb0c : decode_any W_5bb0c = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb10 : bv 32 := 0x00843903.
Lemma F_5bb10 : fetch_word Asan.M.loaded_segments (0x5bb60 : word) = Some W_5bb10.
Proof. vm_refl. Qed.
Lemma D_5bb10 : decode_any W_5bb10 = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb14 : bv 32 := 0x00048513.
Lemma F_5bb14 : fetch_word Asan.M.loaded_segments (0x5bb64 : word) = Some W_5bb14.
Proof. vm_refl. Qed.
Lemma D_5bb14 : decode_any W_5bb14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb18 : bv 32 := 0x00090593.
Lemma F_5bb18 : fetch_word Asan.M.loaded_segments (0x5bb68 : word) = Some W_5bb18.
Proof. vm_refl. Qed.
Lemma D_5bb18 : decode_any W_5bb18 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb1c : bv 32 := 0x00000613.
Lemma F_5bb1c : fetch_word Asan.M.loaded_segments (0x5bb6c : word) = Some W_5bb1c.
Proof. vm_refl. Qed.
Lemma D_5bb1c : decode_any W_5bb1c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb20 : bv 32 := 0x6f1250ef.
Lemma F_5bb20 : fetch_word Asan.M.loaded_segments (0x5bb70 : word) = Some W_5bb20.
Proof. vm_refl. Qed.
Lemma D_5bb20 : decode_any W_5bb20 = Some (Jal 1 155376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb24 : bv 32 := 0x00048513.
Lemma F_5bb24 : fetch_word Asan.M.loaded_segments (0x5bb74 : word) = Some W_5bb24.
Proof. vm_refl. Qed.
Lemma D_5bb24 : decode_any W_5bb24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb28 : bv 32 := 0x00090593.
Lemma F_5bb28 : fetch_word Asan.M.loaded_segments (0x5bb78 : word) = Some W_5bb28.
Proof. vm_refl. Qed.
Lemma D_5bb28 : decode_any W_5bb28 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb2c : bv 32 := 0x0cd240ef.
Lemma F_5bb2c : fetch_word Asan.M.loaded_segments (0x5bb7c : word) = Some W_5bb2c.
Proof. vm_refl. Qed.
Lemma D_5bb2c : decode_any W_5bb2c = Some (Jal 1 149708, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb30 : bv 32 := 0x6592d0ef.
Lemma F_5bb30 : fetch_word Asan.M.loaded_segments (0x5bb80 : word) = Some W_5bb30.
Proof. vm_refl. Qed.
Lemma D_5bb30 : decode_any W_5bb30 = Some (Jal 1 187992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb34 : bv 32 := 0x06053683.
Lemma F_5bb34 : fetch_word Asan.M.loaded_segments (0x5bb84 : word) = Some W_5bb34.
Proof. vm_refl. Qed.
Lemma D_5bb34 : decode_any W_5bb34 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb38 : bv 32 := 0x05853703.
Lemma F_5bb38 : fetch_word Asan.M.loaded_segments (0x5bb88 : word) = Some W_5bb38.
Proof. vm_refl. Qed.
Lemma D_5bb38 : decode_any W_5bb38 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb3c : bv 32 := 0x00043603.
Lemma F_5bb3c : fetch_word Asan.M.loaded_segments (0x5bb8c : word) = Some W_5bb3c.
Proof. vm_refl. Qed.
Lemma D_5bb3c : decode_any W_5bb3c = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb40 : bv 32 := 0x00843583.
Lemma F_5bb40 : fetch_word Asan.M.loaded_segments (0x5bb90 : word) = Some W_5bb40.
Proof. vm_refl. Qed.
Lemma D_5bb40 : decode_any W_5bb40 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb44 : bv 32 := 0x012686b3.
Lemma F_5bb44 : fetch_word Asan.M.loaded_segments (0x5bb94 : word) = Some W_5bb44.
Proof. vm_refl. Qed.
Lemma D_5bb44 : decode_any W_5bb44 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb48 : bv 32 := 0x00170713.
Lemma F_5bb48 : fetch_word Asan.M.loaded_segments (0x5bb98 : word) = Some W_5bb48.
Proof. vm_refl. Qed.
Lemma D_5bb48 : decode_any W_5bb48 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb4c : bv 32 := 0x04e53c23.
Lemma F_5bb4c : fetch_word Asan.M.loaded_segments (0x5bb9c : word) = Some W_5bb4c.
Proof. vm_refl. Qed.
Lemma D_5bb4c : decode_any W_5bb4c = Some (Store SZ8 10 14 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb50 : bv 32 := 0x06d53023.
Lemma F_5bb50 : fetch_word Asan.M.loaded_segments (0x5bba0 : word) = Some W_5bb50.
Proof. vm_refl. Qed.
Lemma D_5bb50 : decode_any W_5bb50 = Some (Store SZ8 10 13 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb54 : bv 32 := 0x00060513.
Lemma F_5bb54 : fetch_word Asan.M.loaded_segments (0x5bba4 : word) = Some W_5bb54.
Proof. vm_refl. Qed.
Lemma D_5bb54 : decode_any W_5bb54 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb58 : bv 32 := 0x00000613.
Lemma F_5bb58 : fetch_word Asan.M.loaded_segments (0x5bba8 : word) = Some W_5bb58.
Proof. vm_refl. Qed.
Lemma D_5bb58 : decode_any W_5bb58 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb5c : bv 32 := 0x01813083.
Lemma F_5bb5c : fetch_word Asan.M.loaded_segments (0x5bbac : word) = Some W_5bb5c.
Proof. vm_refl. Qed.
Lemma D_5bb5c : decode_any W_5bb5c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb60 : bv 32 := 0x01013403.
Lemma F_5bb60 : fetch_word Asan.M.loaded_segments (0x5bbb0 : word) = Some W_5bb60.
Proof. vm_refl. Qed.
Lemma D_5bb60 : decode_any W_5bb60 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb64 : bv 32 := 0x00813483.
Lemma F_5bb64 : fetch_word Asan.M.loaded_segments (0x5bbb4 : word) = Some W_5bb64.
Proof. vm_refl. Qed.
Lemma D_5bb64 : decode_any W_5bb64 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb68 : bv 32 := 0x00013903.
Lemma F_5bb68 : fetch_word Asan.M.loaded_segments (0x5bbb8 : word) = Some W_5bb68.
Proof. vm_refl. Qed.
Lemma D_5bb68 : decode_any W_5bb68 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb6c : bv 32 := 0x02010113.
Lemma F_5bb6c : fetch_word Asan.M.loaded_segments (0x5bbbc : word) = Some W_5bb6c.
Proof. vm_refl. Qed.
Lemma D_5bb6c : decode_any W_5bb6c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb70 : bv 32 := 0x0353806f.
Lemma F_5bb70 : fetch_word Asan.M.loaded_segments (0x5bbc0 : word) = Some W_5bb70.
Proof. vm_refl. Qed.
Lemma D_5bb70 : decode_any W_5bb70 = Some (Jal 0 231476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbfc : bv 32 := 0xfc010113.
Lemma F_5bbfc : fetch_word Asan.M.loaded_segments (0x5bc4c : word) = Some W_5bbfc.
Proof. vm_refl. Qed.
Lemma D_5bbfc : decode_any W_5bbfc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc00 : bv 32 := 0x02113c23.
Lemma F_5bc00 : fetch_word Asan.M.loaded_segments (0x5bc50 : word) = Some W_5bc00.
Proof. vm_refl. Qed.
Lemma D_5bc00 : decode_any W_5bc00 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc04 : bv 32 := 0x02013423.
Lemma F_5bc04 : fetch_word Asan.M.loaded_segments (0x5bc54 : word) = Some W_5bc04.
Proof. vm_refl. Qed.
Lemma D_5bc04 : decode_any W_5bc04 = Some (Store SZ8 2 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc08 : bv 32 := 0x02013823.
Lemma F_5bc08 : fetch_word Asan.M.loaded_segments (0x5bc58 : word) = Some W_5bc08.
Proof. vm_refl. Qed.
Lemma D_5bc08 : decode_any W_5bc08 = Some (Store SZ8 2 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc0c : bv 32 := 0x0005a803.
Lemma F_5bc0c : fetch_word Asan.M.loaded_segments (0x5bc5c : word) = Some W_5bc0c.
Proof. vm_refl. Qed.
Lemma D_5bc0c : decode_any W_5bc0c = Some (Load SZ4 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc10 : bv 32 := 0x0045e783.
Lemma F_5bc10 : fetch_word Asan.M.loaded_segments (0x5bc60 : word) = Some W_5bc10.
Proof. vm_refl. Qed.
Lemma D_5bc10 : decode_any W_5bc10 = Some (Load SZ4 false 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc14 : bv 32 := 0x00c13423.
Lemma F_5bc14 : fetch_word Asan.M.loaded_segments (0x5bc64 : word) = Some W_5bc14.
Proof. vm_refl. Qed.
Lemma D_5bc14 : decode_any W_5bc14 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc18 : bv 32 := 0x00013823.
Lemma F_5bc18 : fetch_word Asan.M.loaded_segments (0x5bc68 : word) = Some W_5bc18.
Proof. vm_refl. Qed.
Lemma D_5bc18 : decode_any W_5bc18 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc1c : bv 32 := 0x00013c23.
Lemma F_5bc1c : fetch_word Asan.M.loaded_segments (0x5bc6c : word) = Some W_5bc1c.
Proof. vm_refl. Qed.
Lemma D_5bc1c : decode_any W_5bc1c = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc20 : bv 32 := 0x02013023.
Lemma F_5bc20 : fetch_word Asan.M.loaded_segments (0x5bc70 : word) = Some W_5bc20.
Proof. vm_refl. Qed.
Lemma D_5bc20 : decode_any W_5bc20 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc24 : bv 32 := 0x0017d793.
Lemma F_5bc24 : fetch_word Asan.M.loaded_segments (0x5bc74 : word) = Some W_5bc24.
Proof. vm_refl. Qed.
Lemma D_5bc24 : decode_any W_5bc24 = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc28 : bv 32 := 0x02081713.
Lemma F_5bc28 : fetch_word Asan.M.loaded_segments (0x5bc78 : word) = Some W_5bc28.
Proof. vm_refl. Qed.
Lemma D_5bc28 : decode_any W_5bc28 = Some (ShiftImm ALU_SLL 14 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc2c : bv 32 := 0x02075713.
Lemma F_5bc2c : fetch_word Asan.M.loaded_segments (0x5bc7c : word) = Some W_5bc2c.
Proof. vm_refl. Qed.
Lemma D_5bc2c : decode_any W_5bc2c = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc30 : bv 32 := 0x04f86663.
Lemma F_5bc30 : fetch_word Asan.M.loaded_segments (0x5bc80 : word) = Some W_5bc30.
Proof. vm_refl. Qed.
Lemma D_5bc30 : decode_any W_5bc30 = Some (Branch BC_LTU 16 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc34 : bv 32 := 0x40f70733.
Lemma F_5bc34 : fetch_word Asan.M.loaded_segments (0x5bc84 : word) = Some W_5bc34.
Proof. vm_refl. Qed.
Lemma D_5bc34 : decode_any W_5bc34 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc38 : bv 32 := 0x7ff50513.
Lemma F_5bc38 : fetch_word Asan.M.loaded_segments (0x5bc88 : word) = Some W_5bc38.
Proof. vm_refl. Qed.
Lemma D_5bc38 : decode_any W_5bc38 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc3c : bv 32 := 0x00e5a023.
Lemma F_5bc3c : fetch_word Asan.M.loaded_segments (0x5bc8c : word) = Some W_5bc3c.
Proof. vm_refl. Qed.
Lemma D_5bc3c : decode_any W_5bc3c = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc40 : bv 32 := 0x20150813.
Lemma F_5bc40 : fetch_word Asan.M.loaded_segments (0x5bc90 : word) = Some W_5bc40.
Proof. vm_refl. Qed.
Lemma D_5bc40 : decode_any W_5bc40 = Some (OpImm ALU_ADD 16 10 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc44 : bv 32 := 0x00271713.
Lemma F_5bc44 : fetch_word Asan.M.loaded_segments (0x5bc94 : word) = Some W_5bc44.
Proof. vm_refl. Qed.
Lemma D_5bc44 : decode_any W_5bc44 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc48 : bv 32 := 0x00e585b3.
Lemma F_5bc48 : fetch_word Asan.M.loaded_segments (0x5bc98 : word) = Some W_5bc48.
Proof. vm_refl. Qed.
Lemma D_5bc48 : decode_any W_5bc48 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc4c : bv 32 := 0x01058713.
Lemma F_5bc4c : fetch_word Asan.M.loaded_segments (0x5bc9c : word) = Some W_5bc4c.
Proof. vm_refl. Qed.
Lemma D_5bc4c : decode_any W_5bc4c = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc50 : bv 32 := 0x00810593.
Lemma F_5bc50 : fetch_word Asan.M.loaded_segments (0x5bca0 : word) = Some W_5bc50.
Proof. vm_refl. Qed.
Lemma D_5bc50 : decode_any W_5bc50 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc54 : bv 32 := 0x00060513.
Lemma F_5bc54 : fetch_word Asan.M.loaded_segments (0x5bca4 : word) = Some W_5bc54.
Proof. vm_refl. Qed.
Lemma D_5bc54 : decode_any W_5bc54 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc58 : bv 32 := 0x00080613.
Lemma F_5bc58 : fetch_word Asan.M.loaded_segments (0x5bca8 : word) = Some W_5bc58.
Proof. vm_refl. Qed.
Lemma D_5bc58 : decode_any W_5bc58 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc5c : bv 32 := 0x144000ef.
Lemma F_5bc5c : fetch_word Asan.M.loaded_segments (0x5bcac : word) = Some W_5bc5c.
Proof. vm_refl. Qed.
Lemma D_5bc5c : decode_any W_5bc5c = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc60 : bv 32 := 0x02013503.
Lemma F_5bc60 : fetch_word Asan.M.loaded_segments (0x5bcb0 : word) = Some W_5bc60.
Proof. vm_refl. Qed.
Lemma D_5bc60 : decode_any W_5bc60 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc64 : bv 32 := 0x02813583.
Lemma F_5bc64 : fetch_word Asan.M.loaded_segments (0x5bcb4 : word) = Some W_5bc64.
Proof. vm_refl. Qed.
Lemma D_5bc64 : decode_any W_5bc64 = Some (Load SZ8 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc68 : bv 32 := 0x00000613.
Lemma F_5bc68 : fetch_word Asan.M.loaded_segments (0x5bcb8 : word) = Some W_5bc68.
Proof. vm_refl. Qed.
Lemma D_5bc68 : decode_any W_5bc68 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc6c : bv 32 := 0x738380ef.
Lemma F_5bc6c : fetch_word Asan.M.loaded_segments (0x5bcbc : word) = Some W_5bc6c.
Proof. vm_refl. Qed.
Lemma D_5bc6c : decode_any W_5bc6c = Some (Jal 1 231224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc70 : bv 32 := 0x03813083.
Lemma F_5bc70 : fetch_word Asan.M.loaded_segments (0x5bcc0 : word) = Some W_5bc70.
Proof. vm_refl. Qed.
Lemma D_5bc70 : decode_any W_5bc70 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc74 : bv 32 := 0x04010113.
Lemma F_5bc74 : fetch_word Asan.M.loaded_segments (0x5bcc4 : word) = Some W_5bc74.
Proof. vm_refl. Qed.
Lemma D_5bc74 : decode_any W_5bc74 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bc78 : bv 32 := 0x00008067.
Lemma F_5bc78 : fetch_word Asan.M.loaded_segments (0x5bcc8 : word) = Some W_5bc78.
Proof. vm_refl. Qed.
Lemma D_5bc78 : decode_any W_5bc78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda0 : bv 32 := 0xf8010113.
Lemma F_5bda0 : fetch_word Asan.M.loaded_segments (0x5bdf0 : word) = Some W_5bda0.
Proof. vm_refl. Qed.
Lemma D_5bda0 : decode_any W_5bda0 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda4 : bv 32 := 0x06113c23.
Lemma F_5bda4 : fetch_word Asan.M.loaded_segments (0x5bdf4 : word) = Some W_5bda4.
Proof. vm_refl. Qed.
Lemma D_5bda4 : decode_any W_5bda4 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda8 : bv 32 := 0x06813823.
Lemma F_5bda8 : fetch_word Asan.M.loaded_segments (0x5bdf8 : word) = Some W_5bda8.
Proof. vm_refl. Qed.
Lemma D_5bda8 : decode_any W_5bda8 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdac : bv 32 := 0x06913423.
Lemma F_5bdac : fetch_word Asan.M.loaded_segments (0x5bdfc : word) = Some W_5bdac.
Proof. vm_refl. Qed.
Lemma D_5bdac : decode_any W_5bdac = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb0 : bv 32 := 0x07213023.
Lemma F_5bdb0 : fetch_word Asan.M.loaded_segments (0x5be00 : word) = Some W_5bdb0.
Proof. vm_refl. Qed.
Lemma D_5bdb0 : decode_any W_5bdb0 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb4 : bv 32 := 0x05313c23.
Lemma F_5bdb4 : fetch_word Asan.M.loaded_segments (0x5be04 : word) = Some W_5bdb4.
Proof. vm_refl. Qed.
Lemma D_5bdb4 : decode_any W_5bdb4 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb8 : bv 32 := 0x05413823.
Lemma F_5bdb8 : fetch_word Asan.M.loaded_segments (0x5be08 : word) = Some W_5bdb8.
Proof. vm_refl. Qed.
Lemma D_5bdb8 : decode_any W_5bdb8 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdbc : bv 32 := 0x05513423.
Lemma F_5bdbc : fetch_word Asan.M.loaded_segments (0x5be0c : word) = Some W_5bdbc.
Proof. vm_refl. Qed.
Lemma D_5bdbc : decode_any W_5bdbc = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc0 : bv 32 := 0x05613023.
Lemma F_5bdc0 : fetch_word Asan.M.loaded_segments (0x5be10 : word) = Some W_5bdc0.
Proof. vm_refl. Qed.
Lemma D_5bdc0 : decode_any W_5bdc0 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc4 : bv 32 := 0x03713c23.
Lemma F_5bdc4 : fetch_word Asan.M.loaded_segments (0x5be14 : word) = Some W_5bdc4.
Proof. vm_refl. Qed.
Lemma D_5bdc4 : decode_any W_5bdc4 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc8 : bv 32 := 0x03813823.
Lemma F_5bdc8 : fetch_word Asan.M.loaded_segments (0x5be18 : word) = Some W_5bdc8.
Proof. vm_refl. Qed.
Lemma D_5bdc8 : decode_any W_5bdc8 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdcc : bv 32 := 0x03913423.
Lemma F_5bdcc : fetch_word Asan.M.loaded_segments (0x5be1c : word) = Some W_5bdcc.
Proof. vm_refl. Qed.
Lemma D_5bdcc : decode_any W_5bdcc = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd0 : bv 32 := 0x03a13023.
Lemma F_5bdd0 : fetch_word Asan.M.loaded_segments (0x5be20 : word) = Some W_5bdd0.
Proof. vm_refl. Qed.
Lemma D_5bdd0 : decode_any W_5bdd0 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd4 : bv 32 := 0x01b13c23.
Lemma F_5bdd4 : fetch_word Asan.M.loaded_segments (0x5be24 : word) = Some W_5bdd4.
Proof. vm_refl. Qed.
Lemma D_5bdd4 : decode_any W_5bdd4 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd8 : bv 32 := 0x00078a93.
Lemma F_5bdd8 : fetch_word Asan.M.loaded_segments (0x5be28 : word) = Some W_5bdd8.
Proof. vm_refl. Qed.
Lemma D_5bdd8 : decode_any W_5bdd8 = Some (OpImm ALU_ADD 21 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bddc : bv 32 := 0x00070b13.
Lemma F_5bddc : fetch_word Asan.M.loaded_segments (0x5be2c : word) = Some W_5bddc.
Proof. vm_refl. Qed.
Lemma D_5bddc : decode_any W_5bddc = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde0 : bv 32 := 0x00068913.
Lemma F_5bde0 : fetch_word Asan.M.loaded_segments (0x5be30 : word) = Some W_5bde0.
Proof. vm_refl. Qed.
Lemma D_5bde0 : decode_any W_5bde0 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde4 : bv 32 := 0x00058993.
Lemma F_5bde4 : fetch_word Asan.M.loaded_segments (0x5be34 : word) = Some W_5bde4.
Proof. vm_refl. Qed.
Lemma D_5bde4 : decode_any W_5bde4 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde8 : bv 32 := 0x00050a13.
Lemma F_5bde8 : fetch_word Asan.M.loaded_segments (0x5be38 : word) = Some W_5bde8.
Proof. vm_refl. Qed.
Lemma D_5bde8 : decode_any W_5bde8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdec : bv 32 := 0x00000513.
Lemma F_5bdec : fetch_word Asan.M.loaded_segments (0x5be3c : word) = Some W_5bdec.
Proof. vm_refl. Qed.
Lemma D_5bdec : decode_any W_5bdec = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf0 : bv 32 := 0x00100d93.
Lemma F_5bdf0 : fetch_word Asan.M.loaded_segments (0x5be40 : word) = Some W_5bdf0.
Proof. vm_refl. Qed.
Lemma D_5bdf0 : decode_any W_5bdf0 = Some (OpImm ALU_ADD 27 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf4 : bv 32 := 0x020a3603.
Lemma F_5bdf4 : fetch_word Asan.M.loaded_segments (0x5be44 : word) = Some W_5bdf4.
Proof. vm_refl. Qed.
Lemma D_5bdf4 : decode_any W_5bdf4 = Some (Load SZ8 true 12 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf8 : bv 32 := 0x030a3403.
Lemma F_5bdf8 : fetch_word Asan.M.loaded_segments (0x5be48 : word) = Some W_5bdf8.
Proof. vm_refl. Qed.
Lemma D_5bdf8 : decode_any W_5bdf8 = Some (Load SZ8 true 8 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdfc : bv 32 := 0x00769693.
Lemma F_5bdfc : fetch_word Asan.M.loaded_segments (0x5be4c : word) = Some W_5bdfc.
Proof. vm_refl. Qed.
Lemma D_5bdfc : decode_any W_5bdfc = Some (ShiftImm ALU_SLL 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be00 : bv 32 := 0x02091713.
Lemma F_5be00 : fetch_word Asan.M.loaded_segments (0x5be50 : word) = Some W_5be00.
Proof. vm_refl. Qed.
Lemma D_5be00 : decode_any W_5be00 = Some (ShiftImm ALU_SLL 14 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be04 : bv 32 := 0x00700793.
Lemma F_5be04 : fetch_word Asan.M.loaded_segments (0x5be54 : word) = Some W_5be04.
Proof. vm_refl. Qed.
Lemma D_5be04 : decode_any W_5be04 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be08 : bv 32 := 0xfff00593.
Lemma F_5be08 : fetch_word Asan.M.loaded_segments (0x5be58 : word) = Some W_5be08.
Proof. vm_refl. Qed.
Lemma D_5be08 : decode_any W_5be08 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be0c : bv 32 := 0x03dd9c13.
Lemma F_5be0c : fetch_word Asan.M.loaded_segments (0x5be5c : word) = Some W_5be0c.
Proof. vm_refl. Qed.
Lemma D_5be0c : decode_any W_5be0c = Some (ShiftImm ALU_SLL 24 27 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be10 : bv 32 := 0x01d79793.
Lemma F_5be10 : fetch_word Asan.M.loaded_segments (0x5be60 : word) = Some W_5be10.
Proof. vm_refl. Qed.
Lemma D_5be10 : decode_any W_5be10 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be14 : bv 32 := 0x028d9b93.
Lemma F_5be14 : fetch_word Asan.M.loaded_segments (0x5be64 : word) = Some W_5be14.
Proof. vm_refl. Qed.
Lemma D_5be14 : decode_any W_5be14 = Some (ShiftImm ALU_SLL 23 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be18 : bv 32 := 0x001b8813.
Lemma F_5be18 : fetch_word Asan.M.loaded_segments (0x5be68 : word) = Some W_5be18.
Proof. vm_refl. Qed.
Lemma D_5be18 : decode_any W_5be18 = Some (OpImm ALU_ADD 16 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be1c : bv 32 := 0x01481813.
Lemma F_5be1c : fetch_word Asan.M.loaded_segments (0x5be6c : word) = Some W_5be1c.
Proof. vm_refl. Qed.
Lemma D_5be1c : decode_any W_5be1c = Some (ShiftImm ALU_SLL 16 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be20 : bv 32 := 0x00d40433.
Lemma F_5be20 : fetch_word Asan.M.loaded_segments (0x5be70 : word) = Some W_5be20.
Proof. vm_refl. Qed.
Lemma D_5be20 : decode_any W_5be20 = Some (Op ALU_ADD 8 8 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be24 : bv 32 := 0x00e60633.
Lemma F_5be24 : fetch_word Asan.M.loaded_segments (0x5be74 : word) = Some W_5be24.
Proof. vm_refl. Qed.
Lemma D_5be24 : decode_any W_5be24 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be28 : bv 32 := 0xfff80d13.
Lemma F_5be28 : fetch_word Asan.M.loaded_segments (0x5be78 : word) = Some W_5be28.
Proof. vm_refl. Qed.
Lemma D_5be28 : decode_any W_5be28 = Some (OpImm ALU_ADD 26 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be2c : bv 32 := 0x00f60cb3.
Lemma F_5be2c : fetch_word Asan.M.loaded_segments (0x5be7c : word) = Some W_5be2c.
Proof. vm_refl. Qed.
Lemma D_5be2c : decode_any W_5be2c = Some (Op ALU_ADD 25 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be30 : bv 32 := 0x00043683.
Lemma F_5be30 : fetch_word Asan.M.loaded_segments (0x5be80 : word) = Some W_5be30.
Proof. vm_refl. Qed.
Lemma D_5be30 : decode_any W_5be30 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be34 : bv 32 := 0x00840713.
Lemma F_5be34 : fetch_word Asan.M.loaded_segments (0x5be84 : word) = Some W_5be34.
Proof. vm_refl. Qed.
Lemma D_5be34 : decode_any W_5be34 = Some (OpImm ALU_ADD 14 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be38 : bv 32 := 0x00e13823.
Lemma F_5be38 : fetch_word Asan.M.loaded_segments (0x5be88 : word) = Some W_5be38.
Proof. vm_refl. Qed.
Lemma D_5be38 : decode_any W_5be38 = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be3c : bv 32 := 0x03cd9d93.
Lemma F_5be3c : fetch_word Asan.M.loaded_segments (0x5be8c : word) = Some W_5be3c.
Proof. vm_refl. Qed.
Lemma D_5be3c : decode_any W_5be3c = Some (ShiftImm ALU_SLL 27 27 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be40 : bv 32 := 0x5dc00893.
Lemma F_5be40 : fetch_word Asan.M.loaded_segments (0x5be90 : word) = Some W_5be40.
Proof. vm_refl. Qed.
Lemma D_5be40 : decode_any W_5be40 = Some (OpImm ALU_ADD 17 0 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be44 : bv 32 := 0x03d59493.
Lemma F_5be44 : fetch_word Asan.M.loaded_segments (0x5be94 : word) = Some W_5be44.
Proof. vm_refl. Qed.
Lemma D_5be44 : decode_any W_5be44 = Some (ShiftImm ALU_SLL 9 11 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be48 : bv 32 := 0xfff48493.
Lemma F_5be48 : fetch_word Asan.M.loaded_segments (0x5be98 : word) = Some W_5be48.
Proof. vm_refl. Qed.
Lemma D_5be48 : decode_any W_5be48 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be4c : bv 32 := 0x01a6f733.
Lemma F_5be4c : fetch_word Asan.M.loaded_segments (0x5be9c : word) = Some W_5be4c.
Proof. vm_refl. Qed.
Lemma D_5be4c : decode_any W_5be4c = Some (Op ALU_AND 14 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be50 : bv 32 := 0x02071663.
Lemma F_5be50 : fetch_word Asan.M.loaded_segments (0x5bea0 : word) = Some W_5be50.
Proof. vm_refl. Qed.
Lemma D_5be50 : decode_any W_5be50 = Some (Branch BC_NE 14 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be54 : bv 32 := 0x01b6e733.
Lemma F_5be54 : fetch_word Asan.M.loaded_segments (0x5bea4 : word) = Some W_5be54.
Proof. vm_refl. Qed.
Lemma D_5be54 : decode_any W_5be54 = Some (Op ALU_OR 14 13 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be58 : bv 32 := 0x00e5f7b3.
Lemma F_5be58 : fetch_word Asan.M.loaded_segments (0x5bea8 : word) = Some W_5be58.
Proof. vm_refl. Qed.
Lemma D_5be58 : decode_any W_5be58 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be5c : bv 32 := 0x1604372f.
Lemma F_5be5c : fetch_word Asan.M.loaded_segments (0x5beac : word) = Some W_5be5c.
Proof. vm_refl. Qed.
Lemma D_5be5c : decode_any W_5be5c = Some (Lr AD true true 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be60 : bv 32 := 0x00d71663.
Lemma F_5be60 : fetch_word Asan.M.loaded_segments (0x5beb0 : word) = Some W_5be60.
Proof. vm_refl. Qed.
Lemma D_5be60 : decode_any W_5be60 = Some (Branch BC_NE 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be64 : bv 32 := 0x1af4382f.
Lemma F_5be64 : fetch_word Asan.M.loaded_segments (0x5beb4 : word) = Some W_5be64.
Proof. vm_refl. Qed.
Lemma D_5be64 : decode_any W_5be64 = Some (Sc AD false true 16 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be68 : bv 32 := 0xfe081ae3.
Lemma F_5be68 : fetch_word Asan.M.loaded_segments (0x5beb8 : word) = Some W_5be68.
Proof. vm_refl. Qed.
Lemma D_5be68 : decode_any W_5be68 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be6c : bv 32 := 0x08d70063.
Lemma F_5be6c : fetch_word Asan.M.loaded_segments (0x5bebc : word) = Some W_5be6c.
Proof. vm_refl. Qed.
Lemma D_5be6c : decode_any W_5be6c = Some (Branch BC_EQ 14 13 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5beec : bv 32 := 0x01043483.
Lemma F_5beec : fetch_word Asan.M.loaded_segments (0x5bf3c : word) = Some W_5beec.
Proof. vm_refl. Qed.
Lemma D_5beec : decode_any W_5beec = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef0 : bv 32 := 0x01548bb3.
Lemma F_5bef0 : fetch_word Asan.M.loaded_segments (0x5bf40 : word) = Some W_5bef0.
Proof. vm_refl. Qed.
Lemma D_5bef0 : decode_any W_5bef0 = Some (Op ALU_ADD 23 9 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef4 : bv 32 := 0x000a0513.
Lemma F_5bef4 : fetch_word Asan.M.loaded_segments (0x5bf44 : word) = Some W_5bef4.
Proof. vm_refl. Qed.
Lemma D_5bef4 : decode_any W_5bef4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef8 : bv 32 := 0x00040593.
Lemma F_5bef8 : fetch_word Asan.M.loaded_segments (0x5bf48 : word) = Some W_5bef8.
Proof. vm_refl. Qed.
Lemma D_5bef8 : decode_any W_5bef8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5befc : bv 32 := 0x000b8693.
Lemma F_5befc : fetch_word Asan.M.loaded_segments (0x5bf4c : word) = Some W_5befc.
Proof. vm_refl. Qed.
Lemma D_5befc : decode_any W_5befc = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf00 : bv 32 := 0x1c8000ef.
Lemma F_5bf00 : fetch_word Asan.M.loaded_segments (0x5bf50 : word) = Some W_5bf00.
Proof. vm_refl. Qed.
Lemma D_5bf00 : decode_any W_5bf00 = Some (Jal 1 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf04 : bv 32 := 0x18050463.
Lemma F_5bf04 : fetch_word Asan.M.loaded_segments (0x5bf54 : word) = Some W_5bf04.
Proof. vm_refl. Qed.
Lemma D_5bf04 : decode_any W_5bf04 = Some (Branch BC_EQ 10 0 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf08 : bv 32 := 0x020a8463.
Lemma F_5bf08 : fetch_word Asan.M.loaded_segments (0x5bf58 : word) = Some W_5bf08.
Proof. vm_refl. Qed.
Lemma D_5bf08 : decode_any W_5bf08 = Some (Branch BC_EQ 21 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf0c : bv 32 := 0x00249493.
Lemma F_5bf0c : fetch_word Asan.M.loaded_segments (0x5bf5c : word) = Some W_5bf0c.
Proof. vm_refl. Qed.
Lemma D_5bf0c : decode_any W_5bf0c = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf10 : bv 32 := 0x009c8cb3.
Lemma F_5bf10 : fetch_word Asan.M.loaded_segments (0x5bf60 : word) = Some W_5bf10.
Proof. vm_refl. Qed.
Lemma D_5bf10 : decode_any W_5bf10 = Some (Op ALU_ADD 25 25 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf14 : bv 32 := 0x002a9513.
Lemma F_5bf14 : fetch_word Asan.M.loaded_segments (0x5bf64 : word) = Some W_5bf14.
Proof. vm_refl. Qed.
Lemma D_5bf14 : decode_any W_5bf14 = Some (ShiftImm ALU_SLL 10 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf18 : bv 32 := 0x00ab0533.
Lemma F_5bf18 : fetch_word Asan.M.loaded_segments (0x5bf68 : word) = Some W_5bf18.
Proof. vm_refl. Qed.
Lemma D_5bf18 : decode_any W_5bf18 = Some (Op ALU_ADD 10 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf1c : bv 32 := 0x000b2583.
Lemma F_5bf1c : fetch_word Asan.M.loaded_segments (0x5bf6c : word) = Some W_5bf1c.
Proof. vm_refl. Qed.
Lemma D_5bf1c : decode_any W_5bf1c = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf20 : bv 32 := 0x004b0b13.
Lemma F_5bf20 : fetch_word Asan.M.loaded_segments (0x5bf70 : word) = Some W_5bf20.
Proof. vm_refl. Qed.
Lemma D_5bf20 : decode_any W_5bf20 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf24 : bv 32 := 0x00bca023.
Lemma F_5bf24 : fetch_word Asan.M.loaded_segments (0x5bf74 : word) = Some W_5bf24.
Proof. vm_refl. Qed.
Lemma D_5bf24 : decode_any W_5bf24 = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf28 : bv 32 := 0x004c8c93.
Lemma F_5bf28 : fetch_word Asan.M.loaded_segments (0x5bf78 : word) = Some W_5bf28.
Proof. vm_refl. Qed.
Lemma D_5bf28 : decode_any W_5bf28 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf2c : bv 32 := 0xfeab18e3.
Lemma F_5bf2c : fetch_word Asan.M.loaded_segments (0x5bf7c : word) = Some W_5bf2c.
Proof. vm_refl. Qed.
Lemma D_5bf2c : decode_any W_5bf2c = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf30 : bv 32 := 0x05043503.
Lemma F_5bf30 : fetch_word Asan.M.loaded_segments (0x5bf80 : word) = Some W_5bf30.
Proof. vm_refl. Qed.
Lemma D_5bf30 : decode_any W_5bf30 = Some (Load SZ8 true 10 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf34 : bv 32 := 0x01743823.
Lemma F_5bf34 : fetch_word Asan.M.loaded_segments (0x5bf84 : word) = Some W_5bf34.
Proof. vm_refl. Qed.
Lemma D_5bf34 : decode_any W_5bf34 = Some (Store SZ8 8 23 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf38 : bv 32 := 0x01550533.
Lemma F_5bf38 : fetch_word Asan.M.loaded_segments (0x5bf88 : word) = Some W_5bf38.
Proof. vm_refl. Qed.
Lemma D_5bf38 : decode_any W_5bf38 = Some (Op ALU_ADD 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf3c : bv 32 := 0x04a43823.
Lemma F_5bf3c : fetch_word Asan.M.loaded_segments (0x5bf8c : word) = Some W_5bf3c.
Proof. vm_refl. Qed.
Lemma D_5bf3c : decode_any W_5bf3c = Some (Store SZ8 8 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf40 : bv 32 := 0x000a0513.
Lemma F_5bf40 : fetch_word Asan.M.loaded_segments (0x5bf90 : word) = Some W_5bf40.
Proof. vm_refl. Qed.
Lemma D_5bf40 : decode_any W_5bf40 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf44 : bv 32 := 0x00098593.
Lemma F_5bf44 : fetch_word Asan.M.loaded_segments (0x5bf94 : word) = Some W_5bf44.
Proof. vm_refl. Qed.
Lemma D_5bf44 : decode_any W_5bf44 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf48 : bv 32 := 0x00090613.
Lemma F_5bf48 : fetch_word Asan.M.loaded_segments (0x5bf98 : word) = Some W_5bf48.
Proof. vm_refl. Qed.
Lemma D_5bf48 : decode_any W_5bf48 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf4c : bv 32 := 0x00000693.
Lemma F_5bf4c : fetch_word Asan.M.loaded_segments (0x5bf9c : word) = Some W_5bf4c.
Proof. vm_refl. Qed.
Lemma D_5bf4c : decode_any W_5bf4c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf50 : bv 32 := 0x2f8000ef.
Lemma F_5bf50 : fetch_word Asan.M.loaded_segments (0x5bfa0 : word) = Some W_5bf50.
Proof. vm_refl. Qed.
Lemma D_5bf50 : decode_any W_5bf50 = Some (Jal 1 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf54 : bv 32 := 0x00043503.
Lemma F_5bf54 : fetch_word Asan.M.loaded_segments (0x5bfa4 : word) = Some W_5bf54.
Proof. vm_refl. Qed.
Lemma D_5bf54 : decode_any W_5bf54 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf58 : bv 32 := 0xfff00813.
Lemma F_5bf58 : fetch_word Asan.M.loaded_segments (0x5bfa8 : word) = Some W_5bf58.
Proof. vm_refl. Qed.
Lemma D_5bf58 : decode_any W_5bf58 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf5c : bv 32 := 0x00300613.
Lemma F_5bf5c : fetch_word Asan.M.loaded_segments (0x5bfac : word) = Some W_5bf5c.
Proof. vm_refl. Qed.
Lemma D_5bf5c : decode_any W_5bf5c = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf60 : bv 32 := 0x001005b7.
Lemma F_5bf60 : fetch_word Asan.M.loaded_segments (0x5bfb0 : word) = Some W_5bf60.
Proof. vm_refl. Qed.
Lemma D_5bf60 : decode_any W_5bf60 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf64 : bv 32 := 0xfffb4697.
Lemma F_5bf64 : fetch_word Asan.M.loaded_segments (0x5bfb4 : word) = Some W_5bf64.
Proof. vm_refl. Qed.
Lemma D_5bf64 : decode_any W_5bf64 = Some (Auipc 13 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf68 : bv 32 := 0x03c81713.
Lemma F_5bf68 : fetch_word Asan.M.loaded_segments (0x5bfb8 : word) = Some W_5bf68.
Proof. vm_refl. Qed.
Lemma D_5bf68 : decode_any W_5bf68 = Some (ShiftImm ALU_SLL 14 16 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf6c : bv 32 := 0x03d61613.
Lemma F_5bf6c : fetch_word Asan.M.loaded_segments (0x5bfbc : word) = Some W_5bf6c.
Proof. vm_refl. Qed.
Lemma D_5bf6c : decode_any W_5bf6c = Some (ShiftImm ALU_SLL 12 12 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf70 : bv 32 := 0xfff58593.
Lemma F_5bf70 : fetch_word Asan.M.loaded_segments (0x5bfc0 : word) = Some W_5bf70.
Proof. vm_refl. Qed.
Lemma D_5bf70 : decode_any W_5bf70 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf74 : bv 32 := 0x4946b683.
Lemma F_5bf74 : fetch_word Asan.M.loaded_segments (0x5bfc4 : word) = Some W_5bf74.
Proof. vm_refl. Qed.
Lemma D_5bf74 : decode_any W_5bf74 = Some (Load SZ8 true 13 13 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf78 : bv 32 := 0xfff70713.
Lemma F_5bf78 : fetch_word Asan.M.loaded_segments (0x5bfc8 : word) = Some W_5bf78.
Proof. vm_refl. Qed.
Lemma D_5bf78 : decode_any W_5bf78 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf7c : bv 32 := 0x02859793.
Lemma F_5bf7c : fetch_word Asan.M.loaded_segments (0x5bfcc : word) = Some W_5bf7c.
Proof. vm_refl. Qed.
Lemma D_5bf7c : decode_any W_5bf7c = Some (ShiftImm ALU_SLL 15 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf80 : bv 32 := 0x02881813.
Lemma F_5bf80 : fetch_word Asan.M.loaded_segments (0x5bfd0 : word) = Some W_5bf80.
Proof. vm_refl. Qed.
Lemma D_5bf80 : decode_any W_5bf80 = Some (ShiftImm ALU_SLL 16 16 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf84 : bv 32 := 0x00100893.
Lemma F_5bf84 : fetch_word Asan.M.loaded_segments (0x5bfd4 : word) = Some W_5bf84.
Proof. vm_refl. Qed.
Lemma D_5bf84 : decode_any W_5bf84 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf88 : bv 32 := 0x03e89893.
Lemma F_5bf88 : fetch_word Asan.M.loaded_segments (0x5bfd8 : word) = Some W_5bf88.
Proof. vm_refl. Qed.
Lemma D_5bf88 : decode_any W_5bf88 = Some (ShiftImm ALU_SLL 17 17 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf8c : bv 32 := 0x01c0006f.
Lemma F_5bf8c : fetch_word Asan.M.loaded_segments (0x5bfdc : word) = Some W_5bf8c.
Proof. vm_refl. Qed.
Lemma D_5bf8c : decode_any W_5bf8c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf90 : bv 32 := 0x1604332f.
Lemma F_5bf90 : fetch_word Asan.M.loaded_segments (0x5bfe0 : word) = Some W_5bf90.
Proof. vm_refl. Qed.
Lemma D_5bf90 : decode_any W_5bf90 = Some (Lr AD true true 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf94 : bv 32 := 0x00a31663.
Lemma F_5bf94 : fetch_word Asan.M.loaded_segments (0x5bfe4 : word) = Some W_5bf94.
Proof. vm_refl. Qed.
Lemma D_5bf94 : decode_any W_5bf94 = Some (Branch BC_NE 6 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf98 : bv 32 := 0x1a5433af.
Lemma F_5bf98 : fetch_word Asan.M.loaded_segments (0x5bfe8 : word) = Some W_5bf98.
Proof. vm_refl. Qed.
Lemma D_5bf98 : decode_any W_5bf98 = Some (Sc AD false true 7 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf9c : bv 32 := 0xfe039ae3.
Lemma F_5bf9c : fetch_word Asan.M.loaded_segments (0x5bfec : word) = Some W_5bf9c.
Proof. vm_refl. Qed.
Lemma D_5bf9c : decode_any W_5bf9c = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfa0 : bv 32 := 0x06a30463.
Lemma F_5bfa0 : fetch_word Asan.M.loaded_segments (0x5bff0 : word) = Some W_5bfa0.
Proof. vm_refl. Qed.
Lemma D_5bfa0 : decode_any W_5bfa0 = Some (Branch BC_EQ 6 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfa8 : bv 32 := 0x00c575b3.
Lemma F_5bfa8 : fetch_word Asan.M.loaded_segments (0x5bff8 : word) = Some W_5bfa8.
Proof. vm_refl. Qed.
Lemma D_5bfa8 : decode_any W_5bfa8 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfac : bv 32 := 0x00e572b3.
Lemma F_5bfac : fetch_word Asan.M.loaded_segments (0x5bffc : word) = Some W_5bfac.
Proof. vm_refl. Qed.
Lemma D_5bfac : decode_any W_5bfac = Some (Op ALU_AND 5 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfb0 : bv 32 := 0x02059663.
Lemma F_5bfb0 : fetch_word Asan.M.loaded_segments (0x5c000 : word) = Some W_5bfb0.
Proof. vm_refl. Qed.
Lemma D_5bfb0 : decode_any W_5bfb0 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfb4 : bv 32 := 0x00f575b3.
Lemma F_5bfb4 : fetch_word Asan.M.loaded_segments (0x5c004 : word) = Some W_5bfb4.
Proof. vm_refl. Qed.
Lemma D_5bfb4 : decode_any W_5bfb4 = Some (Op ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfb8 : bv 32 := 0x02058263.
Lemma F_5bfb8 : fetch_word Asan.M.loaded_segments (0x5c008 : word) = Some W_5bfb8.
Proof. vm_refl. Qed.
Lemma D_5bfb8 : decode_any W_5bfb8 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfdc : bv 32 := 0x018575b3.
Lemma F_5bfdc : fetch_word Asan.M.loaded_segments (0x5c02c : word) = Some W_5bfdc.
Proof. vm_refl. Qed.
Lemma D_5bfdc : decode_any W_5bfdc = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfe0 : bv 32 := 0x00b035b3.
Lemma F_5bfe0 : fetch_word Asan.M.loaded_segments (0x5c030 : word) = Some W_5bfe0.
Proof. vm_refl. Qed.
Lemma D_5bfe0 : decode_any W_5bfe0 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfe4 : bv 32 := 0x01455313.
Lemma F_5bfe4 : fetch_word Asan.M.loaded_segments (0x5c034 : word) = Some W_5bfe4.
Proof. vm_refl. Qed.
Lemma D_5bfe4 : decode_any W_5bfe4 = Some (ShiftImm ALU_SRL 6 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfe8 : bv 32 := 0xfff58593.
Lemma F_5bfe8 : fetch_word Asan.M.loaded_segments (0x5c038 : word) = Some W_5bfe8.
Proof. vm_refl. Qed.
Lemma D_5bfe8 : decode_any W_5bfe8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bfec : bv 32 := 0x00b375b3.
Lemma F_5bfec : fetch_word Asan.M.loaded_segments (0x5c03c : word) = Some W_5bfec.
Proof. vm_refl. Qed.
Lemma D_5bfec : decode_any W_5bfec = Some (Op ALU_AND 11 6 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bff0 : bv 32 := 0x02c59593.
Lemma F_5bff0 : fetch_word Asan.M.loaded_segments (0x5c040 : word) = Some W_5bff0.
Proof. vm_refl. Qed.
Lemma D_5bff0 : decode_any W_5bff0 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bff4 : bv 32 := 0x02c5d593.
Lemma F_5bff4 : fetch_word Asan.M.loaded_segments (0x5c044 : word) = Some W_5bff4.
Proof. vm_refl. Qed.
Lemma D_5bff4 : decode_any W_5bff4 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bff8 : bv 32 := 0xf8058ce3.
Lemma F_5bff8 : fetch_word Asan.M.loaded_segments (0x5c048 : word) = Some W_5bff8.
Proof. vm_refl. Qed.
Lemma D_5bff8 : decode_any W_5bff8 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c008 : bv 32 := 0x0a059c63.
Lemma F_5c008 : fetch_word Asan.M.loaded_segments (0x5c058 : word) = Some W_5c008.
Proof. vm_refl. Qed.
Lemma D_5c008 : decode_any W_5c008 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c00c : bv 32 := 0x07813083.
Lemma F_5c00c : fetch_word Asan.M.loaded_segments (0x5c05c : word) = Some W_5c00c.
Proof. vm_refl. Qed.
Lemma D_5c00c : decode_any W_5c00c = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c010 : bv 32 := 0x07013403.
Lemma F_5c010 : fetch_word Asan.M.loaded_segments (0x5c060 : word) = Some W_5c010.
Proof. vm_refl. Qed.
Lemma D_5c010 : decode_any W_5c010 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c014 : bv 32 := 0x06813483.
Lemma F_5c014 : fetch_word Asan.M.loaded_segments (0x5c064 : word) = Some W_5c014.
Proof. vm_refl. Qed.
Lemma D_5c014 : decode_any W_5c014 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c018 : bv 32 := 0x06013903.
Lemma F_5c018 : fetch_word Asan.M.loaded_segments (0x5c068 : word) = Some W_5c018.
Proof. vm_refl. Qed.
Lemma D_5c018 : decode_any W_5c018 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c01c : bv 32 := 0x05813983.
Lemma F_5c01c : fetch_word Asan.M.loaded_segments (0x5c06c : word) = Some W_5c01c.
Proof. vm_refl. Qed.
Lemma D_5c01c : decode_any W_5c01c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c020 : bv 32 := 0x05013a03.
Lemma F_5c020 : fetch_word Asan.M.loaded_segments (0x5c070 : word) = Some W_5c020.
Proof. vm_refl. Qed.
Lemma D_5c020 : decode_any W_5c020 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c024 : bv 32 := 0x04813a83.
Lemma F_5c024 : fetch_word Asan.M.loaded_segments (0x5c074 : word) = Some W_5c024.
Proof. vm_refl. Qed.
Lemma D_5c024 : decode_any W_5c024 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c028 : bv 32 := 0x04013b03.
Lemma F_5c028 : fetch_word Asan.M.loaded_segments (0x5c078 : word) = Some W_5c028.
Proof. vm_refl. Qed.
Lemma D_5c028 : decode_any W_5c028 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c02c : bv 32 := 0x03813b83.
Lemma F_5c02c : fetch_word Asan.M.loaded_segments (0x5c07c : word) = Some W_5c02c.
Proof. vm_refl. Qed.
Lemma D_5c02c : decode_any W_5c02c = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c030 : bv 32 := 0x03013c03.
Lemma F_5c030 : fetch_word Asan.M.loaded_segments (0x5c080 : word) = Some W_5c030.
Proof. vm_refl. Qed.
Lemma D_5c030 : decode_any W_5c030 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c034 : bv 32 := 0x02813c83.
Lemma F_5c034 : fetch_word Asan.M.loaded_segments (0x5c084 : word) = Some W_5c034.
Proof. vm_refl. Qed.
Lemma D_5c034 : decode_any W_5c034 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c038 : bv 32 := 0x02013d03.
Lemma F_5c038 : fetch_word Asan.M.loaded_segments (0x5c088 : word) = Some W_5c038.
Proof. vm_refl. Qed.
Lemma D_5c038 : decode_any W_5c038 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c03c : bv 32 := 0x01813d83.
Lemma F_5c03c : fetch_word Asan.M.loaded_segments (0x5c08c : word) = Some W_5c03c.
Proof. vm_refl. Qed.
Lemma D_5c03c : decode_any W_5c03c = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c040 : bv 32 := 0x08010113.
Lemma F_5c040 : fetch_word Asan.M.loaded_segments (0x5c090 : word) = Some W_5c040.
Proof. vm_refl. Qed.
Lemma D_5c040 : decode_any W_5c040 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c044 : bv 32 := 0x00008067.
Lemma F_5c044 : fetch_word Asan.M.loaded_segments (0x5c094 : word) = Some W_5c044.
Proof. vm_refl. Qed.
Lemma D_5c044 : decode_any W_5c044 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c8 : bv 32 := 0xfd010113.
Lemma F_5c0c8 : fetch_word Asan.M.loaded_segments (0x5c118 : word) = Some W_5c0c8.
Proof. vm_refl. Qed.
Lemma D_5c0c8 : decode_any W_5c0c8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0cc : bv 32 := 0x02113423.
Lemma F_5c0cc : fetch_word Asan.M.loaded_segments (0x5c11c : word) = Some W_5c0cc.
Proof. vm_refl. Qed.
Lemma D_5c0cc : decode_any W_5c0cc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d0 : bv 32 := 0x02813023.
Lemma F_5c0d0 : fetch_word Asan.M.loaded_segments (0x5c120 : word) = Some W_5c0d0.
Proof. vm_refl. Qed.
Lemma D_5c0d0 : decode_any W_5c0d0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d4 : bv 32 := 0x00913c23.
Lemma F_5c0d4 : fetch_word Asan.M.loaded_segments (0x5c124 : word) = Some W_5c0d4.
Proof. vm_refl. Qed.
Lemma D_5c0d4 : decode_any W_5c0d4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d8 : bv 32 := 0x01213823.
Lemma F_5c0d8 : fetch_word Asan.M.loaded_segments (0x5c128 : word) = Some W_5c0d8.
Proof. vm_refl. Qed.
Lemma D_5c0d8 : decode_any W_5c0d8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0dc : bv 32 := 0x01313423.
Lemma F_5c0dc : fetch_word Asan.M.loaded_segments (0x5c12c : word) = Some W_5c0dc.
Proof. vm_refl. Qed.
Lemma D_5c0dc : decode_any W_5c0dc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e0 : bv 32 := 0x0185b703.
Lemma F_5c0e0 : fetch_word Asan.M.loaded_segments (0x5c130 : word) = Some W_5c0e0.
Proof. vm_refl. Qed.
Lemma D_5c0e0 : decode_any W_5c0e0 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e4 : bv 32 := 0x00269793.
Lemma F_5c0e4 : fetch_word Asan.M.loaded_segments (0x5c134 : word) = Some W_5c0e4.
Proof. vm_refl. Qed.
Lemma D_5c0e4 : decode_any W_5c0e4 = Some (ShiftImm ALU_SLL 15 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e8 : bv 32 := 0x00100693.
Lemma F_5c0e8 : fetch_word Asan.M.loaded_segments (0x5c138 : word) = Some W_5c0e8.
Proof. vm_refl. Qed.
Lemma D_5c0e8 : decode_any W_5c0e8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0ec : bv 32 := 0x0cf77063.
Lemma F_5c0ec : fetch_word Asan.M.loaded_segments (0x5c13c : word) = Some W_5c0ec.
Proof. vm_refl. Qed.
Lemma D_5c0ec : decode_any W_5c0ec = Some (Branch BC_GEU 14 15 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f0 : bv 32 := 0x000406b7.
Lemma F_5c0f0 : fetch_word Asan.M.loaded_segments (0x5c140 : word) = Some W_5c0f0.
Proof. vm_refl. Qed.
Lemma D_5c0f0 : decode_any W_5c0f0 = Some (Lui 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f4 : bv 32 := 0xfff6869b.
Lemma F_5c0f4 : fetch_word Asan.M.loaded_segments (0x5c144 : word) = Some W_5c0f4.
Proof. vm_refl. Qed.
Lemma D_5c0f4 : decode_any W_5c0f4 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f8 : bv 32 := 0x00d786b3.
Lemma F_5c0f8 : fetch_word Asan.M.loaded_segments (0x5c148 : word) = Some W_5c0f8.
Proof. vm_refl. Qed.
Lemma D_5c0f8 : decode_any W_5c0f8 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0fc : bv 32 := 0xfffc0437.
Lemma F_5c0fc : fetch_word Asan.M.loaded_segments (0x5c14c : word) = Some W_5c0fc.
Proof. vm_refl. Qed.
Lemma D_5c0fc : decode_any W_5c0fc = Some (Lui 8 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c100 : bv 32 := 0x0086f433.
Lemma F_5c100 : fetch_word Asan.M.loaded_segments (0x5c150 : word) = Some W_5c100.
Proof. vm_refl. Qed.
Lemma D_5c100 : decode_any W_5c100 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c104 : bv 32 := 0x200006b7.
Lemma F_5c104 : fetch_word Asan.M.loaded_segments (0x5c154 : word) = Some W_5c104.
Proof. vm_refl. Qed.
Lemma D_5c104 : decode_any W_5c104 = Some (Lui 13 131072, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c108 : bv 32 := 0x0016869b.
Lemma F_5c108 : fetch_word Asan.M.loaded_segments (0x5c158 : word) = Some W_5c108.
Proof. vm_refl. Qed.
Lemma D_5c108 : decode_any W_5c108 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c10c : bv 32 := 0x0cd47063.
Lemma F_5c10c : fetch_word Asan.M.loaded_segments (0x5c15c : word) = Some W_5c10c.
Proof. vm_refl. Qed.
Lemma D_5c10c : decode_any W_5c10c = Some (Branch BC_GEU 8 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c110 : bv 32 := 0x03854683.
Lemma F_5c110 : fetch_word Asan.M.loaded_segments (0x5c160 : word) = Some W_5c110.
Proof. vm_refl. Qed.
Lemma D_5c110 : decode_any W_5c110 = Some (Load SZ1 false 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c114 : bv 32 := 0x00700793.
Lemma F_5c114 : fetch_word Asan.M.loaded_segments (0x5c164 : word) = Some W_5c114.
Proof. vm_refl. Qed.
Lemma D_5c114 : decode_any W_5c114 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c118 : bv 32 := 0x01d79793.
Lemma F_5c118 : fetch_word Asan.M.loaded_segments (0x5c168 : word) = Some W_5c118.
Proof. vm_refl. Qed.
Lemma D_5c118 : decode_any W_5c118 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c11c : bv 32 := 0x00f60633.
Lemma F_5c11c : fetch_word Asan.M.loaded_segments (0x5c16c : word) = Some W_5c11c.
Proof. vm_refl. Qed.
Lemma D_5c11c : decode_any W_5c11c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c120 : bv 32 := 0x00c704b3.
Lemma F_5c120 : fetch_word Asan.M.loaded_segments (0x5c170 : word) = Some W_5c120.
Proof. vm_refl. Qed.
Lemma D_5c120 : decode_any W_5c120 = Some (Op ALU_ADD 9 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c124 : bv 32 := 0x02068463.
Lemma F_5c124 : fetch_word Asan.M.loaded_segments (0x5c174 : word) = Some W_5c124.
Proof. vm_refl. Qed.
Lemma D_5c124 : decode_any W_5c124 = Some (Branch BC_EQ 13 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c14c : bv 32 := 0x00058993.
Lemma F_5c14c : fetch_word Asan.M.loaded_segments (0x5c19c : word) = Some W_5c14c.
Proof. vm_refl. Qed.
Lemma D_5c14c : decode_any W_5c14c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c150 : bv 32 := 0x40e40933.
Lemma F_5c150 : fetch_word Asan.M.loaded_segments (0x5c1a0 : word) = Some W_5c150.
Proof. vm_refl. Qed.
Lemma D_5c150 : decode_any W_5c150 = Some (Op ALU_SUB 18 8 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c154 : bv 32 := 0xfffbe597.
Lemma F_5c154 : fetch_word Asan.M.loaded_segments (0x5c1a4 : word) = Some W_5c154.
Proof. vm_refl. Qed.
Lemma D_5c154 : decode_any W_5c154 = Some (Auipc 11 1048510, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c158 : bv 32 := 0xc8b58693.
Lemma F_5c158 : fetch_word Asan.M.loaded_segments (0x5c1a8 : word) = Some W_5c158.
Proof. vm_refl. Qed.
Lemma D_5c158 : decode_any W_5c158 = Some (OpImm ALU_ADD 13 11 3211, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c15c : bv 32 := 0x00048593.
Lemma F_5c15c : fetch_word Asan.M.loaded_segments (0x5c1ac : word) = Some W_5c15c.
Proof. vm_refl. Qed.
Lemma D_5c15c : decode_any W_5c15c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c160 : bv 32 := 0x00090613.
Lemma F_5c160 : fetch_word Asan.M.loaded_segments (0x5c1b0 : word) = Some W_5c160.
Proof. vm_refl. Qed.
Lemma D_5c160 : decode_any W_5c160 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c164 : bv 32 := 0x141400ef.
Lemma F_5c164 : fetch_word Asan.M.loaded_segments (0x5c1b4 : word) = Some W_5c164.
Proof. vm_refl. Qed.
Lemma D_5c164 : decode_any W_5c164 = Some (Jal 1 264512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c168 : bv 32 := 0x08050263.
Lemma F_5c168 : fetch_word Asan.M.loaded_segments (0x5c1b8 : word) = Some W_5c168.
Proof. vm_refl. Qed.
Lemma D_5c168 : decode_any W_5c168 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c16c : bv 32 := 0x00050713.
Lemma F_5c16c : fetch_word Asan.M.loaded_segments (0x5c1bc : word) = Some W_5c16c.
Proof. vm_refl. Qed.
Lemma D_5c16c : decode_any W_5c16c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c170 : bv 32 := 0x08a49263.
Lemma F_5c170 : fetch_word Asan.M.loaded_segments (0x5c1c0 : word) = Some W_5c170.
Proof. vm_refl. Qed.
Lemma D_5c170 : decode_any W_5c170 = Some (Branch BC_NE 9 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c174 : bv 32 := 0x0fa00613.
Lemma F_5c174 : fetch_word Asan.M.loaded_segments (0x5c1c4 : word) = Some W_5c174.
Proof. vm_refl. Qed.
Lemma D_5c174 : decode_any W_5c174 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c178 : bv 32 := 0x00048513.
Lemma F_5c178 : fetch_word Asan.M.loaded_segments (0x5c1c8 : word) = Some W_5c178.
Proof. vm_refl. Qed.
Lemma D_5c178 : decode_any W_5c178 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c17c : bv 32 := 0x00090593.
Lemma F_5c17c : fetch_word Asan.M.loaded_segments (0x5c1cc : word) = Some W_5c17c.
Proof. vm_refl. Qed.
Lemma D_5c17c : decode_any W_5c17c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c180 : bv 32 := 0x091250ef.
Lemma F_5c180 : fetch_word Asan.M.loaded_segments (0x5c1d0 : word) = Some W_5c180.
Proof. vm_refl. Qed.
Lemma D_5c180 : decode_any W_5c180 = Some (Jal 1 153744, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c184 : bv 32 := 0x0052d0ef.
Lemma F_5c184 : fetch_word Asan.M.loaded_segments (0x5c1d4 : word) = Some W_5c184.
Proof. vm_refl. Qed.
Lemma D_5c184 : decode_any W_5c184 = Some (Jal 1 186372, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c188 : bv 32 := 0x05053583.
Lemma F_5c188 : fetch_word Asan.M.loaded_segments (0x5c1d8 : word) = Some W_5c188.
Proof. vm_refl. Qed.
Lemma D_5c188 : decode_any W_5c188 = Some (Load SZ8 true 11 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c18c : bv 32 := 0x04853603.
Lemma F_5c18c : fetch_word Asan.M.loaded_segments (0x5c1dc : word) = Some W_5c18c.
Proof. vm_refl. Qed.
Lemma D_5c18c : decode_any W_5c18c = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c190 : bv 32 := 0x012585b3.
Lemma F_5c190 : fetch_word Asan.M.loaded_segments (0x5c1e0 : word) = Some W_5c190.
Proof. vm_refl. Qed.
Lemma D_5c190 : decode_any W_5c190 = Some (Op ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c194 : bv 32 := 0x00160613.
Lemma F_5c194 : fetch_word Asan.M.loaded_segments (0x5c1e4 : word) = Some W_5c194.
Proof. vm_refl. Qed.
Lemma D_5c194 : decode_any W_5c194 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c198 : bv 32 := 0x04c53423.
Lemma F_5c198 : fetch_word Asan.M.loaded_segments (0x5c1e8 : word) = Some W_5c198.
Proof. vm_refl. Qed.
Lemma D_5c198 : decode_any W_5c198 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c19c : bv 32 := 0x04b53823.
Lemma F_5c19c : fetch_word Asan.M.loaded_segments (0x5c1ec : word) = Some W_5c19c.
Proof. vm_refl. Qed.
Lemma D_5c19c : decode_any W_5c19c = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a0 : bv 32 := 0x00098593.
Lemma F_5c1a0 : fetch_word Asan.M.loaded_segments (0x5c1f0 : word) = Some W_5c1a0.
Proof. vm_refl. Qed.
Lemma D_5c1a0 : decode_any W_5c1a0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a4 : bv 32 := 0x0085bc23.
Lemma F_5c1a4 : fetch_word Asan.M.loaded_segments (0x5c1f4 : word) = Some W_5c1a4.
Proof. vm_refl. Qed.
Lemma D_5c1a4 : decode_any W_5c1a4 = Some (Store SZ8 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a8 : bv 32 := 0x00100693.
Lemma F_5c1a8 : fetch_word Asan.M.loaded_segments (0x5c1f8 : word) = Some W_5c1a8.
Proof. vm_refl. Qed.
Lemma D_5c1a8 : decode_any W_5c1a8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1ac : bv 32 := 0x00068513.
Lemma F_5c1ac : fetch_word Asan.M.loaded_segments (0x5c1fc : word) = Some W_5c1ac.
Proof. vm_refl. Qed.
Lemma D_5c1ac : decode_any W_5c1ac = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b0 : bv 32 := 0x02813083.
Lemma F_5c1b0 : fetch_word Asan.M.loaded_segments (0x5c200 : word) = Some W_5c1b0.
Proof. vm_refl. Qed.
Lemma D_5c1b0 : decode_any W_5c1b0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b4 : bv 32 := 0x02013403.
Lemma F_5c1b4 : fetch_word Asan.M.loaded_segments (0x5c204 : word) = Some W_5c1b4.
Proof. vm_refl. Qed.
Lemma D_5c1b4 : decode_any W_5c1b4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b8 : bv 32 := 0x01813483.
Lemma F_5c1b8 : fetch_word Asan.M.loaded_segments (0x5c208 : word) = Some W_5c1b8.
Proof. vm_refl. Qed.
Lemma D_5c1b8 : decode_any W_5c1b8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1bc : bv 32 := 0x01013903.
Lemma F_5c1bc : fetch_word Asan.M.loaded_segments (0x5c20c : word) = Some W_5c1bc.
Proof. vm_refl. Qed.
Lemma D_5c1bc : decode_any W_5c1bc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c0 : bv 32 := 0x00813983.
Lemma F_5c1c0 : fetch_word Asan.M.loaded_segments (0x5c210 : word) = Some W_5c1c0.
Proof. vm_refl. Qed.
Lemma D_5c1c0 : decode_any W_5c1c0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c4 : bv 32 := 0x03010113.
Lemma F_5c1c4 : fetch_word Asan.M.loaded_segments (0x5c214 : word) = Some W_5c1c4.
Proof. vm_refl. Qed.
Lemma D_5c1c4 : decode_any W_5c1c4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c8 : bv 32 := 0x00008067.
Lemma F_5c1c8 : fetch_word Asan.M.loaded_segments (0x5c218 : word) = Some W_5c1c8.
Proof. vm_refl. Qed.
Lemma D_5c1c8 : decode_any W_5c1c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c248 : bv 32 := 0xfb010113.
Lemma F_5c248 : fetch_word Asan.M.loaded_segments (0x5c298 : word) = Some W_5c248.
Proof. vm_refl. Qed.
Lemma D_5c248 : decode_any W_5c248 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c24c : bv 32 := 0x04113423.
Lemma F_5c24c : fetch_word Asan.M.loaded_segments (0x5c29c : word) = Some W_5c24c.
Proof. vm_refl. Qed.
Lemma D_5c24c : decode_any W_5c24c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c250 : bv 32 := 0x04813023.
Lemma F_5c250 : fetch_word Asan.M.loaded_segments (0x5c2a0 : word) = Some W_5c250.
Proof. vm_refl. Qed.
Lemma D_5c250 : decode_any W_5c250 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c254 : bv 32 := 0x02913c23.
Lemma F_5c254 : fetch_word Asan.M.loaded_segments (0x5c2a4 : word) = Some W_5c254.
Proof. vm_refl. Qed.
Lemma D_5c254 : decode_any W_5c254 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c258 : bv 32 := 0x03213823.
Lemma F_5c258 : fetch_word Asan.M.loaded_segments (0x5c2a8 : word) = Some W_5c258.
Proof. vm_refl. Qed.
Lemma D_5c258 : decode_any W_5c258 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c25c : bv 32 := 0x03313423.
Lemma F_5c25c : fetch_word Asan.M.loaded_segments (0x5c2ac : word) = Some W_5c25c.
Proof. vm_refl. Qed.
Lemma D_5c25c : decode_any W_5c25c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c260 : bv 32 := 0x03413023.
Lemma F_5c260 : fetch_word Asan.M.loaded_segments (0x5c2b0 : word) = Some W_5c260.
Proof. vm_refl. Qed.
Lemma D_5c260 : decode_any W_5c260 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c264 : bv 32 := 0x01513c23.
Lemma F_5c264 : fetch_word Asan.M.loaded_segments (0x5c2b4 : word) = Some W_5c264.
Proof. vm_refl. Qed.
Lemma D_5c264 : decode_any W_5c264 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c268 : bv 32 := 0x01613823.
Lemma F_5c268 : fetch_word Asan.M.loaded_segments (0x5c2b8 : word) = Some W_5c268.
Proof. vm_refl. Qed.
Lemma D_5c268 : decode_any W_5c268 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c26c : bv 32 := 0x01713423.
Lemma F_5c26c : fetch_word Asan.M.loaded_segments (0x5c2bc : word) = Some W_5c26c.
Proof. vm_refl. Qed.
Lemma D_5c26c : decode_any W_5c26c = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c270 : bv 32 := 0x00068a93.
Lemma F_5c270 : fetch_word Asan.M.loaded_segments (0x5c2c0 : word) = Some W_5c270.
Proof. vm_refl. Qed.
Lemma D_5c270 : decode_any W_5c270 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c274 : bv 32 := 0x00060493.
Lemma F_5c274 : fetch_word Asan.M.loaded_segments (0x5c2c4 : word) = Some W_5c274.
Proof. vm_refl. Qed.
Lemma D_5c274 : decode_any W_5c274 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c278 : bv 32 := 0x00058413.
Lemma F_5c278 : fetch_word Asan.M.loaded_segments (0x5c2c8 : word) = Some W_5c278.
Proof. vm_refl. Qed.
Lemma D_5c278 : decode_any W_5c278 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c27c : bv 32 := 0x00050993.
Lemma F_5c27c : fetch_word Asan.M.loaded_segments (0x5c2cc : word) = Some W_5c27c.
Proof. vm_refl. Qed.
Lemma D_5c27c : decode_any W_5c27c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c280 : bv 32 := 0x03053b03.
Lemma F_5c280 : fetch_word Asan.M.loaded_segments (0x5c2d0 : word) = Some W_5c280.
Proof. vm_refl. Qed.
Lemma D_5c280 : decode_any W_5c280 = Some (Load SZ8 true 22 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c284 : bv 32 := 0x01f00513.
Lemma F_5c284 : fetch_word Asan.M.loaded_segments (0x5c2d4 : word) = Some W_5c284.
Proof. vm_refl. Qed.
Lemma D_5c284 : decode_any W_5c284 = Some (OpImm ALU_ADD 10 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c288 : bv 32 := 0x00761593.
Lemma F_5c288 : fetch_word Asan.M.loaded_segments (0x5c2d8 : word) = Some W_5c288.
Proof. vm_refl. Qed.
Lemma D_5c288 : decode_any W_5c288 = Some (ShiftImm ALU_SLL 11 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c28c : bv 32 := 0x18a60863.
Lemma F_5c28c : fetch_word Asan.M.loaded_segments (0x5c2dc : word) = Some W_5c28c.
Proof. vm_refl. Qed.
Lemma D_5c28c : decode_any W_5c28c = Some (Branch BC_EQ 12 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c290 : bv 32 := 0x01000513.
Lemma F_5c290 : fetch_word Asan.M.loaded_segments (0x5c2e0 : word) = Some W_5c290.
Proof. vm_refl. Qed.
Lemma D_5c290 : decode_any W_5c290 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c294 : bv 32 := 0x00956663.
Lemma F_5c294 : fetch_word Asan.M.loaded_segments (0x5c2e4 : word) = Some W_5c294.
Proof. vm_refl. Qed.
Lemma D_5c294 : decode_any W_5c294 = Some (Branch BC_LTU 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c298 : bv 32 := 0x00549913.
Lemma F_5c298 : fetch_word Asan.M.loaded_segments (0x5c2e8 : word) = Some W_5c298.
Proof. vm_refl. Qed.
Lemma D_5c298 : decode_any W_5c298 = Some (ShiftImm ALU_SLL 18 9 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c29c : bv 32 := 0x0280006f.
Lemma F_5c29c : fetch_word Asan.M.loaded_segments (0x5c2ec : word) = Some W_5c29c.
Proof. vm_refl. Qed.
Lemma D_5c29c : decode_any W_5c29c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a0 : bv 32 := 0xff048513.
Lemma F_5c2a0 : fetch_word Asan.M.loaded_segments (0x5c2f0 : word) = Some W_5c2a0.
Proof. vm_refl. Qed.
Lemma D_5c2a0 : decode_any W_5c2a0 = Some (OpImm ALU_ADD 10 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a4 : bv 32 := 0x20000613.
Lemma F_5c2a4 : fetch_word Asan.M.loaded_segments (0x5c2f4 : word) = Some W_5c2a4.
Proof. vm_refl. Qed.
Lemma D_5c2a4 : decode_any W_5c2a4 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a8 : bv 32 := 0x03f49693.
Lemma F_5c2a8 : fetch_word Asan.M.loaded_segments (0x5c2f8 : word) = Some W_5c2a8.
Proof. vm_refl. Qed.
Lemma D_5c2a8 : decode_any W_5c2a8 = Some (ShiftImm ALU_SLL 13 9 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2ac : bv 32 := 0x00155513.
Lemma F_5c2ac : fetch_word Asan.M.loaded_segments (0x5c2fc : word) = Some W_5c2ac.
Proof. vm_refl. Qed.
Lemma D_5c2ac : decode_any W_5c2ac = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b0 : bv 32 := 0x00a61933.
Lemma F_5c2b0 : fetch_word Asan.M.loaded_segments (0x5c300 : word) = Some W_5c2b0.
Proof. vm_refl. Qed.
Lemma D_5c2b0 : decode_any W_5c2b0 = Some (Op ALU_SLL 18 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b4 : bv 32 := 0x00195513.
Lemma F_5c2b4 : fetch_word Asan.M.loaded_segments (0x5c304 : word) = Some W_5c2b4.
Proof. vm_refl. Qed.
Lemma D_5c2b4 : decode_any W_5c2b4 = Some (ShiftImm ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b8 : bv 32 := 0x43f6d693.
Lemma F_5c2b8 : fetch_word Asan.M.loaded_segments (0x5c308 : word) = Some W_5c2b8.
Proof. vm_refl. Qed.
Lemma D_5c2b8 : decode_any W_5c2b8 = Some (ShiftImm ALU_SRA 13 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2bc : bv 32 := 0x00a6f533.
Lemma F_5c2bc : fetch_word Asan.M.loaded_segments (0x5c30c : word) = Some W_5c2bc.
Proof. vm_refl. Qed.
Lemma D_5c2bc : decode_any W_5c2bc = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c0 : bv 32 := 0x01250933.
Lemma F_5c2c0 : fetch_word Asan.M.loaded_segments (0x5c310 : word) = Some W_5c2c0.
Proof. vm_refl. Qed.
Lemma D_5c2c0 : decode_any W_5c2c0 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c4 : bv 32 := 0x000fb517.
Lemma F_5c2c4 : fetch_word Asan.M.loaded_segments (0x5c314 : word) = Some W_5c2c4.
Proof. vm_refl. Qed.
Lemma D_5c2c4 : decode_any W_5c2c4 = Some (Auipc 10 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c8 : bv 32 := 0xa6453a03.
Lemma F_5c2c8 : fetch_word Asan.M.loaded_segments (0x5c318 : word) = Some W_5c2c8.
Proof. vm_refl. Qed.
Lemma D_5c2c8 : decode_any W_5c2c8 = Some (Load SZ8 true 20 10 2660, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2cc : bv 32 := 0x000a3503.
Lemma F_5c2cc : fetch_word Asan.M.loaded_segments (0x5c31c : word) = Some W_5c2cc.
Proof. vm_refl. Qed.
Lemma D_5c2cc : decode_any W_5c2cc = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d0 : bv 32 := 0x00bb0b33.
Lemma F_5c2d0 : fetch_word Asan.M.loaded_segments (0x5c320 : word) = Some W_5c2d0.
Proof. vm_refl. Qed.
Lemma D_5c2d0 : decode_any W_5c2d0 = Some (Op ALU_ADD 22 22 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d4 : bv 32 := 0x00050a63.
Lemma F_5c2d4 : fetch_word Asan.M.loaded_segments (0x5c324 : word) = Some W_5c2d4.
Proof. vm_refl. Qed.
Lemma D_5c2d4 : decode_any W_5c2d4 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d8 : bv 32 := 0x010b3a03.
Lemma F_5c2d8 : fetch_word Asan.M.loaded_segments (0x5c328 : word) = Some W_5c2d8.
Proof. vm_refl. Qed.
Lemma D_5c2d8 : decode_any W_5c2d8 = Some (Load SZ8 true 20 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2dc : bv 32 := 0x032a05b3.
Lemma F_5c2dc : fetch_word Asan.M.loaded_segments (0x5c32c : word) = Some W_5c2dc.
Proof. vm_refl. Qed.
Lemma D_5c2dc : decode_any W_5c2dc = Some (Mul M_MUL 11 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e0 : bv 32 := 0x00a5fe63.
Lemma F_5c2e0 : fetch_word Asan.M.loaded_segments (0x5c330 : word) = Some W_5c2e0.
Proof. vm_refl. Qed.
Lemma D_5c2e0 : decode_any W_5c2e0 = Some (Branch BC_GEU 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e4 : bv 32 := 0x10c0006f.
Lemma F_5c2e4 : fetch_word Asan.M.loaded_segments (0x5c334 : word) = Some W_5c2e4.
Proof. vm_refl. Qed.
Lemma D_5c2e4 : decode_any W_5c2e4 = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2fc : bv 32 := 0x050b3583.
Lemma F_5c2fc : fetch_word Asan.M.loaded_segments (0x5c34c : word) = Some W_5c2fc.
Proof. vm_refl. Qed.
Lemma D_5c2fc : decode_any W_5c2fc = Some (Load SZ8 true 11 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c300 : bv 32 := 0x058b3603.
Lemma F_5c300 : fetch_word Asan.M.loaded_segments (0x5c350 : word) = Some W_5c300.
Proof. vm_refl. Qed.
Lemma D_5c300 : decode_any W_5c300 = Some (Load SZ8 true 12 22 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c304 : bv 32 := 0x40c585b3.
Lemma F_5c304 : fetch_word Asan.M.loaded_segments (0x5c354 : word) = Some W_5c304.
Proof. vm_refl. Qed.
Lemma D_5c304 : decode_any W_5c304 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c308 : bv 32 := 0x032585b3.
Lemma F_5c308 : fetch_word Asan.M.loaded_segments (0x5c358 : word) = Some W_5c308.
Proof. vm_refl. Qed.
Lemma D_5c308 : decode_any W_5c308 = Some (Mul M_MUL 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c30c : bv 32 := 0x0ea5e263.
Lemma F_5c30c : fetch_word Asan.M.loaded_segments (0x5c35c : word) = Some W_5c30c.
Proof. vm_refl. Qed.
Lemma D_5c30c : decode_any W_5c30c = Some (Branch BC_LTU 11 10 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c310 : bv 32 := 0x020a9a63.
Lemma F_5c310 : fetch_word Asan.M.loaded_segments (0x5c360 : word) = Some W_5c310.
Proof. vm_refl. Qed.
Lemma D_5c310 : decode_any W_5c310 = Some (Branch BC_NE 21 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c314 : bv 32 := 0x0289a583.
Lemma F_5c314 : fetch_word Asan.M.loaded_segments (0x5c364 : word) = Some W_5c314.
Proof. vm_refl. Qed.
Lemma D_5c314 : decode_any W_5c314 = Some (Load SZ4 true 11 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c318 : bv 32 := 0x0c05cc63.
Lemma F_5c318 : fetch_word Asan.M.loaded_segments (0x5c368 : word) = Some W_5c318.
Proof. vm_refl. Qed.
Lemma D_5c318 : decode_any W_5c318 = Some (Branch BC_LT 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3f0 : bv 32 := 0x04813083.
Lemma F_5c3f0 : fetch_word Asan.M.loaded_segments (0x5c440 : word) = Some W_5c3f0.
Proof. vm_refl. Qed.
Lemma D_5c3f0 : decode_any W_5c3f0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3f4 : bv 32 := 0x04013403.
Lemma F_5c3f4 : fetch_word Asan.M.loaded_segments (0x5c444 : word) = Some W_5c3f4.
Proof. vm_refl. Qed.
Lemma D_5c3f4 : decode_any W_5c3f4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3f8 : bv 32 := 0x03813483.
Lemma F_5c3f8 : fetch_word Asan.M.loaded_segments (0x5c448 : word) = Some W_5c3f8.
Proof. vm_refl. Qed.
Lemma D_5c3f8 : decode_any W_5c3f8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3fc : bv 32 := 0x03013903.
Lemma F_5c3fc : fetch_word Asan.M.loaded_segments (0x5c44c : word) = Some W_5c3fc.
Proof. vm_refl. Qed.
Lemma D_5c3fc : decode_any W_5c3fc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c400 : bv 32 := 0x02813983.
Lemma F_5c400 : fetch_word Asan.M.loaded_segments (0x5c450 : word) = Some W_5c400.
Proof. vm_refl. Qed.
Lemma D_5c400 : decode_any W_5c400 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c404 : bv 32 := 0x02013a03.
Lemma F_5c404 : fetch_word Asan.M.loaded_segments (0x5c454 : word) = Some W_5c404.
Proof. vm_refl. Qed.
Lemma D_5c404 : decode_any W_5c404 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c408 : bv 32 := 0x01813a83.
Lemma F_5c408 : fetch_word Asan.M.loaded_segments (0x5c458 : word) = Some W_5c408.
Proof. vm_refl. Qed.
Lemma D_5c408 : decode_any W_5c408 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c40c : bv 32 := 0x01013b03.
Lemma F_5c40c : fetch_word Asan.M.loaded_segments (0x5c45c : word) = Some W_5c40c.
Proof. vm_refl. Qed.
Lemma D_5c40c : decode_any W_5c40c = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c410 : bv 32 := 0x00813b83.
Lemma F_5c410 : fetch_word Asan.M.loaded_segments (0x5c460 : word) = Some W_5c410.
Proof. vm_refl. Qed.
Lemma D_5c410 : decode_any W_5c410 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c414 : bv 32 := 0x05010113.
Lemma F_5c414 : fetch_word Asan.M.loaded_segments (0x5c464 : word) = Some W_5c414.
Proof. vm_refl. Qed.
Lemma D_5c414 : decode_any W_5c414 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c418 : bv 32 := 0x00008067.
Lemma F_5c418 : fetch_word Asan.M.loaded_segments (0x5c468 : word) = Some W_5c418.
Proof. vm_refl. Qed.
Lemma D_5c418 : decode_any W_5c418 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
