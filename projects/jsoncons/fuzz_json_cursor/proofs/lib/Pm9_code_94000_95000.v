(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9401c : bv 32 := 0x00155593.
Lemma F_9401c : fetch_word AsanUbsan.M.loaded_segments (0x94064 : word) = Some W_9401c.
Proof. vm_refl. Qed.
Lemma D_9401c : decode_any W_9401c = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_94020 : bv 32 := 0x55555637.
Lemma F_94020 : fetch_word AsanUbsan.M.loaded_segments (0x94068 : word) = Some W_94020.
Proof. vm_refl. Qed.
Lemma D_94020 : decode_any W_94020 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_94024 : bv 32 := 0x333336b7.
Lemma F_94024 : fetch_word AsanUbsan.M.loaded_segments (0x9406c : word) = Some W_94024.
Proof. vm_refl. Qed.
Lemma D_94024 : decode_any W_94024 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_94028 : bv 32 := 0x0f0f1737.
Lemma F_94028 : fetch_word AsanUbsan.M.loaded_segments (0x94070 : word) = Some W_94028.
Proof. vm_refl. Qed.
Lemma D_94028 : decode_any W_94028 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_9402c : bv 32 := 0x010107b7.
Lemma F_9402c : fetch_word AsanUbsan.M.loaded_segments (0x94074 : word) = Some W_9402c.
Proof. vm_refl. Qed.
Lemma D_9402c : decode_any W_9402c = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_94030 : bv 32 := 0x00b56533.
Lemma F_94030 : fetch_word AsanUbsan.M.loaded_segments (0x94078 : word) = Some W_94030.
Proof. vm_refl. Qed.
Lemma D_94030 : decode_any W_94030 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94034 : bv 32 := 0x5556059b.
Lemma F_94034 : fetch_word AsanUbsan.M.loaded_segments (0x9407c : word) = Some W_94034.
Proof. vm_refl. Qed.
Lemma D_94034 : decode_any W_94034 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_94038 : bv 32 := 0x3336861b.
Lemma F_94038 : fetch_word AsanUbsan.M.loaded_segments (0x94080 : word) = Some W_94038.
Proof. vm_refl. Qed.
Lemma D_94038 : decode_any W_94038 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_9403c : bv 32 := 0xf0f7069b.
Lemma F_9403c : fetch_word AsanUbsan.M.loaded_segments (0x94084 : word) = Some W_9403c.
Proof. vm_refl. Qed.
Lemma D_9403c : decode_any W_9403c = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_94040 : bv 32 := 0x1017871b.
Lemma F_94040 : fetch_word AsanUbsan.M.loaded_segments (0x94088 : word) = Some W_94040.
Proof. vm_refl. Qed.
Lemma D_94040 : decode_any W_94040 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_94044 : bv 32 := 0x00255793.
Lemma F_94044 : fetch_word AsanUbsan.M.loaded_segments (0x9408c : word) = Some W_94044.
Proof. vm_refl. Qed.
Lemma D_94044 : decode_any W_94044 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_94048 : bv 32 := 0x00f56533.
Lemma F_94048 : fetch_word AsanUbsan.M.loaded_segments (0x94090 : word) = Some W_94048.
Proof. vm_refl. Qed.
Lemma D_94048 : decode_any W_94048 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9404c : bv 32 := 0x02059793.
Lemma F_9404c : fetch_word AsanUbsan.M.loaded_segments (0x94094 : word) = Some W_9404c.
Proof. vm_refl. Qed.
Lemma D_9404c : decode_any W_9404c = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94050 : bv 32 := 0x00f585b3.
Lemma F_94050 : fetch_word AsanUbsan.M.loaded_segments (0x94098 : word) = Some W_94050.
Proof. vm_refl. Qed.
Lemma D_94050 : decode_any W_94050 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_94054 : bv 32 := 0x02061793.
Lemma F_94054 : fetch_word AsanUbsan.M.loaded_segments (0x9409c : word) = Some W_94054.
Proof. vm_refl. Qed.
Lemma D_94054 : decode_any W_94054 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94058 : bv 32 := 0x00f60633.
Lemma F_94058 : fetch_word AsanUbsan.M.loaded_segments (0x940a0 : word) = Some W_94058.
Proof. vm_refl. Qed.
Lemma D_94058 : decode_any W_94058 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9405c : bv 32 := 0x02069793.
Lemma F_9405c : fetch_word AsanUbsan.M.loaded_segments (0x940a4 : word) = Some W_9405c.
Proof. vm_refl. Qed.
Lemma D_9405c : decode_any W_9405c = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94060 : bv 32 := 0x00f686b3.
Lemma F_94060 : fetch_word AsanUbsan.M.loaded_segments (0x940a8 : word) = Some W_94060.
Proof. vm_refl. Qed.
Lemma D_94060 : decode_any W_94060 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_94064 : bv 32 := 0x02071793.
Lemma F_94064 : fetch_word AsanUbsan.M.loaded_segments (0x940ac : word) = Some W_94064.
Proof. vm_refl. Qed.
Lemma D_94064 : decode_any W_94064 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94068 : bv 32 := 0x00f70733.
Lemma F_94068 : fetch_word AsanUbsan.M.loaded_segments (0x940b0 : word) = Some W_94068.
Proof. vm_refl. Qed.
Lemma D_94068 : decode_any W_94068 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9406c : bv 32 := 0x00455793.
Lemma F_9406c : fetch_word AsanUbsan.M.loaded_segments (0x940b4 : word) = Some W_9406c.
Proof. vm_refl. Qed.
Lemma D_9406c : decode_any W_9406c = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_94070 : bv 32 := 0x00f56533.
Lemma F_94070 : fetch_word AsanUbsan.M.loaded_segments (0x940b8 : word) = Some W_94070.
Proof. vm_refl. Qed.
Lemma D_94070 : decode_any W_94070 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_94074 : bv 32 := 0x00855793.
Lemma F_94074 : fetch_word AsanUbsan.M.loaded_segments (0x940bc : word) = Some W_94074.
Proof. vm_refl. Qed.
Lemma D_94074 : decode_any W_94074 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94078 : bv 32 := 0x00f56533.
Lemma F_94078 : fetch_word AsanUbsan.M.loaded_segments (0x940c0 : word) = Some W_94078.
Proof. vm_refl. Qed.
Lemma D_94078 : decode_any W_94078 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9407c : bv 32 := 0x01055793.
Lemma F_9407c : fetch_word AsanUbsan.M.loaded_segments (0x940c4 : word) = Some W_9407c.
Proof. vm_refl. Qed.
Lemma D_9407c : decode_any W_9407c = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94080 : bv 32 := 0x00f56533.
Lemma F_94080 : fetch_word AsanUbsan.M.loaded_segments (0x940c8 : word) = Some W_94080.
Proof. vm_refl. Qed.
Lemma D_94080 : decode_any W_94080 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_94084 : bv 32 := 0x02055793.
Lemma F_94084 : fetch_word AsanUbsan.M.loaded_segments (0x940cc : word) = Some W_94084.
Proof. vm_refl. Qed.
Lemma D_94084 : decode_any W_94084 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94088 : bv 32 := 0x00f56533.
Lemma F_94088 : fetch_word AsanUbsan.M.loaded_segments (0x940d0 : word) = Some W_94088.
Proof. vm_refl. Qed.
Lemma D_94088 : decode_any W_94088 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9408c : bv 32 := 0xfff54513.
Lemma F_9408c : fetch_word AsanUbsan.M.loaded_segments (0x940d4 : word) = Some W_9408c.
Proof. vm_refl. Qed.
Lemma D_9408c : decode_any W_9408c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94090 : bv 32 := 0x00155793.
Lemma F_94090 : fetch_word AsanUbsan.M.loaded_segments (0x940d8 : word) = Some W_94090.
Proof. vm_refl. Qed.
Lemma D_94090 : decode_any W_94090 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_94094 : bv 32 := 0x00b7f5b3.
Lemma F_94094 : fetch_word AsanUbsan.M.loaded_segments (0x940dc : word) = Some W_94094.
Proof. vm_refl. Qed.
Lemma D_94094 : decode_any W_94094 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94098 : bv 32 := 0x40b50533.
Lemma F_94098 : fetch_word AsanUbsan.M.loaded_segments (0x940e0 : word) = Some W_94098.
Proof. vm_refl. Qed.
Lemma D_94098 : decode_any W_94098 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9409c : bv 32 := 0x00c575b3.
Lemma F_9409c : fetch_word AsanUbsan.M.loaded_segments (0x940e4 : word) = Some W_9409c.
Proof. vm_refl. Qed.
Lemma D_9409c : decode_any W_9409c = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_940a0 : bv 32 := 0x00255513.
Lemma F_940a0 : fetch_word AsanUbsan.M.loaded_segments (0x940e8 : word) = Some W_940a0.
Proof. vm_refl. Qed.
Lemma D_940a0 : decode_any W_940a0 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_940a4 : bv 32 := 0x00c57533.
Lemma F_940a4 : fetch_word AsanUbsan.M.loaded_segments (0x940ec : word) = Some W_940a4.
Proof. vm_refl. Qed.
Lemma D_940a4 : decode_any W_940a4 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_940a8 : bv 32 := 0x00a58533.
Lemma F_940a8 : fetch_word AsanUbsan.M.loaded_segments (0x940f0 : word) = Some W_940a8.
Proof. vm_refl. Qed.
Lemma D_940a8 : decode_any W_940a8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_940ac : bv 32 := 0x00455593.
Lemma F_940ac : fetch_word AsanUbsan.M.loaded_segments (0x940f4 : word) = Some W_940ac.
Proof. vm_refl. Qed.
Lemma D_940ac : decode_any W_940ac = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_940b0 : bv 32 := 0x00b50533.
Lemma F_940b0 : fetch_word AsanUbsan.M.loaded_segments (0x940f8 : word) = Some W_940b0.
Proof. vm_refl. Qed.
Lemma D_940b0 : decode_any W_940b0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_940b4 : bv 32 := 0x00d57533.
Lemma F_940b4 : fetch_word AsanUbsan.M.loaded_segments (0x940fc : word) = Some W_940b4.
Proof. vm_refl. Qed.
Lemma D_940b4 : decode_any W_940b4 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_940b8 : bv 32 := 0x02e50533.
Lemma F_940b8 : fetch_word AsanUbsan.M.loaded_segments (0x94100 : word) = Some W_940b8.
Proof. vm_refl. Qed.
Lemma D_940b8 : decode_any W_940b8 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_940bc : bv 32 := 0x03855513.
Lemma F_940bc : fetch_word AsanUbsan.M.loaded_segments (0x94104 : word) = Some W_940bc.
Proof. vm_refl. Qed.
Lemma D_940bc : decode_any W_940bc = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_940c0 : bv 32 := 0x40a0053b.
Lemma F_940c0 : fetch_word AsanUbsan.M.loaded_segments (0x94108 : word) = Some W_940c0.
Proof. vm_refl. Qed.
Lemma D_940c0 : decode_any W_940c0 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_940c4 : bv 32 := 0xfff00593.
Lemma F_940c4 : fetch_word AsanUbsan.M.loaded_segments (0x9410c : word) = Some W_940c4.
Proof. vm_refl. Qed.
Lemma D_940c4 : decode_any W_940c4 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_940c8 : bv 32 := 0x00a59533.
Lemma F_940c8 : fetch_word AsanUbsan.M.loaded_segments (0x94110 : word) = Some W_940c8.
Proof. vm_refl. Qed.
Lemma D_940c8 : decode_any W_940c8 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_940cc : bv 32 := 0xfff54513.
Lemma F_940cc : fetch_word AsanUbsan.M.loaded_segments (0x94114 : word) = Some W_940cc.
Proof. vm_refl. Qed.
Lemma D_940cc : decode_any W_940cc = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a24 : bv 32 := 0xfd010113.
Lemma F_94a24 : fetch_word AsanUbsan.M.loaded_segments (0x94a6c : word) = Some W_94a24.
Proof. vm_refl. Qed.
Lemma D_94a24 : decode_any W_94a24 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a28 : bv 32 := 0x02113423.
Lemma F_94a28 : fetch_word AsanUbsan.M.loaded_segments (0x94a70 : word) = Some W_94a28.
Proof. vm_refl. Qed.
Lemma D_94a28 : decode_any W_94a28 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a2c : bv 32 := 0x02813023.
Lemma F_94a2c : fetch_word AsanUbsan.M.loaded_segments (0x94a74 : word) = Some W_94a2c.
Proof. vm_refl. Qed.
Lemma D_94a2c : decode_any W_94a2c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a30 : bv 32 := 0x00913c23.
Lemma F_94a30 : fetch_word AsanUbsan.M.loaded_segments (0x94a78 : word) = Some W_94a30.
Proof. vm_refl. Qed.
Lemma D_94a30 : decode_any W_94a30 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a34 : bv 32 := 0x01213823.
Lemma F_94a34 : fetch_word AsanUbsan.M.loaded_segments (0x94a7c : word) = Some W_94a34.
Proof. vm_refl. Qed.
Lemma D_94a34 : decode_any W_94a34 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a38 : bv 32 := 0x02050e63.
Lemma F_94a38 : fetch_word AsanUbsan.M.loaded_segments (0x94a80 : word) = Some W_94a38.
Proof. vm_refl. Qed.
Lemma D_94a38 : decode_any W_94a38 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a3c : bv 32 := 0x00058413.
Lemma F_94a3c : fetch_word AsanUbsan.M.loaded_segments (0x94a84 : word) = Some W_94a3c.
Proof. vm_refl. Qed.
Lemma D_94a3c : decode_any W_94a3c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a40 : bv 32 := 0x02058a63.
Lemma F_94a40 : fetch_word AsanUbsan.M.loaded_segments (0x94a88 : word) = Some W_94a40.
Proof. vm_refl. Qed.
Lemma D_94a40 : decode_any W_94a40 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a44 : bv 32 := 0x00060493.
Lemma F_94a44 : fetch_word AsanUbsan.M.loaded_segments (0x94a8c : word) = Some W_94a44.
Proof. vm_refl. Qed.
Lemma D_94a44 : decode_any W_94a44 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a48 : bv 32 := 0x00050913.
Lemma F_94a48 : fetch_word AsanUbsan.M.loaded_segments (0x94a90 : word) = Some W_94a48.
Proof. vm_refl. Qed.
Lemma D_94a48 : decode_any W_94a48 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a4c : bv 32 := 0x00040593.
Lemma F_94a4c : fetch_word AsanUbsan.M.loaded_segments (0x94a94 : word) = Some W_94a4c.
Proof. vm_refl. Qed.
Lemma D_94a4c : decode_any W_94a4c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a50 : bv 32 := 0xf90fe0ef.
Lemma F_94a50 : fetch_word AsanUbsan.M.loaded_segments (0x94a98 : word) = Some W_94a50.
Proof. vm_refl. Qed.
Lemma D_94a50 : decode_any W_94a50 = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a54 : bv 32 := 0xaaaab5b7.
Lemma F_94a54 : fetch_word AsanUbsan.M.loaded_segments (0x94a9c : word) = Some W_94a54.
Proof. vm_refl. Qed.
Lemma D_94a54 : decode_any W_94a54 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a58 : bv 32 := 0xaaa58593.
Lemma F_94a58 : fetch_word AsanUbsan.M.loaded_segments (0x94aa0 : word) = Some W_94a58.
Proof. vm_refl. Qed.
Lemma D_94a58 : decode_any W_94a58 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a5c : bv 32 := 0x00b12623.
Lemma F_94a5c : fetch_word AsanUbsan.M.loaded_segments (0x94aa4 : word) = Some W_94a5c.
Proof. vm_refl. Qed.
Lemma D_94a5c : decode_any W_94a5c = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a60 : bv 32 := 0x00c10593.
Lemma F_94a60 : fetch_word AsanUbsan.M.loaded_segments (0x94aa8 : word) = Some W_94a60.
Proof. vm_refl. Qed.
Lemma D_94a60 : decode_any W_94a60 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a64 : bv 32 := 0xf50fe0ef.
Lemma F_94a64 : fetch_word AsanUbsan.M.loaded_segments (0x94aac : word) = Some W_94a64.
Proof. vm_refl. Qed.
Lemma D_94a64 : decode_any W_94a64 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a68 : bv 32 := 0x02051263.
Lemma F_94a68 : fetch_word AsanUbsan.M.loaded_segments (0x94ab0 : word) = Some W_94a68.
Proof. vm_refl. Qed.
Lemma D_94a68 : decode_any W_94a68 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a6c : bv 32 := 0x00040513.
Lemma F_94a6c : fetch_word AsanUbsan.M.loaded_segments (0x94ab4 : word) = Some W_94a6c.
Proof. vm_refl. Qed.
Lemma D_94a6c : decode_any W_94a6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a70 : bv 32 := 0xe70fa0ef.
Lemma F_94a70 : fetch_word AsanUbsan.M.loaded_segments (0x94ab8 : word) = Some W_94a70.
Proof. vm_refl. Qed.
Lemma D_94a70 : decode_any W_94a70 = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a74 : bv 32 := 0x02813083.
Lemma F_94a74 : fetch_word AsanUbsan.M.loaded_segments (0x94abc : word) = Some W_94a74.
Proof. vm_refl. Qed.
Lemma D_94a74 : decode_any W_94a74 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a78 : bv 32 := 0x02013403.
Lemma F_94a78 : fetch_word AsanUbsan.M.loaded_segments (0x94ac0 : word) = Some W_94a78.
Proof. vm_refl. Qed.
Lemma D_94a78 : decode_any W_94a78 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a7c : bv 32 := 0x01813483.
Lemma F_94a7c : fetch_word AsanUbsan.M.loaded_segments (0x94ac4 : word) = Some W_94a7c.
Proof. vm_refl. Qed.
Lemma D_94a7c : decode_any W_94a7c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a80 : bv 32 := 0x01013903.
Lemma F_94a80 : fetch_word AsanUbsan.M.loaded_segments (0x94ac8 : word) = Some W_94a80.
Proof. vm_refl. Qed.
Lemma D_94a80 : decode_any W_94a80 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a84 : bv 32 := 0x03010113.
Lemma F_94a84 : fetch_word AsanUbsan.M.loaded_segments (0x94acc : word) = Some W_94a84.
Proof. vm_refl. Qed.
Lemma D_94a84 : decode_any W_94a84 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a88 : bv 32 := 0x00008067.
Lemma F_94a88 : fetch_word AsanUbsan.M.loaded_segments (0x94ad0 : word) = Some W_94a88.
Proof. vm_refl. Qed.
Lemma D_94a88 : decode_any W_94a88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94aa0 : bv 32 := 0xfd010113.
Lemma F_94aa0 : fetch_word AsanUbsan.M.loaded_segments (0x94ae8 : word) = Some W_94aa0.
Proof. vm_refl. Qed.
Lemma D_94aa0 : decode_any W_94aa0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_94aa4 : bv 32 := 0x02113423.
Lemma F_94aa4 : fetch_word AsanUbsan.M.loaded_segments (0x94aec : word) = Some W_94aa4.
Proof. vm_refl. Qed.
Lemma D_94aa4 : decode_any W_94aa4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94aa8 : bv 32 := 0x02813023.
Lemma F_94aa8 : fetch_word AsanUbsan.M.loaded_segments (0x94af0 : word) = Some W_94aa8.
Proof. vm_refl. Qed.
Lemma D_94aa8 : decode_any W_94aa8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94aac : bv 32 := 0x00913c23.
Lemma F_94aac : fetch_word AsanUbsan.M.loaded_segments (0x94af4 : word) = Some W_94aac.
Proof. vm_refl. Qed.
Lemma D_94aac : decode_any W_94aac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ab0 : bv 32 := 0x01213823.
Lemma F_94ab0 : fetch_word AsanUbsan.M.loaded_segments (0x94af8 : word) = Some W_94ab0.
Proof. vm_refl. Qed.
Lemma D_94ab0 : decode_any W_94ab0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ab4 : bv 32 := 0x00058413.
Lemma F_94ab4 : fetch_word AsanUbsan.M.loaded_segments (0x94afc : word) = Some W_94ab4.
Proof. vm_refl. Qed.
Lemma D_94ab4 : decode_any W_94ab4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ab8 : bv 32 := 0x000c0597.
Lemma F_94ab8 : fetch_word AsanUbsan.M.loaded_segments (0x94b00 : word) = Some W_94ab8.
Proof. vm_refl. Qed.
Lemma D_94ab8 : decode_any W_94ab8 = Some (Auipc 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_94abc : bv 32 := 0x9e05b903.
Lemma F_94abc : fetch_word AsanUbsan.M.loaded_segments (0x94b04 : word) = Some W_94abc.
Proof. vm_refl. Qed.
Lemma D_94abc : decode_any W_94abc = Some (Load SZ8 true 18 11 2528, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ac0 : bv 32 := 0x00093583.
Lemma F_94ac0 : fetch_word AsanUbsan.M.loaded_segments (0x94b08 : word) = Some W_94ac0.
Proof. vm_refl. Qed.
Lemma D_94ac0 : decode_any W_94ac0 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ac4 : bv 32 := 0x00050493.
Lemma F_94ac4 : fetch_word AsanUbsan.M.loaded_segments (0x94b0c : word) = Some W_94ac4.
Proof. vm_refl. Qed.
Lemma D_94ac4 : decode_any W_94ac4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ac8 : bv 32 := 0x00059863.
Lemma F_94ac8 : fetch_word AsanUbsan.M.loaded_segments (0x94b10 : word) = Some W_94ac8.
Proof. vm_refl. Qed.
Lemma D_94ac8 : decode_any W_94ac8 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ad8 : bv 32 := 0xfff58513.
Lemma F_94ad8 : fetch_word AsanUbsan.M.loaded_segments (0x94b20 : word) = Some W_94ad8.
Proof. vm_refl. Qed.
Lemma D_94ad8 : decode_any W_94ad8 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94adc : bv 32 := 0x00a5f533.
Lemma F_94adc : fetch_word AsanUbsan.M.loaded_segments (0x94b24 : word) = Some W_94adc.
Proof. vm_refl. Qed.
Lemma D_94adc : decode_any W_94adc = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ae0 : bv 32 := 0x08051a63.
Lemma F_94ae0 : fetch_word AsanUbsan.M.loaded_segments (0x94b28 : word) = Some W_94ae0.
Proof. vm_refl. Qed.
Lemma D_94ae0 : decode_any W_94ae0 = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ae4 : bv 32 := 0x00b484b3.
Lemma F_94ae4 : fetch_word AsanUbsan.M.loaded_segments (0x94b2c : word) = Some W_94ae4.
Proof. vm_refl. Qed.
Lemma D_94ae4 : decode_any W_94ae4 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ae8 : bv 32 := 0x40b00533.
Lemma F_94ae8 : fetch_word AsanUbsan.M.loaded_segments (0x94b30 : word) = Some W_94ae8.
Proof. vm_refl. Qed.
Lemma D_94ae8 : decode_any W_94ae8 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94aec : bv 32 := 0xfff48493.
Lemma F_94aec : fetch_word AsanUbsan.M.loaded_segments (0x94b34 : word) = Some W_94aec.
Proof. vm_refl. Qed.
Lemma D_94aec : decode_any W_94aec = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94af0 : bv 32 := 0x00a4f4b3.
Lemma F_94af0 : fetch_word AsanUbsan.M.loaded_segments (0x94b38 : word) = Some W_94af0.
Proof. vm_refl. Qed.
Lemma D_94af0 : decode_any W_94af0 = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94af4 : bv 32 := 0x02200513.
Lemma F_94af4 : fetch_word AsanUbsan.M.loaded_segments (0x94b3c : word) = Some W_94af4.
Proof. vm_refl. Qed.
Lemma D_94af4 : decode_any W_94af4 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_94af8 : bv 32 := 0x00a12623.
Lemma F_94af8 : fetch_word AsanUbsan.M.loaded_segments (0x94b40 : word) = Some W_94af8.
Proof. vm_refl. Qed.
Lemma D_94af8 : decode_any W_94af8 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94afc : bv 32 := 0x00c10613.
Lemma F_94afc : fetch_word AsanUbsan.M.loaded_segments (0x94b44 : word) = Some W_94afc.
Proof. vm_refl. Qed.
Lemma D_94afc : decode_any W_94afc = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b00 : bv 32 := 0x00040513.
Lemma F_94b00 : fetch_word AsanUbsan.M.loaded_segments (0x94b48 : word) = Some W_94b00.
Proof. vm_refl. Qed.
Lemma D_94b00 : decode_any W_94b00 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b04 : bv 32 := 0x00048593.
Lemma F_94b04 : fetch_word AsanUbsan.M.loaded_segments (0x94b4c : word) = Some W_94b04.
Proof. vm_refl. Qed.
Lemma D_94b04 : decode_any W_94b04 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b08 : bv 32 := 0x279000ef.
Lemma F_94b08 : fetch_word AsanUbsan.M.loaded_segments (0x94b50 : word) = Some W_94b08.
Proof. vm_refl. Qed.
Lemma D_94b08 : decode_any W_94b08 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b0c : bv 32 := 0x00c12683.
Lemma F_94b0c : fetch_word AsanUbsan.M.loaded_segments (0x94b54 : word) = Some W_94b0c.
Proof. vm_refl. Qed.
Lemma D_94b0c : decode_any W_94b0c = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b10 : bv 32 := 0x00050713.
Lemma F_94b10 : fetch_word AsanUbsan.M.loaded_segments (0x94b58 : word) = Some W_94b10.
Proof. vm_refl. Qed.
Lemma D_94b10 : decode_any W_94b10 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b14 : bv 32 := 0x00300613.
Lemma F_94b14 : fetch_word AsanUbsan.M.loaded_segments (0x94b5c : word) = Some W_94b14.
Proof. vm_refl. Qed.
Lemma D_94b14 : decode_any W_94b14 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b18 : bv 32 := 0x00000513.
Lemma F_94b18 : fetch_word AsanUbsan.M.loaded_segments (0x94b60 : word) = Some W_94b18.
Proof. vm_refl. Qed.
Lemma D_94b18 : decode_any W_94b18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b1c : bv 32 := 0x00048593.
Lemma F_94b1c : fetch_word AsanUbsan.M.loaded_segments (0x94b64 : word) = Some W_94b1c.
Proof. vm_refl. Qed.
Lemma D_94b1c : decode_any W_94b1c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b20 : bv 32 := 0x00000793.
Lemma F_94b20 : fetch_word AsanUbsan.M.loaded_segments (0x94b68 : word) = Some W_94b20.
Proof. vm_refl. Qed.
Lemma D_94b20 : decode_any W_94b20 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b24 : bv 32 := 0xeb0fe0ef.
Lemma F_94b24 : fetch_word AsanUbsan.M.loaded_segments (0x94b6c : word) = Some W_94b24.
Proof. vm_refl. Qed.
Lemma D_94b24 : decode_any W_94b24 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b28 : bv 32 := 0x00050913.
Lemma F_94b28 : fetch_word AsanUbsan.M.loaded_segments (0x94b70 : word) = Some W_94b28.
Proof. vm_refl. Qed.
Lemma D_94b28 : decode_any W_94b28 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b2c : bv 32 := 0x00000593.
Lemma F_94b2c : fetch_word AsanUbsan.M.loaded_segments (0x94b74 : word) = Some W_94b2c.
Proof. vm_refl. Qed.
Lemma D_94b2c : decode_any W_94b2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b30 : bv 32 := 0xe84fe0ef.
Lemma F_94b30 : fetch_word AsanUbsan.M.loaded_segments (0x94b78 : word) = Some W_94b30.
Proof. vm_refl. Qed.
Lemma D_94b30 : decode_any W_94b30 = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b34 : bv 32 := 0xaaaab537.
Lemma F_94b34 : fetch_word AsanUbsan.M.loaded_segments (0x94b7c : word) = Some W_94b34.
Proof. vm_refl. Qed.
Lemma D_94b34 : decode_any W_94b34 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b38 : bv 32 := 0xaaa50513.
Lemma F_94b38 : fetch_word AsanUbsan.M.loaded_segments (0x94b80 : word) = Some W_94b38.
Proof. vm_refl. Qed.
Lemma D_94b38 : decode_any W_94b38 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b3c : bv 32 := 0x00a12423.
Lemma F_94b3c : fetch_word AsanUbsan.M.loaded_segments (0x94b84 : word) = Some W_94b3c.
Proof. vm_refl. Qed.
Lemma D_94b3c : decode_any W_94b3c = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b40 : bv 32 := 0x00810593.
Lemma F_94b40 : fetch_word AsanUbsan.M.loaded_segments (0x94b88 : word) = Some W_94b40.
Proof. vm_refl. Qed.
Lemma D_94b40 : decode_any W_94b40 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b44 : bv 32 := 0x00090513.
Lemma F_94b44 : fetch_word AsanUbsan.M.loaded_segments (0x94b8c : word) = Some W_94b44.
Proof. vm_refl. Qed.
Lemma D_94b44 : decode_any W_94b44 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b48 : bv 32 := 0xe6cfe0ef.
Lemma F_94b48 : fetch_word AsanUbsan.M.loaded_segments (0x94b90 : word) = Some W_94b48.
Proof. vm_refl. Qed.
Lemma D_94b48 : decode_any W_94b48 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b4c : bv 32 := 0x02051c63.
Lemma F_94b4c : fetch_word AsanUbsan.M.loaded_segments (0x94b94 : word) = Some W_94b4c.
Proof. vm_refl. Qed.
Lemma D_94b4c : decode_any W_94b4c = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b50 : bv 32 := 0x00048513.
Lemma F_94b50 : fetch_word AsanUbsan.M.loaded_segments (0x94b98 : word) = Some W_94b50.
Proof. vm_refl. Qed.
Lemma D_94b50 : decode_any W_94b50 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b54 : bv 32 := 0xd48fa0ef.
Lemma F_94b54 : fetch_word AsanUbsan.M.loaded_segments (0x94b9c : word) = Some W_94b54.
Proof. vm_refl. Qed.
Lemma D_94b54 : decode_any W_94b54 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b58 : bv 32 := 0x00090513.
Lemma F_94b58 : fetch_word AsanUbsan.M.loaded_segments (0x94ba0 : word) = Some W_94b58.
Proof. vm_refl. Qed.
Lemma D_94b58 : decode_any W_94b58 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b5c : bv 32 := 0x02813083.
Lemma F_94b5c : fetch_word AsanUbsan.M.loaded_segments (0x94ba4 : word) = Some W_94b5c.
Proof. vm_refl. Qed.
Lemma D_94b5c : decode_any W_94b5c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b60 : bv 32 := 0x02013403.
Lemma F_94b60 : fetch_word AsanUbsan.M.loaded_segments (0x94ba8 : word) = Some W_94b60.
Proof. vm_refl. Qed.
Lemma D_94b60 : decode_any W_94b60 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b64 : bv 32 := 0x01813483.
Lemma F_94b64 : fetch_word AsanUbsan.M.loaded_segments (0x94bac : word) = Some W_94b64.
Proof. vm_refl. Qed.
Lemma D_94b64 : decode_any W_94b64 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b68 : bv 32 := 0x01013903.
Lemma F_94b68 : fetch_word AsanUbsan.M.loaded_segments (0x94bb0 : word) = Some W_94b68.
Proof. vm_refl. Qed.
Lemma D_94b68 : decode_any W_94b68 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b6c : bv 32 := 0x03010113.
Lemma F_94b6c : fetch_word AsanUbsan.M.loaded_segments (0x94bb4 : word) = Some W_94b6c.
Proof. vm_refl. Qed.
Lemma D_94b6c : decode_any W_94b6c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b70 : bv 32 := 0x00008067.
Lemma F_94b70 : fetch_word AsanUbsan.M.loaded_segments (0x94bb8 : word) = Some W_94b70.
Proof. vm_refl. Qed.
Lemma D_94b70 : decode_any W_94b70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ee0 : bv 32 := 0x00060693.
Lemma F_94ee0 : fetch_word AsanUbsan.M.loaded_segments (0x94f28 : word) = Some W_94ee0.
Proof. vm_refl. Qed.
Lemma D_94ee0 : decode_any W_94ee0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ee4 : bv 32 := 0x00000613.
Lemma F_94ee4 : fetch_word AsanUbsan.M.loaded_segments (0x94f2c : word) = Some W_94ee4.
Proof. vm_refl. Qed.
Lemma D_94ee4 : decode_any W_94ee4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ee8 : bv 32 := 0x0040006f.
Lemma F_94ee8 : fetch_word AsanUbsan.M.loaded_segments (0x94f30 : word) = Some W_94ee8.
Proof. vm_refl. Qed.
Lemma D_94ee8 : decode_any W_94ee8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_94eec : bv 32 := 0xfa010113.
Lemma F_94eec : fetch_word AsanUbsan.M.loaded_segments (0x94f34 : word) = Some W_94eec.
Proof. vm_refl. Qed.
Lemma D_94eec : decode_any W_94eec = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ef0 : bv 32 := 0x04113c23.
Lemma F_94ef0 : fetch_word AsanUbsan.M.loaded_segments (0x94f38 : word) = Some W_94ef0.
Proof. vm_refl. Qed.
Lemma D_94ef0 : decode_any W_94ef0 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ef4 : bv 32 := 0x04813823.
Lemma F_94ef4 : fetch_word AsanUbsan.M.loaded_segments (0x94f3c : word) = Some W_94ef4.
Proof. vm_refl. Qed.
Lemma D_94ef4 : decode_any W_94ef4 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ef8 : bv 32 := 0x04913423.
Lemma F_94ef8 : fetch_word AsanUbsan.M.loaded_segments (0x94f40 : word) = Some W_94ef8.
Proof. vm_refl. Qed.
Lemma D_94ef8 : decode_any W_94ef8 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_94efc : bv 32 := 0x05213023.
Lemma F_94efc : fetch_word AsanUbsan.M.loaded_segments (0x94f44 : word) = Some W_94efc.
Proof. vm_refl. Qed.
Lemma D_94efc : decode_any W_94efc = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f00 : bv 32 := 0x03313c23.
Lemma F_94f00 : fetch_word AsanUbsan.M.loaded_segments (0x94f48 : word) = Some W_94f00.
Proof. vm_refl. Qed.
Lemma D_94f00 : decode_any W_94f00 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f04 : bv 32 := 0x03413823.
Lemma F_94f04 : fetch_word AsanUbsan.M.loaded_segments (0x94f4c : word) = Some W_94f04.
Proof. vm_refl. Qed.
Lemma D_94f04 : decode_any W_94f04 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f08 : bv 32 := 0x00068993.
Lemma F_94f08 : fetch_word AsanUbsan.M.loaded_segments (0x94f50 : word) = Some W_94f08.
Proof. vm_refl. Qed.
Lemma D_94f08 : decode_any W_94f08 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f0c : bv 32 := 0x00060493.
Lemma F_94f0c : fetch_word AsanUbsan.M.loaded_segments (0x94f54 : word) = Some W_94f0c.
Proof. vm_refl. Qed.
Lemma D_94f0c : decode_any W_94f0c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f10 : bv 32 := 0x00058413.
Lemma F_94f10 : fetch_word AsanUbsan.M.loaded_segments (0x94f58 : word) = Some W_94f10.
Proof. vm_refl. Qed.
Lemma D_94f10 : decode_any W_94f10 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f14 : bv 32 := 0x000bf597.
Lemma F_94f14 : fetch_word AsanUbsan.M.loaded_segments (0x94f5c : word) = Some W_94f14.
Proof. vm_refl. Qed.
Lemma D_94f14 : decode_any W_94f14 = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f18 : bv 32 := 0x5845ba03.
Lemma F_94f18 : fetch_word AsanUbsan.M.loaded_segments (0x94f60 : word) = Some W_94f18.
Proof. vm_refl. Qed.
Lemma D_94f18 : decode_any W_94f18 = Some (Load SZ8 true 20 11 1412, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f1c : bv 32 := 0x000a3583.
Lemma F_94f1c : fetch_word AsanUbsan.M.loaded_segments (0x94f64 : word) = Some W_94f1c.
Proof. vm_refl. Qed.
Lemma D_94f1c : decode_any W_94f1c = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f20 : bv 32 := 0x00050913.
Lemma F_94f20 : fetch_word AsanUbsan.M.loaded_segments (0x94f68 : word) = Some W_94f20.
Proof. vm_refl. Qed.
Lemma D_94f20 : decode_any W_94f20 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f24 : bv 32 := 0x00059863.
Lemma F_94f24 : fetch_word AsanUbsan.M.loaded_segments (0x94f6c : word) = Some W_94f24.
Proof. vm_refl. Qed.
Lemma D_94f24 : decode_any W_94f24 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f34 : bv 32 := 0xfff58513.
Lemma F_94f34 : fetch_word AsanUbsan.M.loaded_segments (0x94f7c : word) = Some W_94f34.
Proof. vm_refl. Qed.
Lemma D_94f34 : decode_any W_94f34 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f38 : bv 32 := 0x00a5f533.
Lemma F_94f38 : fetch_word AsanUbsan.M.loaded_segments (0x94f80 : word) = Some W_94f38.
Proof. vm_refl. Qed.
Lemma D_94f38 : decode_any W_94f38 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f3c : bv 32 := 0x0a051863.
Lemma F_94f3c : fetch_word AsanUbsan.M.loaded_segments (0x94f84 : word) = Some W_94f3c.
Proof. vm_refl. Qed.
Lemma D_94f3c : decode_any W_94f3c = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f40 : bv 32 := 0x00b40433.
Lemma F_94f40 : fetch_word AsanUbsan.M.loaded_segments (0x94f88 : word) = Some W_94f40.
Proof. vm_refl. Qed.
Lemma D_94f40 : decode_any W_94f40 = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f44 : bv 32 := 0xfff40413.
Lemma F_94f44 : fetch_word AsanUbsan.M.loaded_segments (0x94f8c : word) = Some W_94f44.
Proof. vm_refl. Qed.
Lemma D_94f44 : decode_any W_94f44 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f48 : bv 32 := 0x40b00533.
Lemma F_94f48 : fetch_word AsanUbsan.M.loaded_segments (0x94f90 : word) = Some W_94f48.
Proof. vm_refl. Qed.
Lemma D_94f48 : decode_any W_94f48 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f4c : bv 32 := 0x00a47433.
Lemma F_94f4c : fetch_word AsanUbsan.M.loaded_segments (0x94f94 : word) = Some W_94f4c.
Proof. vm_refl. Qed.
Lemma D_94f4c : decode_any W_94f4c = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f50 : bv 32 := 0x00059863.
Lemma F_94f50 : fetch_word AsanUbsan.M.loaded_segments (0x94f98 : word) = Some W_94f50.
Proof. vm_refl. Qed.
Lemma D_94f50 : decode_any W_94f50 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f60 : bv 32 := 0x00a97933.
Lemma F_94f60 : fetch_word AsanUbsan.M.loaded_segments (0x94fa8 : word) = Some W_94f60.
Proof. vm_refl. Qed.
Lemma D_94f60 : decode_any W_94f60 = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f64 : bv 32 := 0x03200513.
Lemma F_94f64 : fetch_word AsanUbsan.M.loaded_segments (0x94fac : word) = Some W_94f64.
Proof. vm_refl. Qed.
Lemma D_94f64 : decode_any W_94f64 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f68 : bv 32 := 0x00a12023.
Lemma F_94f68 : fetch_word AsanUbsan.M.loaded_segments (0x94fb0 : word) = Some W_94f68.
Proof. vm_refl. Qed.
Lemma D_94f68 : decode_any W_94f68 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f6c : bv 32 := 0x00010613.
Lemma F_94f6c : fetch_word AsanUbsan.M.loaded_segments (0x94fb4 : word) = Some W_94f6c.
Proof. vm_refl. Qed.
Lemma D_94f6c : decode_any W_94f6c = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f70 : bv 32 := 0x00098513.
Lemma F_94f70 : fetch_word AsanUbsan.M.loaded_segments (0x94fb8 : word) = Some W_94f70.
Proof. vm_refl. Qed.
Lemma D_94f70 : decode_any W_94f70 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f74 : bv 32 := 0x00040593.
Lemma F_94f74 : fetch_word AsanUbsan.M.loaded_segments (0x94fbc : word) = Some W_94f74.
Proof. vm_refl. Qed.
Lemma D_94f74 : decode_any W_94f74 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f78 : bv 32 := 0x608000ef.
Lemma F_94f78 : fetch_word AsanUbsan.M.loaded_segments (0x94fc0 : word) = Some W_94f78.
Proof. vm_refl. Qed.
Lemma D_94f78 : decode_any W_94f78 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f7c : bv 32 := 0x00012683.
Lemma F_94f7c : fetch_word AsanUbsan.M.loaded_segments (0x94fc4 : word) = Some W_94f7c.
Proof. vm_refl. Qed.
Lemma D_94f7c : decode_any W_94f7c = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f80 : bv 32 := 0x00050713.
Lemma F_94f80 : fetch_word AsanUbsan.M.loaded_segments (0x94fc8 : word) = Some W_94f80.
Proof. vm_refl. Qed.
Lemma D_94f80 : decode_any W_94f80 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f84 : bv 32 := 0x00300613.
Lemma F_94f84 : fetch_word AsanUbsan.M.loaded_segments (0x94fcc : word) = Some W_94f84.
Proof. vm_refl. Qed.
Lemma D_94f84 : decode_any W_94f84 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f88 : bv 32 := 0x00090513.
Lemma F_94f88 : fetch_word AsanUbsan.M.loaded_segments (0x94fd0 : word) = Some W_94f88.
Proof. vm_refl. Qed.
Lemma D_94f88 : decode_any W_94f88 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f8c : bv 32 := 0x00040593.
Lemma F_94f8c : fetch_word AsanUbsan.M.loaded_segments (0x94fd4 : word) = Some W_94f8c.
Proof. vm_refl. Qed.
Lemma D_94f8c : decode_any W_94f8c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f90 : bv 32 := 0x00000793.
Lemma F_94f90 : fetch_word AsanUbsan.M.loaded_segments (0x94fd8 : word) = Some W_94f90.
Proof. vm_refl. Qed.
Lemma D_94f90 : decode_any W_94f90 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f94 : bv 32 := 0xa40fe0ef.
Lemma F_94f94 : fetch_word AsanUbsan.M.loaded_segments (0x94fdc : word) = Some W_94f94.
Proof. vm_refl. Qed.
Lemma D_94f94 : decode_any W_94f94 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f98 : bv 32 := 0x00050993.
Lemma F_94f98 : fetch_word AsanUbsan.M.loaded_segments (0x94fe0 : word) = Some W_94f98.
Proof. vm_refl. Qed.
Lemma D_94f98 : decode_any W_94f98 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f9c : bv 32 := 0x00000593.
Lemma F_94f9c : fetch_word AsanUbsan.M.loaded_segments (0x94fe4 : word) = Some W_94f9c.
Proof. vm_refl. Qed.
Lemma D_94f9c : decode_any W_94f9c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fa0 : bv 32 := 0xa14fe0ef.
Lemma F_94fa0 : fetch_word AsanUbsan.M.loaded_segments (0x94fe8 : word) = Some W_94fa0.
Proof. vm_refl. Qed.
Lemma D_94fa0 : decode_any W_94fa0 = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fa4 : bv 32 := 0xaaaab537.
Lemma F_94fa4 : fetch_word AsanUbsan.M.loaded_segments (0x94fec : word) = Some W_94fa4.
Proof. vm_refl. Qed.
Lemma D_94fa4 : decode_any W_94fa4 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fa8 : bv 32 := 0xaaa50513.
Lemma F_94fa8 : fetch_word AsanUbsan.M.loaded_segments (0x94ff0 : word) = Some W_94fa8.
Proof. vm_refl. Qed.
Lemma D_94fa8 : decode_any W_94fa8 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fac : bv 32 := 0x02a12623.
Lemma F_94fac : fetch_word AsanUbsan.M.loaded_segments (0x94ff4 : word) = Some W_94fac.
Proof. vm_refl. Qed.
Lemma D_94fac : decode_any W_94fac = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fb0 : bv 32 := 0x02c10593.
Lemma F_94fb0 : fetch_word AsanUbsan.M.loaded_segments (0x94ff8 : word) = Some W_94fb0.
Proof. vm_refl. Qed.
Lemma D_94fb0 : decode_any W_94fb0 = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fb4 : bv 32 := 0x00098513.
Lemma F_94fb4 : fetch_word AsanUbsan.M.loaded_segments (0x94ffc : word) = Some W_94fb4.
Proof. vm_refl. Qed.
Lemma D_94fb4 : decode_any W_94fb4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fb8 : bv 32 := 0x9fcfe0ef.
Lemma F_94fb8 : fetch_word AsanUbsan.M.loaded_segments (0x95000 : word) = Some W_94fb8.
Proof. vm_refl. Qed.
Lemma D_94fb8 : decode_any W_94fb8 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fbc : bv 32 := 0x04051063.
Lemma F_94fbc : fetch_word AsanUbsan.M.loaded_segments (0x95004 : word) = Some W_94fbc.
Proof. vm_refl. Qed.
Lemma D_94fbc : decode_any W_94fbc = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fc0 : bv 32 := 0x00040513.
Lemma F_94fc0 : fetch_word AsanUbsan.M.loaded_segments (0x95008 : word) = Some W_94fc0.
Proof. vm_refl. Qed.
Lemma D_94fc0 : decode_any W_94fc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fc4 : bv 32 := 0x8d8fa0ef.
Lemma F_94fc4 : fetch_word AsanUbsan.M.loaded_segments (0x9500c : word) = Some W_94fc4.
Proof. vm_refl. Qed.
Lemma D_94fc4 : decode_any W_94fc4 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fc8 : bv 32 := 0x00098513.
Lemma F_94fc8 : fetch_word AsanUbsan.M.loaded_segments (0x95010 : word) = Some W_94fc8.
Proof. vm_refl. Qed.
Lemma D_94fc8 : decode_any W_94fc8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fcc : bv 32 := 0x05813083.
Lemma F_94fcc : fetch_word AsanUbsan.M.loaded_segments (0x95014 : word) = Some W_94fcc.
Proof. vm_refl. Qed.
Lemma D_94fcc : decode_any W_94fcc = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fd0 : bv 32 := 0x05013403.
Lemma F_94fd0 : fetch_word AsanUbsan.M.loaded_segments (0x95018 : word) = Some W_94fd0.
Proof. vm_refl. Qed.
Lemma D_94fd0 : decode_any W_94fd0 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fd4 : bv 32 := 0x04813483.
Lemma F_94fd4 : fetch_word AsanUbsan.M.loaded_segments (0x9501c : word) = Some W_94fd4.
Proof. vm_refl. Qed.
Lemma D_94fd4 : decode_any W_94fd4 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fd8 : bv 32 := 0x04013903.
Lemma F_94fd8 : fetch_word AsanUbsan.M.loaded_segments (0x95020 : word) = Some W_94fd8.
Proof. vm_refl. Qed.
Lemma D_94fd8 : decode_any W_94fd8 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fdc : bv 32 := 0x03813983.
Lemma F_94fdc : fetch_word AsanUbsan.M.loaded_segments (0x95024 : word) = Some W_94fdc.
Proof. vm_refl. Qed.
Lemma D_94fdc : decode_any W_94fdc = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fe0 : bv 32 := 0x03013a03.
Lemma F_94fe0 : fetch_word AsanUbsan.M.loaded_segments (0x95028 : word) = Some W_94fe0.
Proof. vm_refl. Qed.
Lemma D_94fe0 : decode_any W_94fe0 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fe4 : bv 32 := 0x06010113.
Lemma F_94fe4 : fetch_word AsanUbsan.M.loaded_segments (0x9502c : word) = Some W_94fe4.
Proof. vm_refl. Qed.
Lemma D_94fe4 : decode_any W_94fe4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_94fe8 : bv 32 := 0x00008067.
Lemma F_94fe8 : fetch_word AsanUbsan.M.loaded_segments (0x95030 : word) = Some W_94fe8.
Proof. vm_refl. Qed.
Lemma D_94fe8 : decode_any W_94fe8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

