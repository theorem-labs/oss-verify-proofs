(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_77178 : bv 32 := 0xf7010113.
Lemma F_77178 : fetch_word AsanUbsan.M.loaded_segments (0x77178 : word) = Some W_77178.
Proof. vm_refl. Qed.
Lemma D_77178 : decode_any W_77178 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7717c : bv 32 := 0x08113423.
Lemma F_7717c : fetch_word AsanUbsan.M.loaded_segments (0x7717c : word) = Some W_7717c.
Proof. vm_refl. Qed.
Lemma D_7717c : decode_any W_7717c = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_77180 : bv 32 := 0x08813023.
Lemma F_77180 : fetch_word AsanUbsan.M.loaded_segments (0x77180 : word) = Some W_77180.
Proof. vm_refl. Qed.
Lemma D_77180 : decode_any W_77180 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_77184 : bv 32 := 0x06913c23.
Lemma F_77184 : fetch_word AsanUbsan.M.loaded_segments (0x77184 : word) = Some W_77184.
Proof. vm_refl. Qed.
Lemma D_77184 : decode_any W_77184 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_77188 : bv 32 := 0x07213823.
Lemma F_77188 : fetch_word AsanUbsan.M.loaded_segments (0x77188 : word) = Some W_77188.
Proof. vm_refl. Qed.
Lemma D_77188 : decode_any W_77188 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7718c : bv 32 := 0x07313423.
Lemma F_7718c : fetch_word AsanUbsan.M.loaded_segments (0x7718c : word) = Some W_7718c.
Proof. vm_refl. Qed.
Lemma D_7718c : decode_any W_7718c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_77190 : bv 32 := 0x07413023.
Lemma F_77190 : fetch_word AsanUbsan.M.loaded_segments (0x77190 : word) = Some W_77190.
Proof. vm_refl. Qed.
Lemma D_77190 : decode_any W_77190 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_77194 : bv 32 := 0x05513c23.
Lemma F_77194 : fetch_word AsanUbsan.M.loaded_segments (0x77194 : word) = Some W_77194.
Proof. vm_refl. Qed.
Lemma D_77194 : decode_any W_77194 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_77198 : bv 32 := 0x05613823.
Lemma F_77198 : fetch_word AsanUbsan.M.loaded_segments (0x77198 : word) = Some W_77198.
Proof. vm_refl. Qed.
Lemma D_77198 : decode_any W_77198 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7719c : bv 32 := 0x05713423.
Lemma F_7719c : fetch_word AsanUbsan.M.loaded_segments (0x7719c : word) = Some W_7719c.
Proof. vm_refl. Qed.
Lemma D_7719c : decode_any W_7719c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_771a0 : bv 32 := 0x05813023.
Lemma F_771a0 : fetch_word AsanUbsan.M.loaded_segments (0x771a0 : word) = Some W_771a0.
Proof. vm_refl. Qed.
Lemma D_771a0 : decode_any W_771a0 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_771a4 : bv 32 := 0x03913c23.
Lemma F_771a4 : fetch_word AsanUbsan.M.loaded_segments (0x771a4 : word) = Some W_771a4.
Proof. vm_refl. Qed.
Lemma D_771a4 : decode_any W_771a4 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_771a8 : bv 32 := 0x03a13823.
Lemma F_771a8 : fetch_word AsanUbsan.M.loaded_segments (0x771a8 : word) = Some W_771a8.
Proof. vm_refl. Qed.
Lemma D_771a8 : decode_any W_771a8 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_771ac : bv 32 := 0x03b13423.
Lemma F_771ac : fetch_word AsanUbsan.M.loaded_segments (0x771ac : word) = Some W_771ac.
Proof. vm_refl. Qed.
Lemma D_771ac : decode_any W_771ac = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_771b0 : bv 32 := 0x00058913.
Lemma F_771b0 : fetch_word AsanUbsan.M.loaded_segments (0x771b0 : word) = Some W_771b0.
Proof. vm_refl. Qed.
Lemma D_771b0 : decode_any W_771b0 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771b4 : bv 32 := 0x0005f597.
Lemma F_771b4 : fetch_word AsanUbsan.M.loaded_segments (0x771b4 : word) = Some W_771b4.
Proof. vm_refl. Qed.
Lemma D_771b4 : decode_any W_771b4 = Some (Auipc 11 95, 4%Z).
Proof. vm_refl. Qed.

Definition W_771b8 : bv 32 := 0x3045b583.
Lemma F_771b8 : fetch_word AsanUbsan.M.loaded_segments (0x771b8 : word) = Some W_771b8.
Proof. vm_refl. Qed.
Lemma D_771b8 : decode_any W_771b8 = Some (Load SZ8 true 11 11 772, 4%Z).
Proof. vm_refl. Qed.

Definition W_771bc : bv 32 := 0x0895c583.
Lemma F_771bc : fetch_word AsanUbsan.M.loaded_segments (0x771bc : word) = Some W_771bc.
Proof. vm_refl. Qed.
Lemma D_771bc : decode_any W_771bc = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_771c0 : bv 32 := 0x18058a63.
Lemma F_771c0 : fetch_word AsanUbsan.M.loaded_segments (0x771c0 : word) = Some W_771c0.
Proof. vm_refl. Qed.
Lemma D_771c0 : decode_any W_771c0 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_771c4 : bv 32 := 0x00050993.
Lemma F_771c4 : fetch_word AsanUbsan.M.loaded_segments (0x771c4 : word) = Some W_771c4.
Proof. vm_refl. Qed.
Lemma D_771c4 : decode_any W_771c4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771c8 : bv 32 := 0x0005f517.
Lemma F_771c8 : fetch_word AsanUbsan.M.loaded_segments (0x771c8 : word) = Some W_771c8.
Proof. vm_refl. Qed.
Lemma D_771c8 : decode_any W_771c8 = Some (Auipc 10 95, 4%Z).
Proof. vm_refl. Qed.

Definition W_771cc : bv 32 := 0x35053d03.
Lemma F_771cc : fetch_word AsanUbsan.M.loaded_segments (0x771cc : word) = Some W_771cc.
Proof. vm_refl. Qed.
Lemma D_771cc : decode_any W_771cc = Some (Load SZ8 true 26 10 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_771d0 : bv 32 := 0x0009ba03.
Lemma F_771d0 : fetch_word AsanUbsan.M.loaded_segments (0x771d0 : word) = Some W_771d0.
Proof. vm_refl. Qed.
Lemma D_771d0 : decode_any W_771d0 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771d4 : bv 32 := 0x00060517.
Lemma F_771d4 : fetch_word AsanUbsan.M.loaded_segments (0x771d4 : word) = Some W_771d4.
Proof. vm_refl. Qed.
Lemma D_771d4 : decode_any W_771d4 = Some (Auipc 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_771d8 : bv 32 := 0x000d2583.
Lemma F_771d8 : fetch_word AsanUbsan.M.loaded_segments (0x771d8 : word) = Some W_771d8.
Proof. vm_refl. Qed.
Lemma D_771d8 : decode_any W_771d8 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771dc : bv 32 := 0x0bc53a83.
Lemma F_771dc : fetch_word AsanUbsan.M.loaded_segments (0x771dc : word) = Some W_771dc.
Proof. vm_refl. Qed.
Lemma D_771dc : decode_any W_771dc = Some (Load SZ8 true 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_771e0 : bv 32 := 0x00300513.
Lemma F_771e0 : fetch_word AsanUbsan.M.loaded_segments (0x771e0 : word) = Some W_771e0.
Proof. vm_refl. Qed.
Lemma D_771e0 : decode_any W_771e0 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_771e4 : bv 32 := 0x004a8ab3.
Lemma F_771e4 : fetch_word AsanUbsan.M.loaded_segments (0x771e4 : word) = Some W_771e4.
Proof. vm_refl. Qed.
Lemma D_771e4 : decode_any W_771e4 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_771e8 : bv 32 := 0x1ea5fa63.
Lemma F_771e8 : fetch_word AsanUbsan.M.loaded_segments (0x771e8 : word) = Some W_771e8.
Proof. vm_refl. Qed.
Lemma D_771e8 : decode_any W_771e8 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_771ec : bv 32 := 0x000abb03.
Lemma F_771ec : fetch_word AsanUbsan.M.loaded_segments (0x771ec : word) = Some W_771ec.
Proof. vm_refl. Qed.
Lemma D_771ec : decode_any W_771ec = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771f0 : bv 32 := 0xfff00513.
Lemma F_771f0 : fetch_word AsanUbsan.M.loaded_segments (0x771f0 : word) = Some W_771f0.
Proof. vm_refl. Qed.
Lemma D_771f0 : decode_any W_771f0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_771f4 : bv 32 := 0x0230000f.
Lemma F_771f4 : fetch_word AsanUbsan.M.loaded_segments (0x771f4 : word) = Some W_771f4.
Proof. vm_refl. Qed.
Lemma D_771f4 : decode_any W_771f4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771f8 : bv 32 := 0x14ab0e63.
Lemma F_771f8 : fetch_word AsanUbsan.M.loaded_segments (0x771f8 : word) = Some W_771f8.
Proof. vm_refl. Qed.
Lemma D_771f8 : decode_any W_771f8 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_771fc : bv 32 := 0x080b1263.
Lemma F_771fc : fetch_word AsanUbsan.M.loaded_segments (0x771fc : word) = Some W_771fc.
Proof. vm_refl. Qed.
Lemma D_771fc : decode_any W_771fc = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_77200 : bv 32 := 0x00060c13.
Lemma F_77200 : fetch_word AsanUbsan.M.loaded_segments (0x77200 : word) = Some W_77200.
Proof. vm_refl. Qed.
Lemma D_77200 : decode_any W_77200 = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77204 : bv 32 := 0x00068493.
Lemma F_77204 : fetch_word AsanUbsan.M.loaded_segments (0x77204 : word) = Some W_77204.
Proof. vm_refl. Qed.
Lemma D_77204 : decode_any W_77204 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77208 : bv 32 := 0xfff9d517.
Lemma F_77208 : fetch_word AsanUbsan.M.loaded_segments (0x77208 : word) = Some W_77208.
Proof. vm_refl. Qed.
Lemma D_77208 : decode_any W_77208 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7720c : bv 32 := 0x00001bb7.
Lemma F_7720c : fetch_word AsanUbsan.M.loaded_segments (0x7720c : word) = Some W_7720c.
Proof. vm_refl. Qed.
Lemma D_7720c : decode_any W_7720c = Some (Lui 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_77210 : bv 32 := 0xd8e50593.
Lemma F_77210 : fetch_word AsanUbsan.M.loaded_segments (0x77210 : word) = Some W_77210.
Proof. vm_refl. Qed.
Lemma D_77210 : decode_any W_77210 = Some (OpImm ALU_ADD 11 10 3470, 4%Z).
Proof. vm_refl. Qed.

Definition W_77214 : bv 32 := 0xff8b8b9b.
Lemma F_77214 : fetch_word AsanUbsan.M.loaded_segments (0x77214 : word) = Some W_77214.
Proof. vm_refl. Qed.
Lemma D_77214 : decode_any W_77214 = Some (OpImm32 23 23 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_77218 : bv 32 := 0x000b8513.
Lemma F_77218 : fetch_word AsanUbsan.M.loaded_segments (0x77218 : word) = Some W_77218.
Proof. vm_refl. Qed.
Lemma D_77218 : decode_any W_77218 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7721c : bv 32 := 0x00000613.
Lemma F_7721c : fetch_word AsanUbsan.M.loaded_segments (0x7721c : word) = Some W_7721c.
Proof. vm_refl. Qed.
Lemma D_7721c : decode_any W_7721c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77220 : bv 32 := 0xa90fc0ef.
Lemma F_77220 : fetch_word AsanUbsan.M.loaded_segments (0x77220 : word) = Some W_77220.
Proof. vm_refl. Qed.
Lemma D_77220 : decode_any W_77220 = Some (Jal 1 2081424, 4%Z).
Proof. vm_refl. Qed.

Definition W_77224 : bv 32 := 0x00050b13.
Lemma F_77224 : fetch_word AsanUbsan.M.loaded_segments (0x77224 : word) = Some W_77224.
Proof. vm_refl. Qed.
Lemma D_77224 : decode_any W_77224 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77228 : bv 32 := 0x160ab42f.
Lemma F_77228 : fetch_word AsanUbsan.M.loaded_segments (0x77228 : word) = Some W_77228.
Proof. vm_refl. Qed.
Lemma D_77228 : decode_any W_77228 = Some (Lr AD true true 8 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7722c : bv 32 := 0x02041c63.
Lemma F_7722c : fetch_word AsanUbsan.M.loaded_segments (0x7722c : word) = Some W_7722c.
Proof. vm_refl. Qed.
Lemma D_7722c : decode_any W_7722c = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_77230 : bv 32 := 0x1b6ab52f.
Lemma F_77230 : fetch_word AsanUbsan.M.loaded_segments (0x77230 : word) = Some W_77230.
Proof. vm_refl. Qed.
Lemma D_77230 : decode_any W_77230 = Some (Sc AD false true 10 21 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_77234 : bv 32 := 0xfe051ae3.
Lemma F_77234 : fetch_word AsanUbsan.M.loaded_segments (0x77234 : word) = Some W_77234.
Proof. vm_refl. Qed.
Lemma D_77234 : decode_any W_77234 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_77238 : bv 32 := 0x000f9517.
Lemma F_77238 : fetch_word AsanUbsan.M.loaded_segments (0x77238 : word) = Some W_77238.
Proof. vm_refl. Qed.
Lemma D_77238 : decode_any W_77238 = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_7723c : bv 32 := 0x24050513.
Lemma F_7723c : fetch_word AsanUbsan.M.loaded_segments (0x7723c : word) = Some W_7723c.
Proof. vm_refl. Qed.
Lemma D_7723c : decode_any W_7723c = Some (OpImm ALU_ADD 10 10 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_77240 : bv 32 := 0x00100593.
Lemma F_77240 : fetch_word AsanUbsan.M.loaded_segments (0x77240 : word) = Some W_77240.
Proof. vm_refl. Qed.
Lemma D_77240 : decode_any W_77240 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_77244 : bv 32 := 0x00b5362f.
Lemma F_77244 : fetch_word AsanUbsan.M.loaded_segments (0x77244 : word) = Some W_77244.
Proof. vm_refl. Qed.
Lemma D_77244 : decode_any W_77244 = Some (Amo AMO_ADD AD false false 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_77248 : bv 32 := 0x000d2503.
Lemma F_77248 : fetch_word AsanUbsan.M.loaded_segments (0x77248 : word) = Some W_77248.
Proof. vm_refl. Qed.
Lemma D_77248 : decode_any W_77248 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7724c : bv 32 := 0x02a5f663.
Lemma F_7724c : fetch_word AsanUbsan.M.loaded_segments (0x7724c : word) = Some W_7724c.
Proof. vm_refl. Qed.
Lemma D_7724c : decode_any W_7724c = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_77250 : bv 32 := 0xfff9d517.
Lemma F_77250 : fetch_word AsanUbsan.M.loaded_segments (0x77250 : word) = Some W_77250.
Proof. vm_refl. Qed.
Lemma D_77250 : decode_any W_77250 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_77254 : bv 32 := 0xd5550513.
Lemma F_77254 : fetch_word AsanUbsan.M.loaded_segments (0x77254 : word) = Some W_77254.
Proof. vm_refl. Qed.
Lemma D_77254 : decode_any W_77254 = Some (OpImm ALU_ADD 10 10 3413, 4%Z).
Proof. vm_refl. Qed.

Definition W_77258 : bv 32 := 0x000a8593.
Lemma F_77258 : fetch_word AsanUbsan.M.loaded_segments (0x77258 : word) = Some W_77258.
Proof. vm_refl. Qed.
Lemma D_77258 : decode_any W_77258 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7725c : bv 32 := 0xfacfd0ef.
Lemma F_7725c : fetch_word AsanUbsan.M.loaded_segments (0x7725c : word) = Some W_7725c.
Proof. vm_refl. Qed.
Lemma D_7725c : decode_any W_7725c = Some (Jal 1 2086828, 4%Z).
Proof. vm_refl. Qed.

Definition W_77260 : bv 32 := 0x0180006f.
Lemma F_77260 : fetch_word AsanUbsan.M.loaded_segments (0x77260 : word) = Some W_77260.
Proof. vm_refl. Qed.
Lemma D_77260 : decode_any W_77260 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_77264 : bv 32 := 0x000b0513.
Lemma F_77264 : fetch_word AsanUbsan.M.loaded_segments (0x77264 : word) = Some W_77264.
Proof. vm_refl. Qed.
Lemma D_77264 : decode_any W_77264 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77268 : bv 32 := 0x000b8593.
Lemma F_77268 : fetch_word AsanUbsan.M.loaded_segments (0x77268 : word) = Some W_77268.
Proof. vm_refl. Qed.
Lemma D_77268 : decode_any W_77268 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7726c : bv 32 := 0x00000613.
Lemma F_7726c : fetch_word AsanUbsan.M.loaded_segments (0x7726c : word) = Some W_7726c.
Proof. vm_refl. Qed.
Lemma D_7726c : decode_any W_7726c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77270 : bv 32 := 0xbc0fc0ef.
Lemma F_77270 : fetch_word AsanUbsan.M.loaded_segments (0x77270 : word) = Some W_77270.
Proof. vm_refl. Qed.
Lemma D_77270 : decode_any W_77270 = Some (Jal 1 2081728, 4%Z).
Proof. vm_refl. Qed.

Definition W_77274 : bv 32 := 0x00040b13.
Lemma F_77274 : fetch_word AsanUbsan.M.loaded_segments (0x77274 : word) = Some W_77274.
Proof. vm_refl. Qed.
Lemma D_77274 : decode_any W_77274 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77278 : bv 32 := 0x00048693.
Lemma F_77278 : fetch_word AsanUbsan.M.loaded_segments (0x77278 : word) = Some W_77278.
Proof. vm_refl. Qed.
Lemma D_77278 : decode_any W_77278 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7727c : bv 32 := 0x000c0613.
Lemma F_7727c : fetch_word AsanUbsan.M.loaded_segments (0x7727c : word) = Some W_7727c.
Proof. vm_refl. Qed.
Lemma D_7727c : decode_any W_7727c = Some (OpImm ALU_ADD 12 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77280 : bv 32 := 0x0c0b0a63.
Lemma F_77280 : fetch_word AsanUbsan.M.loaded_segments (0x77280 : word) = Some W_77280.
Proof. vm_refl. Qed.
Lemma D_77280 : decode_any W_77280 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_77284 : bv 32 := 0x00c13823.
Lemma F_77284 : fetch_word AsanUbsan.M.loaded_segments (0x77284 : word) = Some W_77284.
Proof. vm_refl. Qed.
Lemma D_77284 : decode_any W_77284 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_77288 : bv 32 := 0x00d13c23.
Lemma F_77288 : fetch_word AsanUbsan.M.loaded_segments (0x77288 : word) = Some W_77288.
Proof. vm_refl. Qed.
Lemma D_77288 : decode_any W_77288 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7728c : bv 32 := 0x0ff00513.
Lemma F_7728c : fetch_word AsanUbsan.M.loaded_segments (0x7728c : word) = Some W_7728c.
Proof. vm_refl. Qed.
Lemma D_7728c : decode_any W_7728c = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_77290 : bv 32 := 0x0aaa6863.
Lemma F_77290 : fetch_word AsanUbsan.M.loaded_segments (0x77290 : word) = Some W_77290.
Proof. vm_refl. Qed.
Lemma D_77290 : decode_any W_77290 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_77294 : bv 32 := 0xfff00d93.
Lemma F_77294 : fetch_word AsanUbsan.M.loaded_segments (0x77294 : word) = Some W_77294.
Proof. vm_refl. Qed.
Lemma D_77294 : decode_any W_77294 = Some (OpImm ALU_ADD 27 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_77298 : bv 32 := 0x0fe00c93.
Lemma F_77298 : fetch_word AsanUbsan.M.loaded_segments (0x77298 : word) = Some W_77298.
Proof. vm_refl. Qed.
Lemma D_77298 : decode_any W_77298 = Some (OpImm ALU_ADD 25 0 254, 4%Z).
Proof. vm_refl. Qed.

Definition W_7729c : bv 32 := 0xfff9d517.
Lemma F_7729c : fetch_word AsanUbsan.M.loaded_segments (0x7729c : word) = Some W_7729c.
Proof. vm_refl. Qed.
Lemma D_7729c : decode_any W_7729c = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_772a0 : bv 32 := 0x00001c37.
Lemma F_772a0 : fetch_word AsanUbsan.M.loaded_segments (0x772a0 : word) = Some W_772a0.
Proof. vm_refl. Qed.
Lemma D_772a0 : decode_any W_772a0 = Some (Lui 24 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_772a4 : bv 32 := 0x000f9597.
Lemma F_772a4 : fetch_word AsanUbsan.M.loaded_segments (0x772a4 : word) = Some W_772a4.
Proof. vm_refl. Qed.
Lemma D_772a4 : decode_any W_772a4 = Some (Auipc 11 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_772a8 : bv 32 := 0xfff9d617.
Lemma F_772a8 : fetch_word AsanUbsan.M.loaded_segments (0x772a8 : word) = Some W_772a8.
Proof. vm_refl. Qed.
Lemma D_772a8 : decode_any W_772a8 = Some (Auipc 12 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_772ac : bv 32 := 0xcfa50b93.
Lemma F_772ac : fetch_word AsanUbsan.M.loaded_segments (0x772ac : word) = Some W_772ac.
Proof. vm_refl. Qed.
Lemma D_772ac : decode_any W_772ac = Some (OpImm ALU_ADD 23 10 3322, 4%Z).
Proof. vm_refl. Qed.

Definition W_772b0 : bv 32 := 0xff8c0c1b.
Lemma F_772b0 : fetch_word AsanUbsan.M.loaded_segments (0x772b0 : word) = Some W_772b0.
Proof. vm_refl. Qed.
Lemma D_772b0 : decode_any W_772b0 = Some (OpImm32 24 24 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_772b4 : bv 32 := 0x1d458413.
Lemma F_772b4 : fetch_word AsanUbsan.M.loaded_segments (0x772b4 : word) = Some W_772b4.
Proof. vm_refl. Qed.
Lemma D_772b4 : decode_any W_772b4 = Some (OpImm ALU_ADD 8 11 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_772b8 : bv 32 := 0xcfd60513.
Lemma F_772b8 : fetch_word AsanUbsan.M.loaded_segments (0x772b8 : word) = Some W_772b8.
Proof. vm_refl. Qed.
Lemma D_772b8 : decode_any W_772b8 = Some (OpImm ALU_ADD 10 12 3325, 4%Z).
Proof. vm_refl. Qed.

Definition W_772bc : bv 32 := 0x00a13423.
Lemma F_772bc : fetch_word AsanUbsan.M.loaded_segments (0x772bc : word) = Some W_772bc.
Proof. vm_refl. Qed.
Lemma D_772bc : decode_any W_772bc = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_772c0 : bv 32 := 0x0140006f.
Lemma F_772c0 : fetch_word AsanUbsan.M.loaded_segments (0x772c0 : word) = Some W_772c0.
Proof. vm_refl. Qed.
Lemma D_772c0 : decode_any W_772c0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_772c4 : bv 32 := 0x00000513.
Lemma F_772c4 : fetch_word AsanUbsan.M.loaded_segments (0x772c4 : word) = Some W_772c4.
Proof. vm_refl. Qed.
Lemma D_772c4 : decode_any W_772c4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772c8 : bv 32 := 0xf01a0a13.
Lemma F_772c8 : fetch_word AsanUbsan.M.loaded_segments (0x772c8 : word) = Some W_772c8.
Proof. vm_refl. Qed.
Lemma D_772c8 : decode_any W_772c8 = Some (OpImm ALU_ADD 20 20 3841, 4%Z).
Proof. vm_refl. Qed.

Definition W_772cc : bv 32 := 0x00050b13.
Lemma F_772cc : fetch_word AsanUbsan.M.loaded_segments (0x772cc : word) = Some W_772cc.
Proof. vm_refl. Qed.
Lemma D_772cc : decode_any W_772cc = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772d0 : bv 32 := 0x074cfa63.
Lemma F_772d0 : fetch_word AsanUbsan.M.loaded_segments (0x772d0 : word) = Some W_772d0.
Proof. vm_refl. Qed.
Lemma D_772d0 : decode_any W_772d0 = Some (Branch BC_GEU 25 20 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_772d4 : bv 32 := 0x000b3503.
Lemma F_772d4 : fetch_word AsanUbsan.M.loaded_segments (0x772d4 : word) = Some W_772d4.
Proof. vm_refl. Qed.
Lemma D_772d4 : decode_any W_772d4 = Some (Load SZ8 true 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772d8 : bv 32 := 0x0230000f.
Lemma F_772d8 : fetch_word AsanUbsan.M.loaded_segments (0x772d8 : word) = Some W_772d8.
Proof. vm_refl. Qed.
Lemma D_772d8 : decode_any W_772d8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772dc : bv 32 := 0xffb504e3.
Lemma F_772dc : fetch_word AsanUbsan.M.loaded_segments (0x772dc : word) = Some W_772dc.
Proof. vm_refl. Qed.
Lemma D_772dc : decode_any W_772dc = Some (Branch BC_EQ 10 27 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_772e0 : bv 32 := 0xfe0514e3.
Lemma F_772e0 : fetch_word AsanUbsan.M.loaded_segments (0x772e0 : word) = Some W_772e0.
Proof. vm_refl. Qed.
Lemma D_772e0 : decode_any W_772e0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_772e4 : bv 32 := 0x000c0513.
Lemma F_772e4 : fetch_word AsanUbsan.M.loaded_segments (0x772e4 : word) = Some W_772e4.
Proof. vm_refl. Qed.
Lemma D_772e4 : decode_any W_772e4 = Some (OpImm ALU_ADD 10 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772e8 : bv 32 := 0x000b8593.
Lemma F_772e8 : fetch_word AsanUbsan.M.loaded_segments (0x772e8 : word) = Some W_772e8.
Proof. vm_refl. Qed.
Lemma D_772e8 : decode_any W_772e8 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772ec : bv 32 := 0x00000613.
Lemma F_772ec : fetch_word AsanUbsan.M.loaded_segments (0x772ec : word) = Some W_772ec.
Proof. vm_refl. Qed.
Lemma D_772ec : decode_any W_772ec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_772f0 : bv 32 := 0x9c0fc0ef.
Lemma F_772f0 : fetch_word AsanUbsan.M.loaded_segments (0x772f0 : word) = Some W_772f0.
Proof. vm_refl. Qed.
Lemma D_772f0 : decode_any W_772f0 = Some (Jal 1 2081216, 4%Z).
Proof. vm_refl. Qed.

Definition W_772f4 : bv 32 := 0x160b34af.
Lemma F_772f4 : fetch_word AsanUbsan.M.loaded_segments (0x772f4 : word) = Some W_772f4.
Proof. vm_refl. Qed.
Lemma D_772f4 : decode_any W_772f4 = Some (Lr AD true true 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_772f8 : bv 32 := 0x02049a63.
Lemma F_772f8 : fetch_word AsanUbsan.M.loaded_segments (0x772f8 : word) = Some W_772f8.
Proof. vm_refl. Qed.
Lemma D_772f8 : decode_any W_772f8 = Some (Branch BC_NE 9 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_772fc : bv 32 := 0x1aab35af.
Lemma F_772fc : fetch_word AsanUbsan.M.loaded_segments (0x772fc : word) = Some W_772fc.
Proof. vm_refl. Qed.
Lemma D_772fc : decode_any W_772fc = Some (Sc AD false true 11 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_77300 : bv 32 := 0xfe059ae3.
Lemma F_77300 : fetch_word AsanUbsan.M.loaded_segments (0x77300 : word) = Some W_77300.
Proof. vm_refl. Qed.
Lemma D_77300 : decode_any W_77300 = Some (Branch BC_NE 11 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_77304 : bv 32 := 0x00100593.
Lemma F_77304 : fetch_word AsanUbsan.M.loaded_segments (0x77304 : word) = Some W_77304.
Proof. vm_refl. Qed.
Lemma D_77304 : decode_any W_77304 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_77308 : bv 32 := 0x00b4362f.
Lemma F_77308 : fetch_word AsanUbsan.M.loaded_segments (0x77308 : word) = Some W_77308.
Proof. vm_refl. Qed.
Lemma D_77308 : decode_any W_77308 = Some (Amo AMO_ADD AD false false 12 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7730c : bv 32 := 0x000d2583.
Lemma F_7730c : fetch_word AsanUbsan.M.loaded_segments (0x7730c : word) = Some W_7730c.
Proof. vm_refl. Qed.
Lemma D_7730c : decode_any W_7730c = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77310 : bv 32 := 0x00200693.
Lemma F_77310 : fetch_word AsanUbsan.M.loaded_segments (0x77310 : word) = Some W_77310.
Proof. vm_refl. Qed.
Lemma D_77310 : decode_any W_77310 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_77314 : bv 32 := 0xfad5eae3.
Lemma F_77314 : fetch_word AsanUbsan.M.loaded_segments (0x77314 : word) = Some W_77314.
Proof. vm_refl. Qed.
Lemma D_77314 : decode_any W_77314 = Some (Branch BC_LTU 11 13 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_77318 : bv 32 := 0x00050493.
Lemma F_77318 : fetch_word AsanUbsan.M.loaded_segments (0x77318 : word) = Some W_77318.
Proof. vm_refl. Qed.
Lemma D_77318 : decode_any W_77318 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7731c : bv 32 := 0x00813503.
Lemma F_7731c : fetch_word AsanUbsan.M.loaded_segments (0x7731c : word) = Some W_7731c.
Proof. vm_refl. Qed.
Lemma D_7731c : decode_any W_7731c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_77320 : bv 32 := 0x000a8593.
Lemma F_77320 : fetch_word AsanUbsan.M.loaded_segments (0x77320 : word) = Some W_77320.
Proof. vm_refl. Qed.
Lemma D_77320 : decode_any W_77320 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77324 : bv 32 := 0xee4fd0ef.
Lemma F_77324 : fetch_word AsanUbsan.M.loaded_segments (0x77324 : word) = Some W_77324.
Proof. vm_refl. Qed.
Lemma D_77324 : decode_any W_77324 = Some (Jal 1 2086628, 4%Z).
Proof. vm_refl. Qed.

Definition W_77328 : bv 32 := 0x0100006f.
Lemma F_77328 : fetch_word AsanUbsan.M.loaded_segments (0x77328 : word) = Some W_77328.
Proof. vm_refl. Qed.
Lemma D_77328 : decode_any W_77328 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7732c : bv 32 := 0x000c0593.
Lemma F_7732c : fetch_word AsanUbsan.M.loaded_segments (0x7732c : word) = Some W_7732c.
Proof. vm_refl. Qed.
Lemma D_7732c : decode_any W_7732c = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77330 : bv 32 := 0x00000613.
Lemma F_77330 : fetch_word AsanUbsan.M.loaded_segments (0x77330 : word) = Some W_77330.
Proof. vm_refl. Qed.
Lemma D_77330 : decode_any W_77330 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77334 : bv 32 := 0xafcfc0ef.
Lemma F_77334 : fetch_word AsanUbsan.M.loaded_segments (0x77334 : word) = Some W_77334.
Proof. vm_refl. Qed.
Lemma D_77334 : decode_any W_77334 = Some (Jal 1 2081532, 4%Z).
Proof. vm_refl. Qed.

Definition W_77338 : bv 32 := 0x00048513.
Lemma F_77338 : fetch_word AsanUbsan.M.loaded_segments (0x77338 : word) = Some W_77338.
Proof. vm_refl. Qed.
Lemma D_77338 : decode_any W_77338 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7733c : bv 32 := 0xf8dff06f.
Lemma F_7733c : fetch_word AsanUbsan.M.loaded_segments (0x7733c : word) = Some W_7733c.
Proof. vm_refl. Qed.
Lemma D_7733c : decode_any W_7733c = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_77340 : bv 32 := 0x000b0513.
Lemma F_77340 : fetch_word AsanUbsan.M.loaded_segments (0x77340 : word) = Some W_77340.
Proof. vm_refl. Qed.
Lemma D_77340 : decode_any W_77340 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77344 : bv 32 := 0x004a1413.
Lemma F_77344 : fetch_word AsanUbsan.M.loaded_segments (0x77344 : word) = Some W_77344.
Proof. vm_refl. Qed.
Lemma D_77344 : decode_any W_77344 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_77348 : bv 32 := 0x00850433.
Lemma F_77348 : fetch_word AsanUbsan.M.loaded_segments (0x77348 : word) = Some W_77348.
Proof. vm_refl. Qed.
Lemma D_77348 : decode_any W_77348 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7734c : bv 32 := 0x00843503.
Lemma F_7734c : fetch_word AsanUbsan.M.loaded_segments (0x7734c : word) = Some W_7734c.
Proof. vm_refl. Qed.
Lemma D_7734c : decode_any W_7734c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_77350 : bv 32 := 0x04050263.
Lemma F_77350 : fetch_word AsanUbsan.M.loaded_segments (0x77350 : word) = Some W_77350.
Proof. vm_refl. Qed.
Lemma D_77350 : decode_any W_77350 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_77354 : bv 32 := 0x00000513.
Lemma F_77354 : fetch_word AsanUbsan.M.loaded_segments (0x77354 : word) = Some W_77354.
Proof. vm_refl. Qed.
Lemma D_77354 : decode_any W_77354 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77358 : bv 32 := 0x08813083.
Lemma F_77358 : fetch_word AsanUbsan.M.loaded_segments (0x77358 : word) = Some W_77358.
Proof. vm_refl. Qed.
Lemma D_77358 : decode_any W_77358 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7735c : bv 32 := 0x08013403.
Lemma F_7735c : fetch_word AsanUbsan.M.loaded_segments (0x7735c : word) = Some W_7735c.
Proof. vm_refl. Qed.
Lemma D_7735c : decode_any W_7735c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_77360 : bv 32 := 0x07813483.
Lemma F_77360 : fetch_word AsanUbsan.M.loaded_segments (0x77360 : word) = Some W_77360.
Proof. vm_refl. Qed.
Lemma D_77360 : decode_any W_77360 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_77364 : bv 32 := 0x07013903.
Lemma F_77364 : fetch_word AsanUbsan.M.loaded_segments (0x77364 : word) = Some W_77364.
Proof. vm_refl. Qed.
Lemma D_77364 : decode_any W_77364 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_77368 : bv 32 := 0x06813983.
Lemma F_77368 : fetch_word AsanUbsan.M.loaded_segments (0x77368 : word) = Some W_77368.
Proof. vm_refl. Qed.
Lemma D_77368 : decode_any W_77368 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7736c : bv 32 := 0x06013a03.
Lemma F_7736c : fetch_word AsanUbsan.M.loaded_segments (0x7736c : word) = Some W_7736c.
Proof. vm_refl. Qed.
Lemma D_7736c : decode_any W_7736c = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_77370 : bv 32 := 0x05813a83.
Lemma F_77370 : fetch_word AsanUbsan.M.loaded_segments (0x77370 : word) = Some W_77370.
Proof. vm_refl. Qed.
Lemma D_77370 : decode_any W_77370 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_77374 : bv 32 := 0x05013b03.
Lemma F_77374 : fetch_word AsanUbsan.M.loaded_segments (0x77374 : word) = Some W_77374.
Proof. vm_refl. Qed.
Lemma D_77374 : decode_any W_77374 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_77378 : bv 32 := 0x04813b83.
Lemma F_77378 : fetch_word AsanUbsan.M.loaded_segments (0x77378 : word) = Some W_77378.
Proof. vm_refl. Qed.
Lemma D_77378 : decode_any W_77378 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7737c : bv 32 := 0x04013c03.
Lemma F_7737c : fetch_word AsanUbsan.M.loaded_segments (0x7737c : word) = Some W_7737c.
Proof. vm_refl. Qed.
Lemma D_7737c : decode_any W_7737c = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_77380 : bv 32 := 0x03813c83.
Lemma F_77380 : fetch_word AsanUbsan.M.loaded_segments (0x77380 : word) = Some W_77380.
Proof. vm_refl. Qed.
Lemma D_77380 : decode_any W_77380 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_77384 : bv 32 := 0x03013d03.
Lemma F_77384 : fetch_word AsanUbsan.M.loaded_segments (0x77384 : word) = Some W_77384.
Proof. vm_refl. Qed.
Lemma D_77384 : decode_any W_77384 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_77388 : bv 32 := 0x02813d83.
Lemma F_77388 : fetch_word AsanUbsan.M.loaded_segments (0x77388 : word) = Some W_77388.
Proof. vm_refl. Qed.
Lemma D_77388 : decode_any W_77388 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7738c : bv 32 := 0x09010113.
Lemma F_7738c : fetch_word AsanUbsan.M.loaded_segments (0x7738c : word) = Some W_7738c.
Proof. vm_refl. Qed.
Lemma D_7738c : decode_any W_7738c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_77390 : bv 32 := 0x00008067.
Lemma F_77390 : fetch_word AsanUbsan.M.loaded_segments (0x77390 : word) = Some W_77390.
Proof. vm_refl. Qed.
Lemma D_77390 : decode_any W_77390 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77394 : bv 32 := 0x01813483.
Lemma F_77394 : fetch_word AsanUbsan.M.loaded_segments (0x77394 : word) = Some W_77394.
Proof. vm_refl. Qed.
Lemma D_77394 : decode_any W_77394 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_77398 : bv 32 := 0x01013a03.
Lemma F_77398 : fetch_word AsanUbsan.M.loaded_segments (0x77398 : word) = Some W_77398.
Proof. vm_refl. Qed.
Lemma D_77398 : decode_any W_77398 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7739c : bv 32 := 0x0744ec63.
Lemma F_7739c : fetch_word AsanUbsan.M.loaded_segments (0x7739c : word) = Some W_7739c.
Proof. vm_refl. Qed.
Lemma D_7739c : decode_any W_7739c = Some (Branch BC_LTU 9 20 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_773a0 : bv 32 := 0x0089b683.
Lemma F_773a0 : fetch_word AsanUbsan.M.loaded_segments (0x773a0 : word) = Some W_773a0.
Proof. vm_refl. Qed.
Lemma D_773a0 : decode_any W_773a0 = Some (Load SZ8 true 13 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_773a4 : bv 32 := 0x40d90533.
Lemma F_773a4 : fetch_word AsanUbsan.M.loaded_segments (0x773a4 : word) = Some W_773a4.
Proof. vm_refl. Qed.
Lemma D_773a4 : decode_any W_773a4 = Some (Op ALU_SUB 10 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_773a8 : bv 32 := 0x80050793.
Lemma F_773a8 : fetch_word AsanUbsan.M.loaded_segments (0x773a8 : word) = Some W_773a8.
Proof. vm_refl. Qed.
Lemma D_773a8 : decode_any W_773a8 = Some (OpImm ALU_ADD 15 10 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_773ac : bv 32 := 0x02f13023.
Lemma F_773ac : fetch_word AsanUbsan.M.loaded_segments (0x773ac : word) = Some W_773ac.
Proof. vm_refl. Qed.
Lemma D_773ac : decode_any W_773ac = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_773b0 : bv 32 := 0x000d2503.
Lemma F_773b0 : fetch_word AsanUbsan.M.loaded_segments (0x773b0 : word) = Some W_773b0.
Proof. vm_refl. Qed.
Lemma D_773b0 : decode_any W_773b0 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773b4 : bv 32 := 0x00200593.
Lemma F_773b4 : fetch_word AsanUbsan.M.loaded_segments (0x773b4 : word) = Some W_773b4.
Proof. vm_refl. Qed.
Lemma D_773b4 : decode_any W_773b4 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_773b8 : bv 32 := 0x06b57e63.
Lemma F_773b8 : fetch_word AsanUbsan.M.loaded_segments (0x773b8 : word) = Some W_773b8.
Proof. vm_refl. Qed.
Lemma D_773b8 : decode_any W_773b8 = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_773bc : bv 32 := 0x00840913.
Lemma F_773bc : fetch_word AsanUbsan.M.loaded_segments (0x773bc : word) = Some W_773bc.
Proof. vm_refl. Qed.
Lemma D_773bc : decode_any W_773bc = Some (OpImm ALU_ADD 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_773c0 : bv 32 := 0x0b47e263.
Lemma F_773c0 : fetch_word AsanUbsan.M.loaded_segments (0x773c0 : word) = Some W_773c0.
Proof. vm_refl. Qed.
Lemma D_773c0 : decode_any W_773c0 = Some (Branch BC_LTU 15 20 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_773c4 : bv 32 := 0x0a97f063.
Lemma F_773c4 : fetch_word AsanUbsan.M.loaded_segments (0x773c4 : word) = Some W_773c4.
Proof. vm_refl. Qed.
Lemma D_773c4 : decode_any W_773c4 = Some (Branch BC_GEU 15 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_773c8 : bv 32 := 0x000d2503.
Lemma F_773c8 : fetch_word AsanUbsan.M.loaded_segments (0x773c8 : word) = Some W_773c8.
Proof. vm_refl. Qed.
Lemma D_773c8 : decode_any W_773c8 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773cc : bv 32 := 0x00200593.
Lemma F_773cc : fetch_word AsanUbsan.M.loaded_segments (0x773cc : word) = Some W_773cc.
Proof. vm_refl. Qed.
Lemma D_773cc : decode_any W_773cc = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_773d0 : bv 32 := 0x0cb57a63.
Lemma F_773d0 : fetch_word AsanUbsan.M.loaded_segments (0x773d0 : word) = Some W_773d0.
Proof. vm_refl. Qed.
Lemma D_773d0 : decode_any W_773d0 = Some (Branch BC_GEU 10 11 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_773d4 : bv 32 := 0x00000513.
Lemma F_773d4 : fetch_word AsanUbsan.M.loaded_segments (0x773d4 : word) = Some W_773d4.
Proof. vm_refl. Qed.
Lemma D_773d4 : decode_any W_773d4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773d8 : bv 32 := 0x0b80006f.
Lemma F_773d8 : fetch_word AsanUbsan.M.loaded_segments (0x773d8 : word) = Some W_773d8.
Proof. vm_refl. Qed.
Lemma D_773d8 : decode_any W_773d8 = Some (Jal 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_773dc : bv 32 := 0xfff9f517.
Lemma F_773dc : fetch_word AsanUbsan.M.loaded_segments (0x773dc : word) = Some W_773dc.
Proof. vm_refl. Qed.
Lemma D_773dc : decode_any W_773dc = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_773e0 : bv 32 := 0x16d50513.
Lemma F_773e0 : fetch_word AsanUbsan.M.loaded_segments (0x773e0 : word) = Some W_773e0.
Proof. vm_refl. Qed.
Lemma D_773e0 : decode_any W_773e0 = Some (OpImm ALU_ADD 10 10 365, 4%Z).
Proof. vm_refl. Qed.

Definition W_773e4 : bv 32 := 0x000a8593.
Lemma F_773e4 : fetch_word AsanUbsan.M.loaded_segments (0x773e4 : word) = Some W_773e4.
Proof. vm_refl. Qed.
Lemma D_773e4 : decode_any W_773e4 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773e8 : bv 32 := 0x00060493.
Lemma F_773e8 : fetch_word AsanUbsan.M.loaded_segments (0x773e8 : word) = Some W_773e8.
Proof. vm_refl. Qed.
Lemma D_773e8 : decode_any W_773e8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773ec : bv 32 := 0x000a0613.
Lemma F_773ec : fetch_word AsanUbsan.M.loaded_segments (0x773ec : word) = Some W_773ec.
Proof. vm_refl. Qed.
Lemma D_773ec : decode_any W_773ec = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773f0 : bv 32 := 0x00068413.
Lemma F_773f0 : fetch_word AsanUbsan.M.loaded_segments (0x773f0 : word) = Some W_773f0.
Proof. vm_refl. Qed.
Lemma D_773f0 : decode_any W_773f0 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773f4 : bv 32 := 0xe14fd0ef.
Lemma F_773f4 : fetch_word AsanUbsan.M.loaded_segments (0x773f4 : word) = Some W_773f4.
Proof. vm_refl. Qed.
Lemma D_773f4 : decode_any W_773f4 = Some (Jal 1 2086420, 4%Z).
Proof. vm_refl. Qed.

Definition W_773f8 : bv 32 := 0x00048613.
Lemma F_773f8 : fetch_word AsanUbsan.M.loaded_segments (0x773f8 : word) = Some W_773f8.
Proof. vm_refl. Qed.
Lemma D_773f8 : decode_any W_773f8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_773fc : bv 32 := 0x00040693.
Lemma F_773fc : fetch_word AsanUbsan.M.loaded_segments (0x773fc : word) = Some W_773fc.
Proof. vm_refl. Qed.
Lemma D_773fc : decode_any W_773fc = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77400 : bv 32 := 0x000abb03.
Lemma F_77400 : fetch_word AsanUbsan.M.loaded_segments (0x77400 : word) = Some W_77400.
Proof. vm_refl. Qed.
Lemma D_77400 : decode_any W_77400 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77404 : bv 32 := 0xfff00513.
Lemma F_77404 : fetch_word AsanUbsan.M.loaded_segments (0x77404 : word) = Some W_77404.
Proof. vm_refl. Qed.
Lemma D_77404 : decode_any W_77404 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_77408 : bv 32 := 0x0230000f.
Lemma F_77408 : fetch_word AsanUbsan.M.loaded_segments (0x77408 : word) = Some W_77408.
Proof. vm_refl. Qed.
Lemma D_77408 : decode_any W_77408 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7740c : bv 32 := 0xdeab18e3.
Lemma F_7740c : fetch_word AsanUbsan.M.loaded_segments (0x7740c : word) = Some W_7740c.
Proof. vm_refl. Qed.
Lemma D_7740c : decode_any W_7740c = Some (Branch BC_NE 22 10 7664, 4%Z).
Proof. vm_refl. Qed.

Definition W_77410 : bv 32 := 0xf45ff06f.
Lemma F_77410 : fetch_word AsanUbsan.M.loaded_segments (0x77410 : word) = Some W_77410.
Proof. vm_refl. Qed.
Lemma D_77410 : decode_any W_77410 = Some (Jal 0 2096964, 4%Z).
Proof. vm_refl. Qed.

Definition W_77414 : bv 32 := 0xfffa5517.
Lemma F_77414 : fetch_word AsanUbsan.M.loaded_segments (0x77414 : word) = Some W_77414.
Proof. vm_refl. Qed.
Lemma D_77414 : decode_any W_77414 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_77418 : bv 32 := 0xfff9d597.
Lemma F_77418 : fetch_word AsanUbsan.M.loaded_segments (0x77418 : word) = Some W_77418.
Proof. vm_refl. Qed.
Lemma D_77418 : decode_any W_77418 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7741c : bv 32 := 0x3f950513.
Lemma F_7741c : fetch_word AsanUbsan.M.loaded_segments (0x7741c : word) = Some W_7741c.
Proof. vm_refl. Qed.
Lemma D_7741c : decode_any W_7741c = Some (OpImm ALU_ADD 10 10 1017, 4%Z).
Proof. vm_refl. Qed.

Definition W_77420 : bv 32 := 0x59358613.
Lemma F_77420 : fetch_word AsanUbsan.M.loaded_segments (0x77420 : word) = Some W_77420.
Proof. vm_refl. Qed.
Lemma D_77420 : decode_any W_77420 = Some (OpImm ALU_ADD 12 11 1427, 4%Z).
Proof. vm_refl. Qed.

Definition W_77424 : bv 32 := 0x08a00593.
Lemma F_77424 : fetch_word AsanUbsan.M.loaded_segments (0x77424 : word) = Some W_77424.
Proof. vm_refl. Qed.
Lemma D_77424 : decode_any W_77424 = Some (OpImm ALU_ADD 11 0 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_77428 : bv 32 := 0x000a0693.
Lemma F_77428 : fetch_word AsanUbsan.M.loaded_segments (0x77428 : word) = Some W_77428.
Proof. vm_refl. Qed.
Lemma D_77428 : decode_any W_77428 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7742c : bv 32 := 0x00048713.
Lemma F_7742c : fetch_word AsanUbsan.M.loaded_segments (0x7742c : word) = Some W_7742c.
Proof. vm_refl. Qed.
Lemma D_7742c : decode_any W_7742c = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77430 : bv 32 := 0x6b9010ef.
Lemma F_77430 : fetch_word AsanUbsan.M.loaded_segments (0x77430 : word) = Some W_77430.
Proof. vm_refl. Qed.
Lemma D_77430 : decode_any W_77430 = Some (Jal 1 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_77434 : bv 32 := 0x0009b603.
Lemma F_77434 : fetch_word AsanUbsan.M.loaded_segments (0x77434 : word) = Some W_77434.
Proof. vm_refl. Qed.
Lemma D_77434 : decode_any W_77434 = Some (Load SZ8 true 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77438 : bv 32 := 0x000f9517.
Lemma F_77438 : fetch_word AsanUbsan.M.loaded_segments (0x77438 : word) = Some W_77438.
Proof. vm_refl. Qed.
Lemma D_77438 : decode_any W_77438 = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_7743c : bv 32 := 0x04053883.
Lemma F_7743c : fetch_word AsanUbsan.M.loaded_segments (0x7743c : word) = Some W_7743c.
Proof. vm_refl. Qed.
Lemma D_7743c : decode_any W_7743c = Some (Load SZ8 true 17 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_77440 : bv 32 := 0xfff9f517.
Lemma F_77440 : fetch_word AsanUbsan.M.loaded_segments (0x77440 : word) = Some W_77440.
Proof. vm_refl. Qed.
Lemma D_77440 : decode_any W_77440 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_77444 : bv 32 := 0x8a750513.
Lemma F_77444 : fetch_word AsanUbsan.M.loaded_segments (0x77444 : word) = Some W_77444.
Proof. vm_refl. Qed.
Lemma D_77444 : decode_any W_77444 = Some (OpImm ALU_ADD 10 10 2215, 4%Z).
Proof. vm_refl. Qed.

Definition W_77448 : bv 32 := 0x02010813.
Lemma F_77448 : fetch_word AsanUbsan.M.loaded_segments (0x77448 : word) = Some W_77448.
Proof. vm_refl. Qed.
Lemma D_77448 : decode_any W_77448 = Some (OpImm ALU_ADD 16 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7744c : bv 32 := 0x00098593.
Lemma F_7744c : fetch_word AsanUbsan.M.loaded_segments (0x7744c : word) = Some W_7744c.
Proof. vm_refl. Qed.
Lemma D_7744c : decode_any W_7744c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77450 : bv 32 := 0x00090713.
Lemma F_77450 : fetch_word AsanUbsan.M.loaded_segments (0x77450 : word) = Some W_77450.
Proof. vm_refl. Qed.
Lemma D_77450 : decode_any W_77450 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77454 : bv 32 := 0xdb4fd0ef.
Lemma F_77454 : fetch_word AsanUbsan.M.loaded_segments (0x77454 : word) = Some W_77454.
Proof. vm_refl. Qed.
Lemma D_77454 : decode_any W_77454 = Some (Jal 1 2086324, 4%Z).
Proof. vm_refl. Qed.

Definition W_77458 : bv 32 := 0x02013783.
Lemma F_77458 : fetch_word AsanUbsan.M.loaded_segments (0x77458 : word) = Some W_77458.
Proof. vm_refl. Qed.
Lemma D_77458 : decode_any W_77458 = Some (Load SZ8 true 15 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7745c : bv 32 := 0x00840913.
Lemma F_7745c : fetch_word AsanUbsan.M.loaded_segments (0x7745c : word) = Some W_7745c.
Proof. vm_refl. Qed.
Lemma D_7745c : decode_any W_7745c = Some (OpImm ALU_ADD 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_77460 : bv 32 := 0xf747f2e3.
Lemma F_77460 : fetch_word AsanUbsan.M.loaded_segments (0x77460 : word) = Some W_77460.
Proof. vm_refl. Qed.
Lemma D_77460 : decode_any W_77460 = Some (Branch BC_GEU 15 20 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_77464 : bv 32 := 0x00078513.
Lemma F_77464 : fetch_word AsanUbsan.M.loaded_segments (0x77464 : word) = Some W_77464.
Proof. vm_refl. Qed.
Lemma D_77464 : decode_any W_77464 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77468 : bv 32 := 0xc41ff0ef.
Lemma F_77468 : fetch_word AsanUbsan.M.loaded_segments (0x77468 : word) = Some W_77468.
Proof. vm_refl. Qed.
Lemma D_77468 : decode_any W_77468 = Some (Jal 1 2096192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7746c : bv 32 := 0x00050863.
Lemma F_7746c : fetch_word AsanUbsan.M.loaded_segments (0x7746c : word) = Some W_7746c.
Proof. vm_refl. Qed.
Lemma D_7746c : decode_any W_7746c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_77470 : bv 32 := 0x02013783.
Lemma F_77470 : fetch_word AsanUbsan.M.loaded_segments (0x77470 : word) = Some W_77470.
Proof. vm_refl. Qed.
Lemma D_77470 : decode_any W_77470 = Some (Load SZ8 true 15 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_77474 : bv 32 := 0x00090593.
Lemma F_77474 : fetch_word AsanUbsan.M.loaded_segments (0x77474 : word) = Some W_77474.
Proof. vm_refl. Qed.
Lemma D_77474 : decode_any W_77474 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77478 : bv 32 := 0x01c0006f.
Lemma F_77478 : fetch_word AsanUbsan.M.loaded_segments (0x77478 : word) = Some W_77478.
Proof. vm_refl. Qed.
Lemma D_77478 : decode_any W_77478 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7747c : bv 32 := 0x000d2503.
Lemma F_7747c : fetch_word AsanUbsan.M.loaded_segments (0x7747c : word) = Some W_7747c.
Proof. vm_refl. Qed.
Lemma D_7747c : decode_any W_7747c = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77480 : bv 32 := 0x00200593.
Lemma F_77480 : fetch_word AsanUbsan.M.loaded_segments (0x77480 : word) = Some W_77480.
Proof. vm_refl. Qed.
Lemma D_77480 : decode_any W_77480 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_77484 : bv 32 := 0x02b57a63.
Lemma F_77484 : fetch_word AsanUbsan.M.loaded_segments (0x77484 : word) = Some W_77484.
Proof. vm_refl. Qed.
Lemma D_77484 : decode_any W_77484 = Some (Branch BC_GEU 10 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_77488 : bv 32 := 0x00000513.
Lemma F_77488 : fetch_word AsanUbsan.M.loaded_segments (0x77488 : word) = Some W_77488.
Proof. vm_refl. Qed.
Lemma D_77488 : decode_any W_77488 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7748c : bv 32 := 0x02013783.
Lemma F_7748c : fetch_word AsanUbsan.M.loaded_segments (0x7748c : word) = Some W_7748c.
Proof. vm_refl. Qed.
Lemma D_7748c : decode_any W_7748c = Some (Load SZ8 true 15 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_77490 : bv 32 := 0x00000593.
Lemma F_77490 : fetch_word AsanUbsan.M.loaded_segments (0x77490 : word) = Some W_77490.
Proof. vm_refl. Qed.
Lemma D_77490 : decode_any W_77490 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77494 : bv 32 := 0x00f93023.
Lemma F_77494 : fetch_word AsanUbsan.M.loaded_segments (0x77494 : word) = Some W_77494.
Proof. vm_refl. Qed.
Lemma D_77494 : decode_any W_77494 = Some (Store SZ8 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77498 : bv 32 := 0x00a93423.
Lemma F_77498 : fetch_word AsanUbsan.M.loaded_segments (0x77498 : word) = Some W_77498.
Proof. vm_refl. Qed.
Lemma D_77498 : decode_any W_77498 = Some (Store SZ8 18 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7749c : bv 32 := 0x00058513.
Lemma F_7749c : fetch_word AsanUbsan.M.loaded_segments (0x7749c : word) = Some W_7749c.
Proof. vm_refl. Qed.
Lemma D_7749c : decode_any W_7749c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_774a0 : bv 32 := 0xeb9ff06f.
Lemma F_774a0 : fetch_word AsanUbsan.M.loaded_segments (0x774a0 : word) = Some W_774a0.
Proof. vm_refl. Qed.
Lemma D_774a0 : decode_any W_774a0 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_774a4 : bv 32 := 0xfff9d517.
Lemma F_774a4 : fetch_word AsanUbsan.M.loaded_segments (0x774a4 : word) = Some W_774a4.
Proof. vm_refl. Qed.
Lemma D_774a4 : decode_any W_774a4 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_774a8 : bv 32 := 0xad250513.
Lemma F_774a8 : fetch_word AsanUbsan.M.loaded_segments (0x774a8 : word) = Some W_774a8.
Proof. vm_refl. Qed.
Lemma D_774a8 : decode_any W_774a8 = Some (OpImm ALU_ADD 10 10 2770, 4%Z).
Proof. vm_refl. Qed.

Definition W_774ac : bv 32 := 0x00078593.
Lemma F_774ac : fetch_word AsanUbsan.M.loaded_segments (0x774ac : word) = Some W_774ac.
Proof. vm_refl. Qed.
Lemma D_774ac : decode_any W_774ac = Some (OpImm ALU_ADD 11 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_774b0 : bv 32 := 0xd58fd0ef.
Lemma F_774b0 : fetch_word AsanUbsan.M.loaded_segments (0x774b0 : word) = Some W_774b0.
Proof. vm_refl. Qed.
Lemma D_774b0 : decode_any W_774b0 = Some (Jal 1 2086232, 4%Z).
Proof. vm_refl. Qed.

Definition W_774b4 : bv 32 := 0xfd5ff06f.
Lemma F_774b4 : fetch_word AsanUbsan.M.loaded_segments (0x774b4 : word) = Some W_774b4.
Proof. vm_refl. Qed.
Lemma D_774b4 : decode_any W_774b4 = Some (Jal 0 2097108, 4%Z).
Proof. vm_refl. Qed.

Definition W_774b8 : bv 32 := 0xfffa6517.
Lemma F_774b8 : fetch_word AsanUbsan.M.loaded_segments (0x774b8 : word) = Some W_774b8.
Proof. vm_refl. Qed.
Lemma D_774b8 : decode_any W_774b8 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_774bc : bv 32 := 0x59350513.
Lemma F_774bc : fetch_word AsanUbsan.M.loaded_segments (0x774bc : word) = Some W_774bc.
Proof. vm_refl. Qed.
Lemma D_774bc : decode_any W_774bc = Some (OpImm ALU_ADD 10 10 1427, 4%Z).
Proof. vm_refl. Qed.

Definition W_774c0 : bv 32 := 0xd48fd0ef.
Lemma F_774c0 : fetch_word AsanUbsan.M.loaded_segments (0x774c0 : word) = Some W_774c0.
Proof. vm_refl. Qed.
Lemma D_774c0 : decode_any W_774c0 = Some (Jal 1 2086216, 4%Z).
Proof. vm_refl. Qed.

Definition W_774c4 : bv 32 := 0xfc5ff06f.
Lemma F_774c4 : fetch_word AsanUbsan.M.loaded_segments (0x774c4 : word) = Some W_774c4.
Proof. vm_refl. Qed.
Lemma D_774c4 : decode_any W_774c4 = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.
