(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_60000 : bv 32 := 0x01078e93.
Lemma F_60000 : fetch_word AsanUbsan.M.loaded_segments (0x60048 : word) = Some W_60000.
Proof. vm_refl. Qed.
Lemma D_60000 : decode_any W_60000 = Some (OpImm ALU_ADD 29 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60004 : bv 32 := 0x00068e13.
Lemma F_60004 : fetch_word AsanUbsan.M.loaded_segments (0x6004c : word) = Some W_60004.
Proof. vm_refl. Qed.
Lemma D_60004 : decode_any W_60004 = Some (OpImm ALU_ADD 28 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60008 : bv 32 := 0x026ee063.
Lemma F_60008 : fetch_word AsanUbsan.M.loaded_segments (0x60050 : word) = Some W_60008.
Proof. vm_refl. Qed.
Lemma D_60008 : decode_any W_60008 = Some (Branch BC_LTU 29 6 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6000c : bv 32 := 0x0017de13.
Lemma F_6000c : fetch_word AsanUbsan.M.loaded_segments (0x60054 : word) = Some W_6000c.
Proof. vm_refl. Qed.
Lemma D_6000c : decode_any W_6000c = Some (ShiftImm ALU_SRL 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60010 : bv 32 := 0x03fe9e93.
Lemma F_60010 : fetch_word AsanUbsan.M.loaded_segments (0x60058 : word) = Some W_60010.
Proof. vm_refl. Qed.
Lemma D_60010 : decode_any W_60010 = Some (ShiftImm ALU_SLL 29 29 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60014 : bv 32 := 0x01c39e33.
Lemma F_60014 : fetch_word AsanUbsan.M.loaded_segments (0x6005c : word) = Some W_60014.
Proof. vm_refl. Qed.
Lemma D_60014 : decode_any W_60014 = Some (Op ALU_SLL 28 7 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60018 : bv 32 := 0x001e5f13.
Lemma F_60018 : fetch_word AsanUbsan.M.loaded_segments (0x60060 : word) = Some W_60018.
Proof. vm_refl. Qed.
Lemma D_60018 : decode_any W_60018 = Some (ShiftImm ALU_SRL 30 28 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6001c : bv 32 := 0x43fede93.
Lemma F_6001c : fetch_word AsanUbsan.M.loaded_segments (0x60064 : word) = Some W_6001c.
Proof. vm_refl. Qed.
Lemma D_6001c : decode_any W_6001c = Some (ShiftImm ALU_SRA 29 29 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60020 : bv 32 := 0x01eefeb3.
Lemma F_60020 : fetch_word AsanUbsan.M.loaded_segments (0x60068 : word) = Some W_60020.
Proof. vm_refl. Qed.
Lemma D_60020 : decode_any W_60020 = Some (Op ALU_AND 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60024 : bv 32 := 0x01ce8e33.
Lemma F_60024 : fetch_word AsanUbsan.M.loaded_segments (0x6006c : word) = Some W_60024.
Proof. vm_refl. Qed.
Lemma D_60024 : decode_any W_60024 = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60028 : bv 32 := 0x03c8debb.
Lemma F_60028 : fetch_word AsanUbsan.M.loaded_segments (0x60070 : word) = Some W_60028.
Proof. vm_refl. Qed.
Lemma D_60028 : decode_any W_60028 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6002c : bv 32 := 0x00800f13.
Lemma F_6002c : fetch_word AsanUbsan.M.loaded_segments (0x60074 : word) = Some W_6002c.
Proof. vm_refl. Qed.
Lemma D_6002c : decode_any W_6002c = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60030 : bv 32 := 0xfbeee4e3.
Lemma F_60030 : fetch_word AsanUbsan.M.loaded_segments (0x60078 : word) = Some W_60030.
Proof. vm_refl. Qed.
Lemma D_60030 : decode_any W_60030 = Some (Branch BC_LTU 29 30 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60034 : bv 32 := 0x00800e93.
Lemma F_60034 : fetch_word AsanUbsan.M.loaded_segments (0x6007c : word) = Some W_60034.
Proof. vm_refl. Qed.
Lemma D_60034 : decode_any W_60034 = Some (OpImm ALU_ADD 29 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60038 : bv 32 := 0xfa1ff06f.
Lemma F_60038 : fetch_word AsanUbsan.M.loaded_segments (0x60080 : word) = Some W_60038.
Proof. vm_refl. Qed.
Lemma D_60038 : decode_any W_60038 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6003c : bv 32 := 0x04000e13.
Lemma F_6003c : fetch_word AsanUbsan.M.loaded_segments (0x60084 : word) = Some W_6003c.
Proof. vm_refl. Qed.
Lemma D_6003c : decode_any W_6003c = Some (OpImm ALU_ADD 28 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60040 : bv 32 := 0x03c8debb.
Lemma F_60040 : fetch_word AsanUbsan.M.loaded_segments (0x60088 : word) = Some W_60040.
Proof. vm_refl. Qed.
Lemma D_60040 : decode_any W_60040 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60044 : bv 32 := 0x00800f13.
Lemma F_60044 : fetch_word AsanUbsan.M.loaded_segments (0x6008c : word) = Some W_60044.
Proof. vm_refl. Qed.
Lemma D_60044 : decode_any W_60044 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60048 : bv 32 := 0xf9eee8e3.
Lemma F_60048 : fetch_word AsanUbsan.M.loaded_segments (0x60090 : word) = Some W_60048.
Proof. vm_refl. Qed.
Lemma D_60048 : decode_any W_60048 = Some (Branch BC_LTU 29 30 8080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6004c : bv 32 := 0xfe9ff06f.
Lemma F_6004c : fetch_word AsanUbsan.M.loaded_segments (0x60094 : word) = Some W_6004c.
Proof. vm_refl. Qed.
Lemma D_6004c : decode_any W_6004c = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60050 : bv 32 := 0x00442583.
Lemma F_60050 : fetch_word AsanUbsan.M.loaded_segments (0x60098 : word) = Some W_60050.
Proof. vm_refl. Qed.
Lemma D_60050 : decode_any W_60050 = Some (Load SZ4 true 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60054 : bv 32 := 0xf25ff06f.
Lemma F_60054 : fetch_word AsanUbsan.M.loaded_segments (0x6009c : word) = Some W_60054.
Proof. vm_refl. Qed.
Lemma D_60054 : decode_any W_60054 = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60058 : bv 32 := 0xf8010113.
Lemma F_60058 : fetch_word AsanUbsan.M.loaded_segments (0x600a0 : word) = Some W_60058.
Proof. vm_refl. Qed.
Lemma D_60058 : decode_any W_60058 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6005c : bv 32 := 0x06113c23.
Lemma F_6005c : fetch_word AsanUbsan.M.loaded_segments (0x600a4 : word) = Some W_6005c.
Proof. vm_refl. Qed.
Lemma D_6005c : decode_any W_6005c = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60060 : bv 32 := 0x06813823.
Lemma F_60060 : fetch_word AsanUbsan.M.loaded_segments (0x600a8 : word) = Some W_60060.
Proof. vm_refl. Qed.
Lemma D_60060 : decode_any W_60060 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60064 : bv 32 := 0x06913423.
Lemma F_60064 : fetch_word AsanUbsan.M.loaded_segments (0x600ac : word) = Some W_60064.
Proof. vm_refl. Qed.
Lemma D_60064 : decode_any W_60064 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60068 : bv 32 := 0x07213023.
Lemma F_60068 : fetch_word AsanUbsan.M.loaded_segments (0x600b0 : word) = Some W_60068.
Proof. vm_refl. Qed.
Lemma D_60068 : decode_any W_60068 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6006c : bv 32 := 0x05313c23.
Lemma F_6006c : fetch_word AsanUbsan.M.loaded_segments (0x600b4 : word) = Some W_6006c.
Proof. vm_refl. Qed.
Lemma D_6006c : decode_any W_6006c = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60070 : bv 32 := 0x05413823.
Lemma F_60070 : fetch_word AsanUbsan.M.loaded_segments (0x600b8 : word) = Some W_60070.
Proof. vm_refl. Qed.
Lemma D_60070 : decode_any W_60070 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60074 : bv 32 := 0x05513423.
Lemma F_60074 : fetch_word AsanUbsan.M.loaded_segments (0x600bc : word) = Some W_60074.
Proof. vm_refl. Qed.
Lemma D_60074 : decode_any W_60074 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60078 : bv 32 := 0x05613023.
Lemma F_60078 : fetch_word AsanUbsan.M.loaded_segments (0x600c0 : word) = Some W_60078.
Proof. vm_refl. Qed.
Lemma D_60078 : decode_any W_60078 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6007c : bv 32 := 0x03713c23.
Lemma F_6007c : fetch_word AsanUbsan.M.loaded_segments (0x600c4 : word) = Some W_6007c.
Proof. vm_refl. Qed.
Lemma D_6007c : decode_any W_6007c = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60080 : bv 32 := 0x03813823.
Lemma F_60080 : fetch_word AsanUbsan.M.loaded_segments (0x600c8 : word) = Some W_60080.
Proof. vm_refl. Qed.
Lemma D_60080 : decode_any W_60080 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60084 : bv 32 := 0x03913423.
Lemma F_60084 : fetch_word AsanUbsan.M.loaded_segments (0x600cc : word) = Some W_60084.
Proof. vm_refl. Qed.
Lemma D_60084 : decode_any W_60084 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60088 : bv 32 := 0x03a13023.
Lemma F_60088 : fetch_word AsanUbsan.M.loaded_segments (0x600d0 : word) = Some W_60088.
Proof. vm_refl. Qed.
Lemma D_60088 : decode_any W_60088 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6008c : bv 32 := 0x01b13c23.
Lemma F_6008c : fetch_word AsanUbsan.M.loaded_segments (0x600d4 : word) = Some W_6008c.
Proof. vm_refl. Qed.
Lemma D_6008c : decode_any W_6008c = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60090 : bv 32 := 0x00050493.
Lemma F_60090 : fetch_word AsanUbsan.M.loaded_segments (0x600d8 : word) = Some W_60090.
Proof. vm_refl. Qed.
Lemma D_60090 : decode_any W_60090 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60094 : bv 32 := 0x00000793.
Lemma F_60094 : fetch_word AsanUbsan.M.loaded_segments (0x600dc : word) = Some W_60094.
Proof. vm_refl. Qed.
Lemma D_60094 : decode_any W_60094 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60098 : bv 32 := 0x00100b93.
Lemma F_60098 : fetch_word AsanUbsan.M.loaded_segments (0x600e0 : word) = Some W_60098.
Proof. vm_refl. Qed.
Lemma D_60098 : decode_any W_60098 = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6009c : bv 32 := 0x02053a03.
Lemma F_6009c : fetch_word AsanUbsan.M.loaded_segments (0x600e4 : word) = Some W_6009c.
Proof. vm_refl. Qed.
Lemma D_6009c : decode_any W_6009c = Some (Load SZ8 true 20 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a0 : bv 32 := 0x03053403.
Lemma F_600a0 : fetch_word AsanUbsan.M.loaded_segments (0x600e8 : word) = Some W_600a0.
Proof. vm_refl. Qed.
Lemma D_600a0 : decode_any W_600a0 = Some (Load SZ8 true 8 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a4 : bv 32 := 0x00761513.
Lemma F_600a4 : fetch_word AsanUbsan.M.loaded_segments (0x600ec : word) = Some W_600a4.
Proof. vm_refl. Qed.
Lemma D_600a4 : decode_any W_600a4 = Some (ShiftImm ALU_SLL 10 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a8 : bv 32 := 0x02061893.
Lemma F_600a8 : fetch_word AsanUbsan.M.loaded_segments (0x600f0 : word) = Some W_600a8.
Proof. vm_refl. Qed.
Lemma D_600a8 : decode_any W_600a8 = Some (ShiftImm ALU_SLL 17 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600ac : bv 32 := 0x00700293.
Lemma F_600ac : fetch_word AsanUbsan.M.loaded_segments (0x600f4 : word) = Some W_600ac.
Proof. vm_refl. Qed.
Lemma D_600ac : decode_any W_600ac = Some (OpImm ALU_ADD 5 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b0 : bv 32 := 0xfff00813.
Lemma F_600b0 : fetch_word AsanUbsan.M.loaded_segments (0x600f8 : word) = Some W_600b0.
Proof. vm_refl. Qed.
Lemma D_600b0 : decode_any W_600b0 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b4 : bv 32 := 0x03db9993.
Lemma F_600b4 : fetch_word AsanUbsan.M.loaded_segments (0x600fc : word) = Some W_600b4.
Proof. vm_refl. Qed.
Lemma D_600b4 : decode_any W_600b4 = Some (ShiftImm ALU_SLL 19 23 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b8 : bv 32 := 0x01d29293.
Lemma F_600b8 : fetch_word AsanUbsan.M.loaded_segments (0x60100 : word) = Some W_600b8.
Proof. vm_refl. Qed.
Lemma D_600b8 : decode_any W_600b8 = Some (ShiftImm ALU_SLL 5 5 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600bc : bv 32 := 0x028b9a93.
Lemma F_600bc : fetch_word AsanUbsan.M.loaded_segments (0x60104 : word) = Some W_600bc.
Proof. vm_refl. Qed.
Lemma D_600bc : decode_any W_600bc = Some (ShiftImm ALU_SLL 21 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c0 : bv 32 := 0x005888b3.
Lemma F_600c0 : fetch_word AsanUbsan.M.loaded_segments (0x60108 : word) = Some W_600c0.
Proof. vm_refl. Qed.
Lemma D_600c0 : decode_any W_600c0 = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c4 : bv 32 := 0x001a8293.
Lemma F_600c4 : fetch_word AsanUbsan.M.loaded_segments (0x6010c : word) = Some W_600c4.
Proof. vm_refl. Qed.
Lemma D_600c4 : decode_any W_600c4 = Some (OpImm ALU_ADD 5 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c8 : bv 32 := 0x01429293.
Lemma F_600c8 : fetch_word AsanUbsan.M.loaded_segments (0x60110 : word) = Some W_600c8.
Proof. vm_refl. Qed.
Lemma D_600c8 : decode_any W_600c8 = Some (ShiftImm ALU_SLL 5 5 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600cc : bv 32 := 0x00a40433.
Lemma F_600cc : fetch_word AsanUbsan.M.loaded_segments (0x60114 : word) = Some W_600cc.
Proof. vm_refl. Qed.
Lemma D_600cc : decode_any W_600cc = Some (Op ALU_ADD 8 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d0 : bv 32 := 0x011a0a33.
Lemma F_600d0 : fetch_word AsanUbsan.M.loaded_segments (0x60118 : word) = Some W_600d0.
Proof. vm_refl. Qed.
Lemma D_600d0 : decode_any W_600d0 = Some (Op ALU_ADD 20 20 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d4 : bv 32 := 0xfff28b13.
Lemma F_600d4 : fetch_word AsanUbsan.M.loaded_segments (0x6011c : word) = Some W_600d4.
Proof. vm_refl. Qed.
Lemma D_600d4 : decode_any W_600d4 = Some (OpImm ALU_ADD 22 5 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d8 : bv 32 := 0x00043883.
Lemma F_600d8 : fetch_word AsanUbsan.M.loaded_segments (0x60120 : word) = Some W_600d8.
Proof. vm_refl. Qed.
Lemma D_600d8 : decode_any W_600d8 = Some (Load SZ8 true 17 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600dc : bv 32 := 0x00840513.
Lemma F_600dc : fetch_word AsanUbsan.M.loaded_segments (0x60124 : word) = Some W_600dc.
Proof. vm_refl. Qed.
Lemma D_600dc : decode_any W_600dc = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e0 : bv 32 := 0x03cb9b93.
Lemma F_600e0 : fetch_word AsanUbsan.M.loaded_segments (0x60128 : word) = Some W_600e0.
Proof. vm_refl. Qed.
Lemma D_600e0 : decode_any W_600e0 = Some (ShiftImm ALU_SLL 23 23 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e4 : bv 32 := 0x5dc00c13.
Lemma F_600e4 : fetch_word AsanUbsan.M.loaded_segments (0x6012c : word) = Some W_600e4.
Proof. vm_refl. Qed.
Lemma D_600e4 : decode_any W_600e4 = Some (OpImm ALU_ADD 24 0 1500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e8 : bv 32 := 0x03d81c93.
Lemma F_600e8 : fetch_word AsanUbsan.M.loaded_segments (0x60130 : word) = Some W_600e8.
Proof. vm_refl. Qed.
Lemma D_600e8 : decode_any W_600e8 = Some (ShiftImm ALU_SLL 25 16 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600ec : bv 32 := 0xfffc8c93.
Lemma F_600ec : fetch_word AsanUbsan.M.loaded_segments (0x60134 : word) = Some W_600ec.
Proof. vm_refl. Qed.
Lemma D_600ec : decode_any W_600ec = Some (OpImm ALU_ADD 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f0 : bv 32 := 0x0168f2b3.
Lemma F_600f0 : fetch_word AsanUbsan.M.loaded_segments (0x60138 : word) = Some W_600f0.
Proof. vm_refl. Qed.
Lemma D_600f0 : decode_any W_600f0 = Some (Op ALU_AND 5 17 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f4 : bv 32 := 0x02029663.
Lemma F_600f4 : fetch_word AsanUbsan.M.loaded_segments (0x6013c : word) = Some W_600f4.
Proof. vm_refl. Qed.
Lemma D_600f4 : decode_any W_600f4 = Some (Branch BC_NE 5 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f8 : bv 32 := 0x0178e2b3.
Lemma F_600f8 : fetch_word AsanUbsan.M.loaded_segments (0x60140 : word) = Some W_600f8.
Proof. vm_refl. Qed.
Lemma D_600f8 : decode_any W_600f8 = Some (Op ALU_OR 5 17 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600fc : bv 32 := 0x00587333.
Lemma F_600fc : fetch_word AsanUbsan.M.loaded_segments (0x60144 : word) = Some W_600fc.
Proof. vm_refl. Qed.
Lemma D_600fc : decode_any W_600fc = Some (Op ALU_AND 6 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60100 : bv 32 := 0x160432af.
Lemma F_60100 : fetch_word AsanUbsan.M.loaded_segments (0x60148 : word) = Some W_60100.
Proof. vm_refl. Qed.
Lemma D_60100 : decode_any W_60100 = Some (Lr AD true true 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60104 : bv 32 := 0x01129663.
Lemma F_60104 : fetch_word AsanUbsan.M.loaded_segments (0x6014c : word) = Some W_60104.
Proof. vm_refl. Qed.
Lemma D_60104 : decode_any W_60104 = Some (Branch BC_NE 5 17 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60108 : bv 32 := 0x1a6433af.
Lemma F_60108 : fetch_word AsanUbsan.M.loaded_segments (0x60150 : word) = Some W_60108.
Proof. vm_refl. Qed.
Lemma D_60108 : decode_any W_60108 = Some (Sc AD false true 7 8 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6010c : bv 32 := 0xfe039ae3.
Lemma F_6010c : fetch_word AsanUbsan.M.loaded_segments (0x60154 : word) = Some W_6010c.
Proof. vm_refl. Qed.
Lemma D_6010c : decode_any W_6010c = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60110 : bv 32 := 0x09128c63.
Lemma F_60110 : fetch_word AsanUbsan.M.loaded_segments (0x60158 : word) = Some W_60110.
Proof. vm_refl. Qed.
Lemma D_60110 : decode_any W_60110 = Some (Branch BC_EQ 5 17 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a8 : bv 32 := 0x01043783.
Lemma F_601a8 : fetch_word AsanUbsan.M.loaded_segments (0x601f0 : word) = Some W_601a8.
Proof. vm_refl. Qed.
Lemma D_601a8 : decode_any W_601a8 = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601ac : bv 32 := 0x14e7e663.
Lemma F_601ac : fetch_word AsanUbsan.M.loaded_segments (0x601f4 : word) = Some W_601ac.
Proof. vm_refl. Qed.
Lemma D_601ac : decode_any W_601ac = Some (Branch BC_LTU 15 14 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b0 : bv 32 := 0x40e787b3.
Lemma F_601b0 : fetch_word AsanUbsan.M.loaded_segments (0x601f8 : word) = Some W_601b0.
Proof. vm_refl. Qed.
Lemma D_601b0 : decode_any W_601b0 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b4 : bv 32 := 0x00f43823.
Lemma F_601b4 : fetch_word AsanUbsan.M.loaded_segments (0x601fc : word) = Some W_601b4.
Proof. vm_refl. Qed.
Lemma D_601b4 : decode_any W_601b4 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b8 : bv 32 := 0x02070463.
Lemma F_601b8 : fetch_word AsanUbsan.M.loaded_segments (0x60200 : word) = Some W_601b8.
Proof. vm_refl. Qed.
Lemma D_601b8 : decode_any W_601b8 = Some (Branch BC_EQ 14 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601bc : bv 32 := 0x00279793.
Lemma F_601bc : fetch_word AsanUbsan.M.loaded_segments (0x60204 : word) = Some W_601bc.
Proof. vm_refl. Qed.
Lemma D_601bc : decode_any W_601bc = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c0 : bv 32 := 0x00fa0a33.
Lemma F_601c0 : fetch_word AsanUbsan.M.loaded_segments (0x60208 : word) = Some W_601c0.
Proof. vm_refl. Qed.
Lemma D_601c0 : decode_any W_601c0 = Some (Op ALU_ADD 20 20 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c4 : bv 32 := 0x00271593.
Lemma F_601c4 : fetch_word AsanUbsan.M.loaded_segments (0x6020c : word) = Some W_601c4.
Proof. vm_refl. Qed.
Lemma D_601c4 : decode_any W_601c4 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c8 : bv 32 := 0x00b685b3.
Lemma F_601c8 : fetch_word AsanUbsan.M.loaded_segments (0x60210 : word) = Some W_601c8.
Proof. vm_refl. Qed.
Lemma D_601c8 : decode_any W_601c8 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601cc : bv 32 := 0x000a2603.
Lemma F_601cc : fetch_word AsanUbsan.M.loaded_segments (0x60214 : word) = Some W_601cc.
Proof. vm_refl. Qed.
Lemma D_601cc : decode_any W_601cc = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d0 : bv 32 := 0x00c6a023.
Lemma F_601d0 : fetch_word AsanUbsan.M.loaded_segments (0x60218 : word) = Some W_601d0.
Proof. vm_refl. Qed.
Lemma D_601d0 : decode_any W_601d0 = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d4 : bv 32 := 0x00468693.
Lemma F_601d4 : fetch_word AsanUbsan.M.loaded_segments (0x6021c : word) = Some W_601d4.
Proof. vm_refl. Qed.
Lemma D_601d4 : decode_any W_601d4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d8 : bv 32 := 0x004a0a13.
Lemma F_601d8 : fetch_word AsanUbsan.M.loaded_segments (0x60220 : word) = Some W_601d8.
Proof. vm_refl. Qed.
Lemma D_601d8 : decode_any W_601d8 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601dc : bv 32 := 0xfeb698e3.
Lemma F_601dc : fetch_word AsanUbsan.M.loaded_segments (0x60224 : word) = Some W_601dc.
Proof. vm_refl. Qed.
Lemma D_601dc : decode_any W_601dc = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e0 : bv 32 := 0x04843583.
Lemma F_601e0 : fetch_word AsanUbsan.M.loaded_segments (0x60228 : word) = Some W_601e0.
Proof. vm_refl. Qed.
Lemma D_601e0 : decode_any W_601e0 = Some (Load SZ8 true 11 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e4 : bv 32 := 0x00e585b3.
Lemma F_601e4 : fetch_word AsanUbsan.M.loaded_segments (0x6022c : word) = Some W_601e4.
Proof. vm_refl. Qed.
Lemma D_601e4 : decode_any W_601e4 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e8 : bv 32 := 0x04b43423.
Lemma F_601e8 : fetch_word AsanUbsan.M.loaded_segments (0x60230 : word) = Some W_601e8.
Proof. vm_refl. Qed.
Lemma D_601e8 : decode_any W_601e8 = Some (Store SZ8 8 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601ec : bv 32 := 0x00100493.
Lemma F_601ec : fetch_word AsanUbsan.M.loaded_segments (0x60234 : word) = Some W_601ec.
Proof. vm_refl. Qed.
Lemma D_601ec : decode_any W_601ec = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f0 : bv 32 := 0x00043603.
Lemma F_601f0 : fetch_word AsanUbsan.M.loaded_segments (0x60238 : word) = Some W_601f0.
Proof. vm_refl. Qed.
Lemma D_601f0 : decode_any W_601f0 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f4 : bv 32 := 0xfff00893.
Lemma F_601f4 : fetch_word AsanUbsan.M.loaded_segments (0x6023c : word) = Some W_601f4.
Proof. vm_refl. Qed.
Lemma D_601f4 : decode_any W_601f4 = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f8 : bv 32 := 0x00300693.
Lemma F_601f8 : fetch_word AsanUbsan.M.loaded_segments (0x60240 : word) = Some W_601f8.
Proof. vm_refl. Qed.
Lemma D_601f8 : decode_any W_601f8 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601fc : bv 32 := 0x001005b7.
Lemma F_601fc : fetch_word AsanUbsan.M.loaded_segments (0x60244 : word) = Some W_601fc.
Proof. vm_refl. Qed.
Lemma D_601fc : decode_any W_601fc = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60200 : bv 32 := 0xfffb0717.
Lemma F_60200 : fetch_word AsanUbsan.M.loaded_segments (0x60248 : word) = Some W_60200.
Proof. vm_refl. Qed.
Lemma D_60200 : decode_any W_60200 = Some (Auipc 14 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60204 : bv 32 := 0x03c89793.
Lemma F_60204 : fetch_word AsanUbsan.M.loaded_segments (0x6024c : word) = Some W_60204.
Proof. vm_refl. Qed.
Lemma D_60204 : decode_any W_60204 = Some (ShiftImm ALU_SLL 15 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60208 : bv 32 := 0x03d69693.
Lemma F_60208 : fetch_word AsanUbsan.M.loaded_segments (0x60250 : word) = Some W_60208.
Proof. vm_refl. Qed.
Lemma D_60208 : decode_any W_60208 = Some (ShiftImm ALU_SLL 13 13 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6020c : bv 32 := 0xfff58593.
Lemma F_6020c : fetch_word AsanUbsan.M.loaded_segments (0x60254 : word) = Some W_6020c.
Proof. vm_refl. Qed.
Lemma D_6020c : decode_any W_6020c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60210 : bv 32 := 0x21073703.
Lemma F_60210 : fetch_word AsanUbsan.M.loaded_segments (0x60258 : word) = Some W_60210.
Proof. vm_refl. Qed.
Lemma D_60210 : decode_any W_60210 = Some (Load SZ8 true 14 14 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60214 : bv 32 := 0xfff78793.
Lemma F_60214 : fetch_word AsanUbsan.M.loaded_segments (0x6025c : word) = Some W_60214.
Proof. vm_refl. Qed.
Lemma D_60214 : decode_any W_60214 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60218 : bv 32 := 0x02859813.
Lemma F_60218 : fetch_word AsanUbsan.M.loaded_segments (0x60260 : word) = Some W_60218.
Proof. vm_refl. Qed.
Lemma D_60218 : decode_any W_60218 = Some (ShiftImm ALU_SLL 16 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6021c : bv 32 := 0x02889893.
Lemma F_6021c : fetch_word AsanUbsan.M.loaded_segments (0x60264 : word) = Some W_6021c.
Proof. vm_refl. Qed.
Lemma D_6021c : decode_any W_6021c = Some (ShiftImm ALU_SLL 17 17 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60220 : bv 32 := 0x00100293.
Lemma F_60220 : fetch_word AsanUbsan.M.loaded_segments (0x60268 : word) = Some W_60220.
Proof. vm_refl. Qed.
Lemma D_60220 : decode_any W_60220 = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60224 : bv 32 := 0x03e29293.
Lemma F_60224 : fetch_word AsanUbsan.M.loaded_segments (0x6026c : word) = Some W_60224.
Proof. vm_refl. Qed.
Lemma D_60224 : decode_any W_60224 = Some (ShiftImm ALU_SLL 5 5 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60228 : bv 32 := 0x01c0006f.
Lemma F_60228 : fetch_word AsanUbsan.M.loaded_segments (0x60270 : word) = Some W_60228.
Proof. vm_refl. Qed.
Lemma D_60228 : decode_any W_60228 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6022c : bv 32 := 0x160433af.
Lemma F_6022c : fetch_word AsanUbsan.M.loaded_segments (0x60274 : word) = Some W_6022c.
Proof. vm_refl. Qed.
Lemma D_6022c : decode_any W_6022c = Some (Lr AD true true 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60230 : bv 32 := 0x00c39663.
Lemma F_60230 : fetch_word AsanUbsan.M.loaded_segments (0x60278 : word) = Some W_60230.
Proof. vm_refl. Qed.
Lemma D_60230 : decode_any W_60230 = Some (Branch BC_NE 7 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60234 : bv 32 := 0x1a643e2f.
Lemma F_60234 : fetch_word AsanUbsan.M.loaded_segments (0x6027c : word) = Some W_60234.
Proof. vm_refl. Qed.
Lemma D_60234 : decode_any W_60234 = Some (Sc AD false true 28 8 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60238 : bv 32 := 0xfe0e1ae3.
Lemma F_60238 : fetch_word AsanUbsan.M.loaded_segments (0x60280 : word) = Some W_60238.
Proof. vm_refl. Qed.
Lemma D_60238 : decode_any W_60238 = Some (Branch BC_NE 28 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6023c : bv 32 := 0x06c38463.
Lemma F_6023c : fetch_word AsanUbsan.M.loaded_segments (0x60284 : word) = Some W_6023c.
Proof. vm_refl. Qed.
Lemma D_6023c : decode_any W_6023c = Some (Branch BC_EQ 7 12 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60244 : bv 32 := 0x00d675b3.
Lemma F_60244 : fetch_word AsanUbsan.M.loaded_segments (0x6028c : word) = Some W_60244.
Proof. vm_refl. Qed.
Lemma D_60244 : decode_any W_60244 = Some (Op ALU_AND 11 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60248 : bv 32 := 0x00f67333.
Lemma F_60248 : fetch_word AsanUbsan.M.loaded_segments (0x60290 : word) = Some W_60248.
Proof. vm_refl. Qed.
Lemma D_60248 : decode_any W_60248 = Some (Op ALU_AND 6 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6024c : bv 32 := 0x02059663.
Lemma F_6024c : fetch_word AsanUbsan.M.loaded_segments (0x60294 : word) = Some W_6024c.
Proof. vm_refl. Qed.
Lemma D_6024c : decode_any W_6024c = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60250 : bv 32 := 0x010675b3.
Lemma F_60250 : fetch_word AsanUbsan.M.loaded_segments (0x60298 : word) = Some W_60250.
Proof. vm_refl. Qed.
Lemma D_60250 : decode_any W_60250 = Some (Op ALU_AND 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60254 : bv 32 := 0x02058263.
Lemma F_60254 : fetch_word AsanUbsan.M.loaded_segments (0x6029c : word) = Some W_60254.
Proof. vm_refl. Qed.
Lemma D_60254 : decode_any W_60254 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60278 : bv 32 := 0x013675b3.
Lemma F_60278 : fetch_word AsanUbsan.M.loaded_segments (0x602c0 : word) = Some W_60278.
Proof. vm_refl. Qed.
Lemma D_60278 : decode_any W_60278 = Some (Op ALU_AND 11 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6027c : bv 32 := 0x00b035b3.
Lemma F_6027c : fetch_word AsanUbsan.M.loaded_segments (0x602c4 : word) = Some W_6027c.
Proof. vm_refl. Qed.
Lemma D_6027c : decode_any W_6027c = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60280 : bv 32 := 0x01465393.
Lemma F_60280 : fetch_word AsanUbsan.M.loaded_segments (0x602c8 : word) = Some W_60280.
Proof. vm_refl. Qed.
Lemma D_60280 : decode_any W_60280 = Some (ShiftImm ALU_SRL 7 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60284 : bv 32 := 0xfff58593.
Lemma F_60284 : fetch_word AsanUbsan.M.loaded_segments (0x602cc : word) = Some W_60284.
Proof. vm_refl. Qed.
Lemma D_60284 : decode_any W_60284 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60288 : bv 32 := 0x00b3f5b3.
Lemma F_60288 : fetch_word AsanUbsan.M.loaded_segments (0x602d0 : word) = Some W_60288.
Proof. vm_refl. Qed.
Lemma D_60288 : decode_any W_60288 = Some (Op ALU_AND 11 7 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6028c : bv 32 := 0x02c59593.
Lemma F_6028c : fetch_word AsanUbsan.M.loaded_segments (0x602d4 : word) = Some W_6028c.
Proof. vm_refl. Qed.
Lemma D_6028c : decode_any W_6028c = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60290 : bv 32 := 0x02c5d593.
Lemma F_60290 : fetch_word AsanUbsan.M.loaded_segments (0x602d8 : word) = Some W_60290.
Proof. vm_refl. Qed.
Lemma D_60290 : decode_any W_60290 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60294 : bv 32 := 0xf8058ce3.
Lemma F_60294 : fetch_word AsanUbsan.M.loaded_segments (0x602dc : word) = Some W_60294.
Proof. vm_refl. Qed.
Lemma D_60294 : decode_any W_60294 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602a4 : bv 32 := 0x00058a63.
Lemma F_602a4 : fetch_word AsanUbsan.M.loaded_segments (0x602ec : word) = Some W_602a4.
Proof. vm_refl. Qed.
Lemma D_602a4 : decode_any W_602a4 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602b8 : bv 32 := 0x00048513.
Lemma F_602b8 : fetch_word AsanUbsan.M.loaded_segments (0x60300 : word) = Some W_602b8.
Proof. vm_refl. Qed.
Lemma D_602b8 : decode_any W_602b8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602bc : bv 32 := 0x07813083.
Lemma F_602bc : fetch_word AsanUbsan.M.loaded_segments (0x60304 : word) = Some W_602bc.
Proof. vm_refl. Qed.
Lemma D_602bc : decode_any W_602bc = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602c0 : bv 32 := 0x07013403.
Lemma F_602c0 : fetch_word AsanUbsan.M.loaded_segments (0x60308 : word) = Some W_602c0.
Proof. vm_refl. Qed.
Lemma D_602c0 : decode_any W_602c0 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602c4 : bv 32 := 0x06813483.
Lemma F_602c4 : fetch_word AsanUbsan.M.loaded_segments (0x6030c : word) = Some W_602c4.
Proof. vm_refl. Qed.
Lemma D_602c4 : decode_any W_602c4 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602c8 : bv 32 := 0x06013903.
Lemma F_602c8 : fetch_word AsanUbsan.M.loaded_segments (0x60310 : word) = Some W_602c8.
Proof. vm_refl. Qed.
Lemma D_602c8 : decode_any W_602c8 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602cc : bv 32 := 0x05813983.
Lemma F_602cc : fetch_word AsanUbsan.M.loaded_segments (0x60314 : word) = Some W_602cc.
Proof. vm_refl. Qed.
Lemma D_602cc : decode_any W_602cc = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602d0 : bv 32 := 0x05013a03.
Lemma F_602d0 : fetch_word AsanUbsan.M.loaded_segments (0x60318 : word) = Some W_602d0.
Proof. vm_refl. Qed.
Lemma D_602d0 : decode_any W_602d0 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602d4 : bv 32 := 0x04813a83.
Lemma F_602d4 : fetch_word AsanUbsan.M.loaded_segments (0x6031c : word) = Some W_602d4.
Proof. vm_refl. Qed.
Lemma D_602d4 : decode_any W_602d4 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602d8 : bv 32 := 0x04013b03.
Lemma F_602d8 : fetch_word AsanUbsan.M.loaded_segments (0x60320 : word) = Some W_602d8.
Proof. vm_refl. Qed.
Lemma D_602d8 : decode_any W_602d8 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602dc : bv 32 := 0x03813b83.
Lemma F_602dc : fetch_word AsanUbsan.M.loaded_segments (0x60324 : word) = Some W_602dc.
Proof. vm_refl. Qed.
Lemma D_602dc : decode_any W_602dc = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602e0 : bv 32 := 0x03013c03.
Lemma F_602e0 : fetch_word AsanUbsan.M.loaded_segments (0x60328 : word) = Some W_602e0.
Proof. vm_refl. Qed.
Lemma D_602e0 : decode_any W_602e0 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602e4 : bv 32 := 0x02813c83.
Lemma F_602e4 : fetch_word AsanUbsan.M.loaded_segments (0x6032c : word) = Some W_602e4.
Proof. vm_refl. Qed.
Lemma D_602e4 : decode_any W_602e4 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602e8 : bv 32 := 0x02013d03.
Lemma F_602e8 : fetch_word AsanUbsan.M.loaded_segments (0x60330 : word) = Some W_602e8.
Proof. vm_refl. Qed.
Lemma D_602e8 : decode_any W_602e8 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602ec : bv 32 := 0x01813d83.
Lemma F_602ec : fetch_word AsanUbsan.M.loaded_segments (0x60334 : word) = Some W_602ec.
Proof. vm_refl. Qed.
Lemma D_602ec : decode_any W_602ec = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602f0 : bv 32 := 0x08010113.
Lemma F_602f0 : fetch_word AsanUbsan.M.loaded_segments (0x60338 : word) = Some W_602f0.
Proof. vm_refl. Qed.
Lemma D_602f0 : decode_any W_602f0 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602f4 : bv 32 := 0x00008067.
Lemma F_602f4 : fetch_word AsanUbsan.M.loaded_segments (0x6033c : word) = Some W_602f4.
Proof. vm_refl. Qed.
Lemma D_602f4 : decode_any W_602f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602f8 : bv 32 := 0x00068a93.
Lemma F_602f8 : fetch_word AsanUbsan.M.loaded_segments (0x60340 : word) = Some W_602f8.
Proof. vm_refl. Qed.
Lemma D_602f8 : decode_any W_602f8 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_602fc : bv 32 := 0x00050913.
Lemma F_602fc : fetch_word AsanUbsan.M.loaded_segments (0x60344 : word) = Some W_602fc.
Proof. vm_refl. Qed.
Lemma D_602fc : decode_any W_602fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60300 : bv 32 := 0x00070b13.
Lemma F_60300 : fetch_word AsanUbsan.M.loaded_segments (0x60348 : word) = Some W_60300.
Proof. vm_refl. Qed.
Lemma D_60300 : decode_any W_60300 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60304 : bv 32 := 0x40f70733.
Lemma F_60304 : fetch_word AsanUbsan.M.loaded_segments (0x6034c : word) = Some W_60304.
Proof. vm_refl. Qed.
Lemma D_60304 : decode_any W_60304 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60308 : bv 32 := 0x00048513.
Lemma F_60308 : fetch_word AsanUbsan.M.loaded_segments (0x60350 : word) = Some W_60308.
Proof. vm_refl. Qed.
Lemma D_60308 : decode_any W_60308 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6030c : bv 32 := 0x00040693.
Lemma F_6030c : fetch_word AsanUbsan.M.loaded_segments (0x60354 : word) = Some W_6030c.
Proof. vm_refl. Qed.
Lemma D_6030c : decode_any W_6030c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60310 : bv 32 := 0x050000ef.
Lemma F_60310 : fetch_word AsanUbsan.M.loaded_segments (0x60358 : word) = Some W_60310.
Proof. vm_refl. Qed.
Lemma D_60310 : decode_any W_60310 = Some (Jal 1 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60314 : bv 32 := 0x02050263.
Lemma F_60314 : fetch_word AsanUbsan.M.loaded_segments (0x6035c : word) = Some W_60314.
Proof. vm_refl. Qed.
Lemma D_60314 : decode_any W_60314 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60318 : bv 32 := 0x01043783.
Lemma F_60318 : fetch_word AsanUbsan.M.loaded_segments (0x60360 : word) = Some W_60318.
Proof. vm_refl. Qed.
Lemma D_60318 : decode_any W_60318 = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6031c : bv 32 := 0x000b0713.
Lemma F_6031c : fetch_word AsanUbsan.M.loaded_segments (0x60364 : word) = Some W_6031c.
Proof. vm_refl. Qed.
Lemma D_6031c : decode_any W_6031c = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60320 : bv 32 := 0x0367e263.
Lemma F_60320 : fetch_word AsanUbsan.M.loaded_segments (0x60368 : word) = Some W_60320.
Proof. vm_refl. Qed.
Lemma D_60320 : decode_any W_60320 = Some (Branch BC_LTU 15 22 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60324 : bv 32 := 0x000a8693.
Lemma F_60324 : fetch_word AsanUbsan.M.loaded_segments (0x6036c : word) = Some W_60324.
Proof. vm_refl. Qed.
Lemma D_60324 : decode_any W_60324 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60328 : bv 32 := 0x40e787b3.
Lemma F_60328 : fetch_word AsanUbsan.M.loaded_segments (0x60370 : word) = Some W_60328.
Proof. vm_refl. Qed.
Lemma D_60328 : decode_any W_60328 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6032c : bv 32 := 0x00f43823.
Lemma F_6032c : fetch_word AsanUbsan.M.loaded_segments (0x60374 : word) = Some W_6032c.
Proof. vm_refl. Qed.
Lemma D_6032c : decode_any W_6032c = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60330 : bv 32 := 0x00090513.
Lemma F_60330 : fetch_word AsanUbsan.M.loaded_segments (0x60378 : word) = Some W_60330.
Proof. vm_refl. Qed.
Lemma D_60330 : decode_any W_60330 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60334 : bv 32 := 0xe89ff06f.
Lemma F_60334 : fetch_word AsanUbsan.M.loaded_segments (0x6037c : word) = Some W_60334.
Proof. vm_refl. Qed.
Lemma D_60334 : decode_any W_60334 = Some (Jal 0 2096776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60360 : bv 32 := 0xfc010113.
Lemma F_60360 : fetch_word AsanUbsan.M.loaded_segments (0x603a8 : word) = Some W_60360.
Proof. vm_refl. Qed.
Lemma D_60360 : decode_any W_60360 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60364 : bv 32 := 0x02113c23.
Lemma F_60364 : fetch_word AsanUbsan.M.loaded_segments (0x603ac : word) = Some W_60364.
Proof. vm_refl. Qed.
Lemma D_60364 : decode_any W_60364 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60368 : bv 32 := 0x02813823.
Lemma F_60368 : fetch_word AsanUbsan.M.loaded_segments (0x603b0 : word) = Some W_60368.
Proof. vm_refl. Qed.
Lemma D_60368 : decode_any W_60368 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6036c : bv 32 := 0x02913423.
Lemma F_6036c : fetch_word AsanUbsan.M.loaded_segments (0x603b4 : word) = Some W_6036c.
Proof. vm_refl. Qed.
Lemma D_6036c : decode_any W_6036c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60370 : bv 32 := 0x03213023.
Lemma F_60370 : fetch_word AsanUbsan.M.loaded_segments (0x603b8 : word) = Some W_60370.
Proof. vm_refl. Qed.
Lemma D_60370 : decode_any W_60370 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60374 : bv 32 := 0x01313c23.
Lemma F_60374 : fetch_word AsanUbsan.M.loaded_segments (0x603bc : word) = Some W_60374.
Proof. vm_refl. Qed.
Lemma D_60374 : decode_any W_60374 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60378 : bv 32 := 0x01413823.
Lemma F_60378 : fetch_word AsanUbsan.M.loaded_segments (0x603c0 : word) = Some W_60378.
Proof. vm_refl. Qed.
Lemma D_60378 : decode_any W_60378 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6037c : bv 32 := 0x01513423.
Lemma F_6037c : fetch_word AsanUbsan.M.loaded_segments (0x603c4 : word) = Some W_6037c.
Proof. vm_refl. Qed.
Lemma D_6037c : decode_any W_6037c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60380 : bv 32 := 0x01613023.
Lemma F_60380 : fetch_word AsanUbsan.M.loaded_segments (0x603c8 : word) = Some W_60380.
Proof. vm_refl. Qed.
Lemma D_60380 : decode_any W_60380 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60384 : bv 32 := 0x00068413.
Lemma F_60384 : fetch_word AsanUbsan.M.loaded_segments (0x603cc : word) = Some W_60384.
Proof. vm_refl. Qed.
Lemma D_60384 : decode_any W_60384 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60388 : bv 32 := 0x00058493.
Lemma F_60388 : fetch_word AsanUbsan.M.loaded_segments (0x603d0 : word) = Some W_60388.
Proof. vm_refl. Qed.
Lemma D_60388 : decode_any W_60388 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6038c : bv 32 := 0x02053903.
Lemma F_6038c : fetch_word AsanUbsan.M.loaded_segments (0x603d4 : word) = Some W_6038c.
Proof. vm_refl. Qed.
Lemma D_6038c : decode_any W_6038c = Some (Load SZ8 true 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60390 : bv 32 := 0x01f00693.
Lemma F_60390 : fetch_word AsanUbsan.M.loaded_segments (0x603d8 : word) = Some W_60390.
Proof. vm_refl. Qed.
Lemma D_60390 : decode_any W_60390 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60394 : bv 32 := 0x02061593.
Lemma F_60394 : fetch_word AsanUbsan.M.loaded_segments (0x603dc : word) = Some W_60394.
Proof. vm_refl. Qed.
Lemma D_60394 : decode_any W_60394 = Some (ShiftImm ALU_SLL 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60398 : bv 32 := 0x20d60263.
Lemma F_60398 : fetch_word AsanUbsan.M.loaded_segments (0x603e0 : word) = Some W_60398.
Proof. vm_refl. Qed.
Lemma D_60398 : decode_any W_60398 = Some (Branch BC_EQ 12 13 516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6039c : bv 32 := 0x01000693.
Lemma F_6039c : fetch_word AsanUbsan.M.loaded_segments (0x603e4 : word) = Some W_6039c.
Proof. vm_refl. Qed.
Lemma D_6039c : decode_any W_6039c = Some (OpImm ALU_ADD 13 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603a0 : bv 32 := 0x02c6e263.
Lemma F_603a0 : fetch_word AsanUbsan.M.loaded_segments (0x603e8 : word) = Some W_603a0.
Proof. vm_refl. Qed.
Lemma D_603a0 : decode_any W_603a0 = Some (Branch BC_LTU 13 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603a4 : bv 32 := 0x00561a93.
Lemma F_603a4 : fetch_word AsanUbsan.M.loaded_segments (0x603ec : word) = Some W_603a4.
Proof. vm_refl. Qed.
Lemma D_603a4 : decode_any W_603a4 = Some (ShiftImm ALU_SLL 21 12 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603a8 : bv 32 := 0x02043683.
Lemma F_603a8 : fetch_word AsanUbsan.M.loaded_segments (0x603f0 : word) = Some W_603a8.
Proof. vm_refl. Qed.
Lemma D_603a8 : decode_any W_603a8 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603ac : bv 32 := 0x03043a03.
Lemma F_603ac : fetch_word AsanUbsan.M.loaded_segments (0x603f4 : word) = Some W_603ac.
Proof. vm_refl. Qed.
Lemma D_603ac : decode_any W_603ac = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603b0 : bv 32 := 0x02ea89b3.
Lemma F_603b0 : fetch_word AsanUbsan.M.loaded_segments (0x603f8 : word) = Some W_603b0.
Proof. vm_refl. Qed.
Lemma D_603b0 : decode_any W_603b0 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603b4 : bv 32 := 0x013689b3.
Lemma F_603b4 : fetch_word AsanUbsan.M.loaded_segments (0x603fc : word) = Some W_603b4.
Proof. vm_refl. Qed.
Lemma D_603b4 : decode_any W_603b4 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603b8 : bv 32 := 0x00b90933.
Lemma F_603b8 : fetch_word AsanUbsan.M.loaded_segments (0x60400 : word) = Some W_603b8.
Proof. vm_refl. Qed.
Lemma D_603b8 : decode_any W_603b8 = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603bc : bv 32 := 0x053a6263.
Lemma F_603bc : fetch_word AsanUbsan.M.loaded_segments (0x60404 : word) = Some W_603bc.
Proof. vm_refl. Qed.
Lemma D_603bc : decode_any W_603bc = Some (Branch BC_LTU 20 19 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603c4 : bv 32 := 0xff060693.
Lemma F_603c4 : fetch_word AsanUbsan.M.loaded_segments (0x6040c : word) = Some W_603c4.
Proof. vm_refl. Qed.
Lemma D_603c4 : decode_any W_603c4 = Some (OpImm ALU_ADD 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603c8 : bv 32 := 0x20000793.
Lemma F_603c8 : fetch_word AsanUbsan.M.loaded_segments (0x60410 : word) = Some W_603c8.
Proof. vm_refl. Qed.
Lemma D_603c8 : decode_any W_603c8 = Some (OpImm ALU_ADD 15 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603cc : bv 32 := 0x03f61813.
Lemma F_603cc : fetch_word AsanUbsan.M.loaded_segments (0x60414 : word) = Some W_603cc.
Proof. vm_refl. Qed.
Lemma D_603cc : decode_any W_603cc = Some (ShiftImm ALU_SLL 16 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603d0 : bv 32 := 0x0016d693.
Lemma F_603d0 : fetch_word AsanUbsan.M.loaded_segments (0x60418 : word) = Some W_603d0.
Proof. vm_refl. Qed.
Lemma D_603d0 : decode_any W_603d0 = Some (ShiftImm ALU_SRL 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603d4 : bv 32 := 0x00d79ab3.
Lemma F_603d4 : fetch_word AsanUbsan.M.loaded_segments (0x6041c : word) = Some W_603d4.
Proof. vm_refl. Qed.
Lemma D_603d4 : decode_any W_603d4 = Some (Op ALU_SLL 21 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603d8 : bv 32 := 0x001ad693.
Lemma F_603d8 : fetch_word AsanUbsan.M.loaded_segments (0x60420 : word) = Some W_603d8.
Proof. vm_refl. Qed.
Lemma D_603d8 : decode_any W_603d8 = Some (ShiftImm ALU_SRL 13 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603dc : bv 32 := 0x43f85793.
Lemma F_603dc : fetch_word AsanUbsan.M.loaded_segments (0x60424 : word) = Some W_603dc.
Proof. vm_refl. Qed.
Lemma D_603dc : decode_any W_603dc = Some (ShiftImm ALU_SRA 15 16 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603e0 : bv 32 := 0x00d7f6b3.
Lemma F_603e0 : fetch_word AsanUbsan.M.loaded_segments (0x60428 : word) = Some W_603e0.
Proof. vm_refl. Qed.
Lemma D_603e0 : decode_any W_603e0 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603e4 : bv 32 := 0x01568ab3.
Lemma F_603e4 : fetch_word AsanUbsan.M.loaded_segments (0x6042c : word) = Some W_603e4.
Proof. vm_refl. Qed.
Lemma D_603e4 : decode_any W_603e4 = Some (Op ALU_ADD 21 13 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603e8 : bv 32 := 0x02043683.
Lemma F_603e8 : fetch_word AsanUbsan.M.loaded_segments (0x60430 : word) = Some W_603e8.
Proof. vm_refl. Qed.
Lemma D_603e8 : decode_any W_603e8 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603ec : bv 32 := 0x03043a03.
Lemma F_603ec : fetch_word AsanUbsan.M.loaded_segments (0x60434 : word) = Some W_603ec.
Proof. vm_refl. Qed.
Lemma D_603ec : decode_any W_603ec = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603f0 : bv 32 := 0x02ea89b3.
Lemma F_603f0 : fetch_word AsanUbsan.M.loaded_segments (0x60438 : word) = Some W_603f0.
Proof. vm_refl. Qed.
Lemma D_603f0 : decode_any W_603f0 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603f4 : bv 32 := 0x013689b3.
Lemma F_603f4 : fetch_word AsanUbsan.M.loaded_segments (0x6043c : word) = Some W_603f4.
Proof. vm_refl. Qed.
Lemma D_603f4 : decode_any W_603f4 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603f8 : bv 32 := 0x00b90933.
Lemma F_603f8 : fetch_word AsanUbsan.M.loaded_segments (0x60440 : word) = Some W_603f8.
Proof. vm_refl. Qed.
Lemma D_603f8 : decode_any W_603f8 = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_603fc : bv 32 := 0x0d3a7c63.
Lemma F_603fc : fetch_word AsanUbsan.M.loaded_segments (0x60444 : word) = Some W_603fc.
Proof. vm_refl. Qed.
Lemma D_603fc : decode_any W_603fc = Some (Branch BC_GEU 20 19 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60400 : bv 32 := 0x1a0a0e63.
Lemma F_60400 : fetch_word AsanUbsan.M.loaded_segments (0x60448 : word) = Some W_60400.
Proof. vm_refl. Qed.
Lemma D_60400 : decode_any W_60400 = Some (Branch BC_EQ 20 0 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60404 : bv 32 := 0xfffa4593.
Lemma F_60404 : fetch_word AsanUbsan.M.loaded_segments (0x6044c : word) = Some W_60404.
Proof. vm_refl. Qed.
Lemma D_60404 : decode_any W_60404 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60408 : bv 32 := 0xfffc06b7.
Lemma F_60408 : fetch_word AsanUbsan.M.loaded_segments (0x60450 : word) = Some W_60408.
Proof. vm_refl. Qed.
Lemma D_60408 : decode_any W_60408 = Some (Lui 13 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6040c : bv 32 := 0x00b985b3.
Lemma F_6040c : fetch_word AsanUbsan.M.loaded_segments (0x60454 : word) = Some W_6040c.
Proof. vm_refl. Qed.
Lemma D_6040c : decode_any W_6040c = Some (Op ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60410 : bv 32 := 0x000409b7.
Lemma F_60410 : fetch_word AsanUbsan.M.loaded_segments (0x60458 : word) = Some W_60410.
Proof. vm_refl. Qed.
Lemma D_60410 : decode_any W_60410 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60414 : bv 32 := 0x00d5f5b3.
Lemma F_60414 : fetch_word AsanUbsan.M.loaded_segments (0x6045c : word) = Some W_60414.
Proof. vm_refl. Qed.
Lemma D_60414 : decode_any W_60414 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60418 : bv 32 := 0x03843683.
Lemma F_60418 : fetch_word AsanUbsan.M.loaded_segments (0x60460 : word) = Some W_60418.
Proof. vm_refl. Qed.
Lemma D_60418 : decode_any W_60418 = Some (Load SZ8 true 13 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6041c : bv 32 := 0x013589b3.
Lemma F_6041c : fetch_word AsanUbsan.M.loaded_segments (0x60464 : word) = Some W_6041c.
Proof. vm_refl. Qed.
Lemma D_6041c : decode_any W_6041c = Some (Op ALU_ADD 19 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60420 : bv 32 := 0x00700593.
Lemma F_60420 : fetch_word AsanUbsan.M.loaded_segments (0x60468 : word) = Some W_60420.
Proof. vm_refl. Qed.
Lemma D_60420 : decode_any W_60420 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60424 : bv 32 := 0x01d59593.
Lemma F_60424 : fetch_word AsanUbsan.M.loaded_segments (0x6046c : word) = Some W_60424.
Proof. vm_refl. Qed.
Lemma D_60424 : decode_any W_60424 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60428 : bv 32 := 0x014686b3.
Lemma F_60428 : fetch_word AsanUbsan.M.loaded_segments (0x60470 : word) = Some W_60428.
Proof. vm_refl. Qed.
Lemma D_60428 : decode_any W_60428 = Some (Op ALU_ADD 13 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6042c : bv 32 := 0x013686b3.
Lemma F_6042c : fetch_word AsanUbsan.M.loaded_segments (0x60474 : word) = Some W_6042c.
Proof. vm_refl. Qed.
Lemma D_6042c : decode_any W_6042c = Some (Op ALU_ADD 13 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60430 : bv 32 := 0x00158593.
Lemma F_60430 : fetch_word AsanUbsan.M.loaded_segments (0x60478 : word) = Some W_60430.
Proof. vm_refl. Qed.
Lemma D_60430 : decode_any W_60430 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60434 : bv 32 := 0x1ab6fa63.
Lemma F_60434 : fetch_word AsanUbsan.M.loaded_segments (0x6047c : word) = Some W_60434.
Proof. vm_refl. Qed.
Lemma D_60434 : decode_any W_60434 = Some (Branch BC_GEU 13 11 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60438 : bv 32 := 0x03854583.
Lemma F_60438 : fetch_word AsanUbsan.M.loaded_segments (0x60480 : word) = Some W_60438.
Proof. vm_refl. Qed.
Lemma D_60438 : decode_any W_60438 = Some (Load SZ1 false 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6043c : bv 32 := 0x012a0a33.
Lemma F_6043c : fetch_word AsanUbsan.M.loaded_segments (0x60484 : word) = Some W_6043c.
Proof. vm_refl. Qed.
Lemma D_6043c : decode_any W_6043c = Some (Op ALU_ADD 20 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60440 : bv 32 := 0x02058463.
Lemma F_60440 : fetch_word AsanUbsan.M.loaded_segments (0x60488 : word) = Some W_60440.
Proof. vm_refl. Qed.
Lemma D_60440 : decode_any W_60440 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60468 : bv 32 := 0xfffb8597.
Lemma F_60468 : fetch_word AsanUbsan.M.loaded_segments (0x604b0 : word) = Some W_60468.
Proof. vm_refl. Qed.
Lemma D_60468 : decode_any W_60468 = Some (Auipc 11 1048504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6046c : bv 32 := 0xcac58693.
Lemma F_6046c : fetch_word AsanUbsan.M.loaded_segments (0x604b4 : word) = Some W_6046c.
Proof. vm_refl. Qed.
Lemma D_6046c : decode_any W_6046c = Some (OpImm ALU_ADD 13 11 3244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60470 : bv 32 := 0x00050b13.
Lemma F_60470 : fetch_word AsanUbsan.M.loaded_segments (0x604b8 : word) = Some W_60470.
Proof. vm_refl. Qed.
Lemma D_60470 : decode_any W_60470 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60474 : bv 32 := 0x000a0593.
Lemma F_60474 : fetch_word AsanUbsan.M.loaded_segments (0x604bc : word) = Some W_60474.
Proof. vm_refl. Qed.
Lemma D_60474 : decode_any W_60474 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60478 : bv 32 := 0x00098613.
Lemma F_60478 : fetch_word AsanUbsan.M.loaded_segments (0x604c0 : word) = Some W_60478.
Proof. vm_refl. Qed.
Lemma D_60478 : decode_any W_60478 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6047c : bv 32 := 0x5843e0ef.
Lemma F_6047c : fetch_word AsanUbsan.M.loaded_segments (0x604c4 : word) = Some W_6047c.
Proof. vm_refl. Qed.
Lemma D_6047c : decode_any W_6047c = Some (Jal 1 255364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60480 : bv 32 := 0x16050863.
Lemma F_60480 : fetch_word AsanUbsan.M.loaded_segments (0x604c8 : word) = Some W_60480.
Proof. vm_refl. Qed.
Lemma D_60480 : decode_any W_60480 = Some (Branch BC_EQ 10 0 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60484 : bv 32 := 0x00050713.
Lemma F_60484 : fetch_word AsanUbsan.M.loaded_segments (0x604cc : word) = Some W_60484.
Proof. vm_refl. Qed.
Lemma D_60484 : decode_any W_60484 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60488 : bv 32 := 0x1eaa1063.
Lemma F_60488 : fetch_word AsanUbsan.M.loaded_segments (0x604d0 : word) = Some W_60488.
Proof. vm_refl. Qed.
Lemma D_60488 : decode_any W_60488 = Some (Branch BC_NE 20 10 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6048c : bv 32 := 0x0fa00613.
Lemma F_6048c : fetch_word AsanUbsan.M.loaded_segments (0x604d4 : word) = Some W_6048c.
Proof. vm_refl. Qed.
Lemma D_6048c : decode_any W_6048c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60490 : bv 32 := 0x000a0513.
Lemma F_60490 : fetch_word AsanUbsan.M.loaded_segments (0x604d8 : word) = Some W_60490.
Proof. vm_refl. Qed.
Lemma D_60490 : decode_any W_60490 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60494 : bv 32 := 0x00098593.
Lemma F_60494 : fetch_word AsanUbsan.M.loaded_segments (0x604dc : word) = Some W_60494.
Proof. vm_refl. Qed.
Lemma D_60494 : decode_any W_60494 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60498 : bv 32 := 0x4d4230ef.
Lemma F_60498 : fetch_word AsanUbsan.M.loaded_segments (0x604e0 : word) = Some W_60498.
Proof. vm_refl. Qed.
Lemma D_60498 : decode_any W_60498 = Some (Jal 1 144596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6049c : bv 32 := 0x4482b0ef.
Lemma F_6049c : fetch_word AsanUbsan.M.loaded_segments (0x604e4 : word) = Some W_6049c.
Proof. vm_refl. Qed.
Lemma D_6049c : decode_any W_6049c = Some (Jal 1 177224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604a0 : bv 32 := 0x04853583.
Lemma F_604a0 : fetch_word AsanUbsan.M.loaded_segments (0x604e8 : word) = Some W_604a0.
Proof. vm_refl. Qed.
Lemma D_604a0 : decode_any W_604a0 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604a4 : bv 32 := 0x05053603.
Lemma F_604a4 : fetch_word AsanUbsan.M.loaded_segments (0x604ec : word) = Some W_604a4.
Proof. vm_refl. Qed.
Lemma D_604a4 : decode_any W_604a4 = Some (Load SZ8 true 12 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604a8 : bv 32 := 0x00158593.
Lemma F_604a8 : fetch_word AsanUbsan.M.loaded_segments (0x604f0 : word) = Some W_604a8.
Proof. vm_refl. Qed.
Lemma D_604a8 : decode_any W_604a8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604ac : bv 32 := 0x01360633.
Lemma F_604ac : fetch_word AsanUbsan.M.loaded_segments (0x604f4 : word) = Some W_604ac.
Proof. vm_refl. Qed.
Lemma D_604ac : decode_any W_604ac = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604b0 : bv 32 := 0x04b53423.
Lemma F_604b0 : fetch_word AsanUbsan.M.loaded_segments (0x604f8 : word) = Some W_604b0.
Proof. vm_refl. Qed.
Lemma D_604b0 : decode_any W_604b0 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604b4 : bv 32 := 0x04c53823.
Lemma F_604b4 : fetch_word AsanUbsan.M.loaded_segments (0x604fc : word) = Some W_604b4.
Proof. vm_refl. Qed.
Lemma D_604b4 : decode_any W_604b4 = Some (Store SZ8 10 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604b8 : bv 32 := 0x000b0513.
Lemma F_604b8 : fetch_word AsanUbsan.M.loaded_segments (0x60500 : word) = Some W_604b8.
Proof. vm_refl. Qed.
Lemma D_604b8 : decode_any W_604b8 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604bc : bv 32 := 0x01848493.
Lemma F_604bc : fetch_word AsanUbsan.M.loaded_segments (0x60504 : word) = Some W_604bc.
Proof. vm_refl. Qed.
Lemma D_604bc : decode_any W_604bc = Some (OpImm ALU_ADD 9 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604c0 : bv 32 := 0x0134b02f.
Lemma F_604c0 : fetch_word AsanUbsan.M.loaded_segments (0x60508 : word) = Some W_604c0.
Proof. vm_refl. Qed.
Lemma D_604c0 : decode_any W_604c0 = Some (Amo AMO_ADD AD false false 0 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604c4 : bv 32 := 0x03043a03.
Lemma F_604c4 : fetch_word AsanUbsan.M.loaded_segments (0x6050c : word) = Some W_604c4.
Proof. vm_refl. Qed.
Lemma D_604c4 : decode_any W_604c4 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604c8 : bv 32 := 0x02043683.
Lemma F_604c8 : fetch_word AsanUbsan.M.loaded_segments (0x60510 : word) = Some W_604c8.
Proof. vm_refl. Qed.
Lemma D_604c8 : decode_any W_604c8 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604cc : bv 32 := 0x013a0a33.
Lemma F_604cc : fetch_word AsanUbsan.M.loaded_segments (0x60514 : word) = Some W_604cc.
Proof. vm_refl. Qed.
Lemma D_604cc : decode_any W_604cc = Some (Op ALU_ADD 20 20 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604d0 : bv 32 := 0x03443823.
Lemma F_604d0 : fetch_word AsanUbsan.M.loaded_segments (0x60518 : word) = Some W_604d0.
Proof. vm_refl. Qed.
Lemma D_604d0 : decode_any W_604d0 = Some (Store SZ8 8 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604d4 : bv 32 := 0x01043483.
Lemma F_604d4 : fetch_word AsanUbsan.M.loaded_segments (0x6051c : word) = Some W_604d4.
Proof. vm_refl. Qed.
Lemma D_604d4 : decode_any W_604d4 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604d8 : bv 32 := 0x40da0a33.
Lemma F_604d8 : fetch_word AsanUbsan.M.loaded_segments (0x60520 : word) = Some W_604d8.
Proof. vm_refl. Qed.
Lemma D_604d8 : decode_any W_604d8 = Some (Op ALU_SUB 20 20 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604dc : bv 32 := 0x035a59b3.
Lemma F_604dc : fetch_word AsanUbsan.M.loaded_segments (0x60524 : word) = Some W_604dc.
Proof. vm_refl. Qed.
Lemma D_604dc : decode_any W_604dc = Some (Mul M_DIVU 19 20 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604e0 : bv 32 := 0x013484b3.
Lemma F_604e0 : fetch_word AsanUbsan.M.loaded_segments (0x60528 : word) = Some W_604e0.
Proof. vm_refl. Qed.
Lemma D_604e0 : decode_any W_604e0 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604e4 : bv 32 := 0x00040593.
Lemma F_604e4 : fetch_word AsanUbsan.M.loaded_segments (0x6052c : word) = Some W_604e4.
Proof. vm_refl. Qed.
Lemma D_604e4 : decode_any W_604e4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604e8 : bv 32 := 0x00090613.
Lemma F_604e8 : fetch_word AsanUbsan.M.loaded_segments (0x60530 : word) = Some W_604e8.
Proof. vm_refl. Qed.
Lemma D_604e8 : decode_any W_604e8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604ec : bv 32 := 0x00048693.
Lemma F_604ec : fetch_word AsanUbsan.M.loaded_segments (0x60534 : word) = Some W_604ec.
Proof. vm_refl. Qed.
Lemma D_604ec : decode_any W_604ec = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604f0 : bv 32 := 0xb35fd0ef.
Lemma F_604f0 : fetch_word AsanUbsan.M.loaded_segments (0x60538 : word) = Some W_604f0.
Proof. vm_refl. Qed.
Lemma D_604f0 : decode_any W_604f0 = Some (Jal 1 2087732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604f4 : bv 32 := 0x0e050e63.
Lemma F_604f4 : fetch_word AsanUbsan.M.loaded_segments (0x6053c : word) = Some W_604f4.
Proof. vm_refl. Qed.
Lemma D_604f4 : decode_any W_604f4 = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604f8 : bv 32 := 0x02043683.
Lemma F_604f8 : fetch_word AsanUbsan.M.loaded_segments (0x60540 : word) = Some W_604f8.
Proof. vm_refl. Qed.
Lemma D_604f8 : decode_any W_604f8 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_604fc : bv 32 := 0x055a6063.
Lemma F_604fc : fetch_word AsanUbsan.M.loaded_segments (0x60544 : word) = Some W_604fc.
Proof. vm_refl. Qed.
Lemma D_604fc : decode_any W_604fc = Some (Branch BC_LTU 20 21 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60500 : bv 32 := 0x00000513.
Lemma F_60500 : fetch_word AsanUbsan.M.loaded_segments (0x60548 : word) = Some W_60500.
Proof. vm_refl. Qed.
Lemma D_60500 : decode_any W_60500 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60504 : bv 32 := 0x00700593.
Lemma F_60504 : fetch_word AsanUbsan.M.loaded_segments (0x6054c : word) = Some W_60504.
Proof. vm_refl. Qed.
Lemma D_60504 : decode_any W_60504 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60508 : bv 32 := 0x01d59593.
Lemma F_60508 : fetch_word AsanUbsan.M.loaded_segments (0x60550 : word) = Some W_60508.
Proof. vm_refl. Qed.
Lemma D_60508 : decode_any W_60508 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6050c : bv 32 := 0x00b905b3.
Lemma F_6050c : fetch_word AsanUbsan.M.loaded_segments (0x60554 : word) = Some W_6050c.
Proof. vm_refl. Qed.
Lemma D_6050c : decode_any W_6050c = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60510 : bv 32 := 0x00249493.
Lemma F_60510 : fetch_word AsanUbsan.M.loaded_segments (0x60558 : word) = Some W_60510.
Proof. vm_refl. Qed.
Lemma D_60510 : decode_any W_60510 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60514 : bv 32 := 0x009585b3.
Lemma F_60514 : fetch_word AsanUbsan.M.loaded_segments (0x6055c : word) = Some W_60514.
Proof. vm_refl. Qed.
Lemma D_60514 : decode_any W_60514 = Some (Op ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60518 : bv 32 := 0x00068613.
Lemma F_60518 : fetch_word AsanUbsan.M.loaded_segments (0x60560 : word) = Some W_60518.
Proof. vm_refl. Qed.
Lemma D_60518 : decode_any W_60518 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6051c : bv 32 := 0x00465713.
Lemma F_6051c : fetch_word AsanUbsan.M.loaded_segments (0x60564 : word) = Some W_6051c.
Proof. vm_refl. Qed.
Lemma D_6051c : decode_any W_6051c = Some (ShiftImm ALU_SRL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60520 : bv 32 := 0xfff54793.
Lemma F_60520 : fetch_word AsanUbsan.M.loaded_segments (0x60568 : word) = Some W_60520.
Proof. vm_refl. Qed.
Lemma D_60520 : decode_any W_60520 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60524 : bv 32 := 0x00150513.
Lemma F_60524 : fetch_word AsanUbsan.M.loaded_segments (0x6056c : word) = Some W_60524.
Proof. vm_refl. Qed.
Lemma D_60524 : decode_any W_60524 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60528 : bv 32 := 0x00279793.
Lemma F_60528 : fetch_word AsanUbsan.M.loaded_segments (0x60570 : word) = Some W_60528.
Proof. vm_refl. Qed.
Lemma D_60528 : decode_any W_60528 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6052c : bv 32 := 0x00f587b3.
Lemma F_6052c : fetch_word AsanUbsan.M.loaded_segments (0x60574 : word) = Some W_6052c.
Proof. vm_refl. Qed.
Lemma D_6052c : decode_any W_6052c = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60530 : bv 32 := 0x00e7a023.
Lemma F_60530 : fetch_word AsanUbsan.M.loaded_segments (0x60578 : word) = Some W_60530.
Proof. vm_refl. Qed.
Lemma D_60530 : decode_any W_60530 = Some (Store SZ4 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60534 : bv 32 := 0x01560633.
Lemma F_60534 : fetch_word AsanUbsan.M.loaded_segments (0x6057c : word) = Some W_60534.
Proof. vm_refl. Qed.
Lemma D_60534 : decode_any W_60534 = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60538 : bv 32 := 0xff3562e3.
Lemma F_60538 : fetch_word AsanUbsan.M.loaded_segments (0x60580 : word) = Some W_60538.
Proof. vm_refl. Qed.
Lemma D_60538 : decode_any W_60538 = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6053c : bv 32 := 0x01043503.
Lemma F_6053c : fetch_word AsanUbsan.M.loaded_segments (0x60584 : word) = Some W_6053c.
Proof. vm_refl. Qed.
Lemma D_6053c : decode_any W_6053c = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60540 : bv 32 := 0x035985b3.
Lemma F_60540 : fetch_word AsanUbsan.M.loaded_segments (0x60588 : word) = Some W_60540.
Proof. vm_refl. Qed.
Lemma D_60540 : decode_any W_60540 = Some (Mul M_MUL 11 19 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60544 : bv 32 := 0x03043703.
Lemma F_60544 : fetch_word AsanUbsan.M.loaded_segments (0x6058c : word) = Some W_60544.
Proof. vm_refl. Qed.
Lemma D_60544 : decode_any W_60544 = Some (Load SZ8 true 14 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60548 : bv 32 := 0x00b686b3.
Lemma F_60548 : fetch_word AsanUbsan.M.loaded_segments (0x60590 : word) = Some W_60548.
Proof. vm_refl. Qed.
Lemma D_60548 : decode_any W_60548 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6054c : bv 32 := 0x01350533.
Lemma F_6054c : fetch_word AsanUbsan.M.loaded_segments (0x60594 : word) = Some W_6054c.
Proof. vm_refl. Qed.
Lemma D_6054c : decode_any W_6054c = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60550 : bv 32 := 0x00a43823.
Lemma F_60550 : fetch_word AsanUbsan.M.loaded_segments (0x60598 : word) = Some W_60550.
Proof. vm_refl. Qed.
Lemma D_60550 : decode_any W_60550 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60554 : bv 32 := 0x02d43023.
Lemma F_60554 : fetch_word AsanUbsan.M.loaded_segments (0x6059c : word) = Some W_60554.
Proof. vm_refl. Qed.
Lemma D_60554 : decode_any W_60554 = Some (Store SZ8 8 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60558 : bv 32 := 0x0ad76063.
Lemma F_60558 : fetch_word AsanUbsan.M.loaded_segments (0x605a0 : word) = Some W_60558.
Proof. vm_refl. Qed.
Lemma D_60558 : decode_any W_60558 = Some (Branch BC_LTU 14 13 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6055c : bv 32 := 0x02843683.
Lemma F_6055c : fetch_word AsanUbsan.M.loaded_segments (0x605a4 : word) = Some W_6055c.
Proof. vm_refl. Qed.
Lemma D_6055c : decode_any W_6055c = Some (Load SZ8 true 13 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60560 : bv 32 := 0x03843703.
Lemma F_60560 : fetch_word AsanUbsan.M.loaded_segments (0x605a8 : word) = Some W_60560.
Proof. vm_refl. Qed.
Lemma D_60560 : decode_any W_60560 = Some (Load SZ8 true 14 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60564 : bv 32 := 0x0ad76663.
Lemma F_60564 : fetch_word AsanUbsan.M.loaded_segments (0x605ac : word) = Some W_60564.
Proof. vm_refl. Qed.
Lemma D_60564 : decode_any W_60564 = Some (Branch BC_LTU 14 13 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60568 : bv 32 := 0x04040223.
Lemma F_60568 : fetch_word AsanUbsan.M.loaded_segments (0x605b0 : word) = Some W_60568.
Proof. vm_refl. Qed.
Lemma D_60568 : decode_any W_60568 = Some (Store SZ1 8 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6056c : bv 32 := 0x00100593.
Lemma F_6056c : fetch_word AsanUbsan.M.loaded_segments (0x605b4 : word) = Some W_6056c.
Proof. vm_refl. Qed.
Lemma D_6056c : decode_any W_6056c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60570 : bv 32 := 0x00058513.
Lemma F_60570 : fetch_word AsanUbsan.M.loaded_segments (0x605b8 : word) = Some W_60570.
Proof. vm_refl. Qed.
Lemma D_60570 : decode_any W_60570 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60574 : bv 32 := 0x03813083.
Lemma F_60574 : fetch_word AsanUbsan.M.loaded_segments (0x605bc : word) = Some W_60574.
Proof. vm_refl. Qed.
Lemma D_60574 : decode_any W_60574 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60578 : bv 32 := 0x03013403.
Lemma F_60578 : fetch_word AsanUbsan.M.loaded_segments (0x605c0 : word) = Some W_60578.
Proof. vm_refl. Qed.
Lemma D_60578 : decode_any W_60578 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6057c : bv 32 := 0x02813483.
Lemma F_6057c : fetch_word AsanUbsan.M.loaded_segments (0x605c4 : word) = Some W_6057c.
Proof. vm_refl. Qed.
Lemma D_6057c : decode_any W_6057c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60580 : bv 32 := 0x02013903.
Lemma F_60580 : fetch_word AsanUbsan.M.loaded_segments (0x605c8 : word) = Some W_60580.
Proof. vm_refl. Qed.
Lemma D_60580 : decode_any W_60580 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60584 : bv 32 := 0x01813983.
Lemma F_60584 : fetch_word AsanUbsan.M.loaded_segments (0x605cc : word) = Some W_60584.
Proof. vm_refl. Qed.
Lemma D_60584 : decode_any W_60584 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60588 : bv 32 := 0x01013a03.
Lemma F_60588 : fetch_word AsanUbsan.M.loaded_segments (0x605d0 : word) = Some W_60588.
Proof. vm_refl. Qed.
Lemma D_60588 : decode_any W_60588 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6058c : bv 32 := 0x00813a83.
Lemma F_6058c : fetch_word AsanUbsan.M.loaded_segments (0x605d4 : word) = Some W_6058c.
Proof. vm_refl. Qed.
Lemma D_6058c : decode_any W_6058c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60590 : bv 32 := 0x00013b03.
Lemma F_60590 : fetch_word AsanUbsan.M.loaded_segments (0x605d8 : word) = Some W_60590.
Proof. vm_refl. Qed.
Lemma D_60590 : decode_any W_60590 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60594 : bv 32 := 0x04010113.
Lemma F_60594 : fetch_word AsanUbsan.M.loaded_segments (0x605dc : word) = Some W_60594.
Proof. vm_refl. Qed.
Lemma D_60594 : decode_any W_60594 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60598 : bv 32 := 0x00008067.
Lemma F_60598 : fetch_word AsanUbsan.M.loaded_segments (0x605e0 : word) = Some W_60598.
Proof. vm_refl. Qed.
Lemma D_60598 : decode_any W_60598 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_605bc : bv 32 := 0x02852583.
Lemma F_605bc : fetch_word AsanUbsan.M.loaded_segments (0x60604 : word) = Some W_605bc.
Proof. vm_refl. Qed.
Lemma D_605bc : decode_any W_605bc = Some (Load SZ4 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_605c0 : bv 32 := 0x0c05c263.
Lemma F_605c0 : fetch_word AsanUbsan.M.loaded_segments (0x60608 : word) = Some W_605c0.
Proof. vm_refl. Qed.
Lemma D_605c0 : decode_any W_605c0 = Some (Branch BC_LT 11 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60684 : bv 32 := 0x00000a13.
Lemma F_60684 : fetch_word AsanUbsan.M.loaded_segments (0x606cc : word) = Some W_60684.
Proof. vm_refl. Qed.
Lemma D_60684 : decode_any W_60684 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60688 : bv 32 := 0xd7dff06f.
Lemma F_60688 : fetch_word AsanUbsan.M.loaded_segments (0x606d0 : word) = Some W_60688.
Proof. vm_refl. Qed.
Lemma D_60688 : decode_any W_60688 = Some (Jal 0 2096508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d0 : bv 32 := 0xff010113.
Lemma F_606d0 : fetch_word AsanUbsan.M.loaded_segments (0x60718 : word) = Some W_606d0.
Proof. vm_refl. Qed.
Lemma D_606d0 : decode_any W_606d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d4 : bv 32 := 0x00113423.
Lemma F_606d4 : fetch_word AsanUbsan.M.loaded_segments (0x6071c : word) = Some W_606d4.
Proof. vm_refl. Qed.
Lemma D_606d4 : decode_any W_606d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d8 : bv 32 := 0x02051693.
Lemma F_606d8 : fetch_word AsanUbsan.M.loaded_segments (0x60720 : word) = Some W_606d8.
Proof. vm_refl. Qed.
Lemma D_606d8 : decode_any W_606d8 = Some (ShiftImm ALU_SLL 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606dc : bv 32 := 0x00f00593.
Lemma F_606dc : fetch_word AsanUbsan.M.loaded_segments (0x60724 : word) = Some W_606dc.
Proof. vm_refl. Qed.
Lemma D_606dc : decode_any W_606dc = Some (OpImm ALU_ADD 11 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e0 : bv 32 := 0x0206d693.
Lemma F_606e0 : fetch_word AsanUbsan.M.loaded_segments (0x60728 : word) = Some W_606e0.
Proof. vm_refl. Qed.
Lemma D_606e0 : decode_any W_606e0 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e4 : bv 32 := 0x06a5f663.
Lemma F_606e4 : fetch_word AsanUbsan.M.loaded_segments (0x6072c : word) = Some W_606e4.
Proof. vm_refl. Qed.
Lemma D_606e4 : decode_any W_606e4 = Some (Branch BC_GEU 11 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e8 : bv 32 := 0x000015b7.
Lemma F_606e8 : fetch_word AsanUbsan.M.loaded_segments (0x60730 : word) = Some W_606e8.
Proof. vm_refl. Qed.
Lemma D_606e8 : decode_any W_606e8 = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606ec : bv 32 := 0x8015859b.
Lemma F_606ec : fetch_word AsanUbsan.M.loaded_segments (0x60734 : word) = Some W_606ec.
Proof. vm_refl. Qed.
Lemma D_606ec : decode_any W_606ec = Some (OpImm32 11 11 2049, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f0 : bv 32 := 0x06b57e63.
Lemma F_606f0 : fetch_word AsanUbsan.M.loaded_segments (0x60738 : word) = Some W_606f0.
Proof. vm_refl. Qed.
Lemma D_606f0 : decode_any W_606f0 = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f4 : bv 32 := 0xfff68593.
Lemma F_606f4 : fetch_word AsanUbsan.M.loaded_segments (0x6073c : word) = Some W_606f4.
Proof. vm_refl. Qed.
Lemma D_606f4 : decode_any W_606f4 = Some (OpImm ALU_ADD 11 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f8 : bv 32 := 0x00b6f5b3.
Lemma F_606f8 : fetch_word AsanUbsan.M.loaded_segments (0x60740 : word) = Some W_606f8.
Proof. vm_refl. Qed.
Lemma D_606f8 : decode_any W_606f8 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606fc : bv 32 := 0x08059863.
Lemma F_606fc : fetch_word AsanUbsan.M.loaded_segments (0x60744 : word) = Some W_606fc.
Proof. vm_refl. Qed.
Lemma D_606fc : decode_any W_606fc = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60700 : bv 32 := 0x40d005b3.
Lemma F_60700 : fetch_word AsanUbsan.M.loaded_segments (0x60748 : word) = Some W_60700.
Proof. vm_refl. Qed.
Lemma D_60700 : decode_any W_60700 = Some (Op ALU_SUB 11 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60704 : bv 32 := 0xfffb0617.
Lemma F_60704 : fetch_word AsanUbsan.M.loaded_segments (0x6074c : word) = Some W_60704.
Proof. vm_refl. Qed.
Lemma D_60704 : decode_any W_60704 = Some (Auipc 12 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60708 : bv 32 := 0xd2c63603.
Lemma F_60708 : fetch_word AsanUbsan.M.loaded_segments (0x60750 : word) = Some W_60708.
Proof. vm_refl. Qed.
Lemma D_60708 : decode_any W_60708 = Some (Load SZ8 true 12 12 3372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6070c : bv 32 := 0xfffb0717.
Lemma F_6070c : fetch_word AsanUbsan.M.loaded_segments (0x60754 : word) = Some W_6070c.
Proof. vm_refl. Qed.
Lemma D_6070c : decode_any W_6070c = Some (Auipc 14 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60710 : bv 32 := 0x00b6f5b3.
Lemma F_60710 : fetch_word AsanUbsan.M.loaded_segments (0x60758 : word) = Some W_60710.
Proof. vm_refl. Qed.
Lemma D_60710 : decode_any W_60710 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60714 : bv 32 := 0xe9c70713.
Lemma F_60714 : fetch_word AsanUbsan.M.loaded_segments (0x6075c : word) = Some W_60714.
Proof. vm_refl. Qed.
Lemma D_60714 : decode_any W_60714 = Some (OpImm ALU_ADD 14 14 3740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60718 : bv 32 := 0x02c585b3.
Lemma F_60718 : fetch_word AsanUbsan.M.loaded_segments (0x60760 : word) = Some W_60718.
Proof. vm_refl. Qed.
Lemma D_60718 : decode_any W_60718 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6071c : bv 32 := 0x03a5d593.
Lemma F_6071c : fetch_word AsanUbsan.M.loaded_segments (0x60764 : word) = Some W_6071c.
Proof. vm_refl. Qed.
Lemma D_6071c : decode_any W_6071c = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60720 : bv 32 := 0x00b705b3.
Lemma F_60720 : fetch_word AsanUbsan.M.loaded_segments (0x60768 : word) = Some W_60720.
Proof. vm_refl. Qed.
Lemma D_60720 : decode_any W_60720 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60724 : bv 32 := 0x0005c603.
Lemma F_60724 : fetch_word AsanUbsan.M.loaded_segments (0x6076c : word) = Some W_60724.
Proof. vm_refl. Qed.
Lemma D_60724 : decode_any W_60724 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60728 : bv 32 := 0xffc60593.
Lemma F_60728 : fetch_word AsanUbsan.M.loaded_segments (0x60770 : word) = Some W_60728.
Proof. vm_refl. Qed.
Lemma D_60728 : decode_any W_60728 = Some (OpImm ALU_ADD 11 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6072c : bv 32 := 0x00800713.
Lemma F_6072c : fetch_word AsanUbsan.M.loaded_segments (0x60774 : word) = Some W_6072c.
Proof. vm_refl. Qed.
Lemma D_6072c : decode_any W_6072c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60730 : bv 32 := 0x06e5fe63.
Lemma F_60730 : fetch_word AsanUbsan.M.loaded_segments (0x60778 : word) = Some W_60730.
Proof. vm_refl. Qed.
Lemma D_60730 : decode_any W_60730 = Some (Branch BC_GEU 11 14 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60734 : bv 32 := 0x00100713.
Lemma F_60734 : fetch_word AsanUbsan.M.loaded_segments (0x6077c : word) = Some W_60734.
Proof. vm_refl. Qed.
Lemma D_60734 : decode_any W_60734 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60738 : bv 32 := 0x00c7173b.
Lemma F_60738 : fetch_word AsanUbsan.M.loaded_segments (0x60780 : word) = Some W_60738.
Proof. vm_refl. Qed.
Lemma D_60738 : decode_any W_60738 = Some (Op32 ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6073c : bv 32 := 0x08e51a63.
Lemma F_6073c : fetch_word AsanUbsan.M.loaded_segments (0x60784 : word) = Some W_6073c.
Proof. vm_refl. Qed.
Lemma D_6073c : decode_any W_6073c = Some (Branch BC_NE 10 14 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60740 : bv 32 := 0x00058513.
Lemma F_60740 : fetch_word AsanUbsan.M.loaded_segments (0x60788 : word) = Some W_60740.
Proof. vm_refl. Qed.
Lemma D_60740 : decode_any W_60740 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60744 : bv 32 := 0x00813083.
Lemma F_60744 : fetch_word AsanUbsan.M.loaded_segments (0x6078c : word) = Some W_60744.
Proof. vm_refl. Qed.
Lemma D_60744 : decode_any W_60744 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60748 : bv 32 := 0x01010113.
Lemma F_60748 : fetch_word AsanUbsan.M.loaded_segments (0x60790 : word) = Some W_60748.
Proof. vm_refl. Qed.
Lemma D_60748 : decode_any W_60748 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6074c : bv 32 := 0x00008067.
Lemma F_6074c : fetch_word AsanUbsan.M.loaded_segments (0x60794 : word) = Some W_6074c.
Proof. vm_refl. Qed.
Lemma D_6074c : decode_any W_6074c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

