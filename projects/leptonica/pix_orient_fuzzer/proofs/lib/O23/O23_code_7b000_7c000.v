(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_7bc6c : bv 32 := 0x0e0a0e63.
Lemma F_7bc6c : fetch_word Plain.M.loaded_segments (0x7bcc4 : word) = Some W_7bc6c.
Proof. vm_refl. Qed.
Lemma D_7bc6c : decode_any W_7bc6c = Some (Branch BC_EQ 20 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc70 : bv 32 := 0xfff94513.
Lemma F_7bc70 : fetch_word Plain.M.loaded_segments (0x7bcc8 : word) = Some W_7bc70.
Proof. vm_refl. Qed.
Lemma D_7bc70 : decode_any W_7bc70 = Some (OpImm ALU_XOR 10 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc74 : bv 32 := 0xfff8c593.
Lemma F_7bc74 : fetch_word Plain.M.loaded_segments (0x7bccc : word) = Some W_7bc74.
Proof. vm_refl. Qed.
Lemma D_7bc74 : decode_any W_7bc74 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc78 : bv 32 := 0x00408093.
Lemma F_7bc78 : fetch_word Plain.M.loaded_segments (0x7bcd0 : word) = Some W_7bc78.
Proof. vm_refl. Qed.
Lemma D_7bc78 : decode_any W_7bc78 = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc7c : bv 32 := 0x00269a13.
Lemma F_7bc7c : fetch_word Plain.M.loaded_segments (0x7bcd4 : word) = Some W_7bc7c.
Proof. vm_refl. Qed.
Lemma D_7bc7c : decode_any W_7bc7c = Some (ShiftImm ALU_SLL 20 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc80 : bv 32 := 0x00271a93.
Lemma F_7bc80 : fetch_word Plain.M.loaded_segments (0x7bcd8 : word) = Some W_7bc80.
Proof. vm_refl. Qed.
Lemma D_7bc80 : decode_any W_7bc80 = Some (ShiftImm ALU_SLL 21 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc84 : bv 32 := 0x001cfb13.
Lemma F_7bc84 : fetch_word Plain.M.loaded_segments (0x7bcdc : word) = Some W_7bc84.
Proof. vm_refl. Qed.
Lemma D_7bc84 : decode_any W_7bc84 = Some (OpImm ALU_AND 22 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc88 : bv 32 := 0x001c7b93.
Lemma F_7bc88 : fetch_word Plain.M.loaded_segments (0x7bce0 : word) = Some W_7bc88.
Proof. vm_refl. Qed.
Lemma D_7bc88 : decode_any W_7bc88 = Some (OpImm ALU_AND 23 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc8c : bv 32 := 0x00060c13.
Lemma F_7bc8c : fetch_word Plain.M.loaded_segments (0x7bce4 : word) = Some W_7bc8c.
Proof. vm_refl. Qed.
Lemma D_7bc8c : decode_any W_7bc8c = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc90 : bv 32 := 0x02c0006f.
Lemma F_7bc90 : fetch_word Plain.M.loaded_segments (0x7bce8 : word) = Some W_7bc90.
Proof. vm_refl. Qed.
Lemma D_7bc90 : decode_any W_7bc90 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc94 : bv 32 := 0x0103d3bb.
Lemma F_7bc94 : fetch_word Plain.M.loaded_segments (0x7bcec : word) = Some W_7bc94.
Proof. vm_refl. Qed.
Lemma D_7bc94 : decode_any W_7bc94 = Some (Op32 ALU_SRL 7 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc98 : bv 32 := 0x00042f83.
Lemma F_7bc98 : fetch_word Plain.M.loaded_segments (0x7bcf0 : word) = Some W_7bc98.
Proof. vm_refl. Qed.
Lemma D_7bc98 : decode_any W_7bc98 = Some (Load SZ4 true 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bc9c : bv 32 := 0x0123f3b3.
Lemma F_7bc9c : fetch_word Plain.M.loaded_segments (0x7bcf4 : word) = Some W_7bc9c.
Proof. vm_refl. Qed.
Lemma D_7bc9c : decode_any W_7bc9c = Some (Op ALU_AND 7 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bca0 : bv 32 := 0xfffc0c1b.
Lemma F_7bca0 : fetch_word Plain.M.loaded_segments (0x7bcf8 : word) = Some W_7bca0.
Proof. vm_refl. Qed.
Lemma D_7bca0 : decode_any W_7bca0 = Some (OpImm32 24 24 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bca4 : bv 32 := 0x014080b3.
Lemma F_7bca4 : fetch_word Plain.M.loaded_segments (0x7bcfc : word) = Some W_7bca4.
Proof. vm_refl. Qed.
Lemma D_7bca4 : decode_any W_7bca4 = Some (Op ALU_ADD 1 1 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bca8 : bv 32 := 0x00afffb3.
Lemma F_7bca8 : fetch_word Plain.M.loaded_segments (0x7bd00 : word) = Some W_7bca8.
Proof. vm_refl. Qed.
Lemma D_7bca8 : decode_any W_7bca8 = Some (Op ALU_AND 31 31 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcac : bv 32 := 0x007fe3b3.
Lemma F_7bcac : fetch_word Plain.M.loaded_segments (0x7bd04 : word) = Some W_7bcac.
Proof. vm_refl. Qed.
Lemma D_7bcac : decode_any W_7bcac = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcb0 : bv 32 := 0x00742023.
Lemma F_7bcb0 : fetch_word Plain.M.loaded_segments (0x7bd08 : word) = Some W_7bcb0.
Proof. vm_refl. Qed.
Lemma D_7bcb0 : decode_any W_7bcb0 = Some (Store SZ4 8 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcb4 : bv 32 := 0x01540433.
Lemma F_7bcb4 : fetch_word Plain.M.loaded_segments (0x7bd0c : word) = Some W_7bcb4.
Proof. vm_refl. Qed.
Lemma D_7bcb4 : decode_any W_7bcb4 = Some (Op ALU_ADD 8 8 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcb8 : bv 32 := 0x0a0c0863.
Lemma F_7bcb8 : fetch_word Plain.M.loaded_segments (0x7bd10 : word) = Some W_7bcb8.
Proof. vm_refl. Qed.
Lemma D_7bcb8 : decode_any W_7bcb8 = Some (Branch BC_EQ 24 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcbc : bv 32 := 0xffc0a383.
Lemma F_7bcbc : fetch_word Plain.M.loaded_segments (0x7bd14 : word) = Some W_7bcbc.
Proof. vm_refl. Qed.
Lemma D_7bcbc : decode_any W_7bcbc = Some (Load SZ4 true 7 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcc0 : bv 32 := 0xfc0b0ae3.
Lemma F_7bcc0 : fetch_word Plain.M.loaded_segments (0x7bd18 : word) = Some W_7bcc0.
Proof. vm_refl. Qed.
Lemma D_7bcc0 : decode_any W_7bcc0 = Some (Branch BC_EQ 22 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcc4 : bv 32 := 0x00f393bb.
Lemma F_7bcc4 : fetch_word Plain.M.loaded_segments (0x7bd1c : word) = Some W_7bcc4.
Proof. vm_refl. Qed.
Lemma D_7bcc4 : decode_any W_7bcc4 = Some (Op32 ALU_SLL 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcc8 : bv 32 := 0xfc0b98e3.
Lemma F_7bcc8 : fetch_word Plain.M.loaded_segments (0x7bd20 : word) = Some W_7bcc8.
Proof. vm_refl. Qed.
Lemma D_7bcc8 : decode_any W_7bcc8 = Some (Branch BC_NE 23 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bccc : bv 32 := 0x0000af83.
Lemma F_7bccc : fetch_word Plain.M.loaded_segments (0x7bd24 : word) = Some W_7bccc.
Proof. vm_refl. Qed.
Lemma D_7bccc : decode_any W_7bccc = Some (Load SZ4 true 31 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcd0 : bv 32 := 0x00b3f3b3.
Lemma F_7bcd0 : fetch_word Plain.M.loaded_segments (0x7bd28 : word) = Some W_7bcd0.
Proof. vm_refl. Qed.
Lemma D_7bcd0 : decode_any W_7bcd0 = Some (Op ALU_AND 7 7 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcd4 : bv 32 := 0x010fdfbb.
Lemma F_7bcd4 : fetch_word Plain.M.loaded_segments (0x7bd2c : word) = Some W_7bcd4.
Proof. vm_refl. Qed.
Lemma D_7bcd4 : decode_any W_7bcd4 = Some (Op32 ALU_SRL 31 31 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcd8 : bv 32 := 0x011fffb3.
Lemma F_7bcd8 : fetch_word Plain.M.loaded_segments (0x7bd30 : word) = Some W_7bcd8.
Proof. vm_refl. Qed.
Lemma D_7bcd8 : decode_any W_7bcd8 = Some (Op ALU_AND 31 31 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcdc : bv 32 := 0x007fe3b3.
Lemma F_7bcdc : fetch_word Plain.M.loaded_segments (0x7bd34 : word) = Some W_7bcdc.
Proof. vm_refl. Qed.
Lemma D_7bcdc : decode_any W_7bcdc = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bce0 : bv 32 := 0xfb9ff06f.
Lemma F_7bce0 : fetch_word Plain.M.loaded_segments (0x7bd38 : word) = Some W_7bce0.
Proof. vm_refl. Qed.
Lemma D_7bce0 : decode_any W_7bce0 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd68 : bv 32 := 0x3a0982e3.
Lemma F_7bd68 : fetch_word Plain.M.loaded_segments (0x7bdc0 : word) = Some W_7bd68.
Proof. vm_refl. Qed.
Lemma D_7bd68 : decode_any W_7bd68 = Some (Branch BC_EQ 19 0 2980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd6c : bv 32 := 0x00013503.
Lemma F_7bd6c : fetch_word Plain.M.loaded_segments (0x7bdc4 : word) = Some W_7bd6c.
Proof. vm_refl. Qed.
Lemma D_7bd6c : decode_any W_7bd6c = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd70 : bv 32 := 0x18051063.
Lemma F_7bd70 : fetch_word Plain.M.loaded_segments (0x7bdc8 : word) = Some W_7bd70.
Proof. vm_refl. Qed.
Lemma D_7bd70 : decode_any W_7bd70 = Some (Branch BC_NE 10 0 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd74 : bv 32 := 0xfff34513.
Lemma F_7bd74 : fetch_word Plain.M.loaded_segments (0x7bdcc : word) = Some W_7bd74.
Proof. vm_refl. Qed.
Lemma D_7bd74 : decode_any W_7bd74 = Some (OpImm ALU_XOR 10 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd78 : bv 32 := 0xfff8c593.
Lemma F_7bd78 : fetch_word Plain.M.loaded_segments (0x7bdd0 : word) = Some W_7bd78.
Proof. vm_refl. Qed.
Lemma D_7bd78 : decode_any W_7bd78 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd7c : bv 32 := 0x004d0393.
Lemma F_7bd7c : fetch_word Plain.M.loaded_segments (0x7bdd4 : word) = Some W_7bd7c.
Proof. vm_refl. Qed.
Lemma D_7bd7c : decode_any W_7bd7c = Some (OpImm ALU_ADD 7 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd80 : bv 32 := 0x00269693.
Lemma F_7bd80 : fetch_word Plain.M.loaded_segments (0x7bdd8 : word) = Some W_7bd80.
Proof. vm_refl. Qed.
Lemma D_7bd80 : decode_any W_7bd80 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd84 : bv 32 := 0x00271713.
Lemma F_7bd84 : fetch_word Plain.M.loaded_segments (0x7bddc : word) = Some W_7bd84.
Proof. vm_refl. Qed.
Lemma D_7bd84 : decode_any W_7bd84 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd88 : bv 32 := 0x001f7e13.
Lemma F_7bd88 : fetch_word Plain.M.loaded_segments (0x7bde0 : word) = Some W_7bd88.
Proof. vm_refl. Qed.
Lemma D_7bd88 : decode_any W_7bd88 = Some (OpImm ALU_AND 28 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd8c : bv 32 := 0x0280006f.
Lemma F_7bd8c : fetch_word Plain.M.loaded_segments (0x7bde4 : word) = Some W_7bd8c.
Proof. vm_refl. Qed.
Lemma D_7bd8c : decode_any W_7bd8c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd90 : bv 32 := 0x0002af03.
Lemma F_7bd90 : fetch_word Plain.M.loaded_segments (0x7bde8 : word) = Some W_7bd90.
Proof. vm_refl. Qed.
Lemma D_7bd90 : decode_any W_7bd90 = Some (Load SZ4 true 30 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd94 : bv 32 := 0x006efeb3.
Lemma F_7bd94 : fetch_word Plain.M.loaded_segments (0x7bdec : word) = Some W_7bd94.
Proof. vm_refl. Qed.
Lemma D_7bd94 : decode_any W_7bd94 = Some (Op ALU_AND 29 29 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd98 : bv 32 := 0xfff6061b.
Lemma F_7bd98 : fetch_word Plain.M.loaded_segments (0x7bdf0 : word) = Some W_7bd98.
Proof. vm_refl. Qed.
Lemma D_7bd98 : decode_any W_7bd98 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd9c : bv 32 := 0x00d383b3.
Lemma F_7bd9c : fetch_word Plain.M.loaded_segments (0x7bdf4 : word) = Some W_7bd9c.
Proof. vm_refl. Qed.
Lemma D_7bd9c : decode_any W_7bd9c = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bda0 : bv 32 := 0x00af7f33.
Lemma F_7bda0 : fetch_word Plain.M.loaded_segments (0x7bdf8 : word) = Some W_7bda0.
Proof. vm_refl. Qed.
Lemma D_7bda0 : decode_any W_7bda0 = Some (Op ALU_AND 30 30 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bda4 : bv 32 := 0x01df6eb3.
Lemma F_7bda4 : fetch_word Plain.M.loaded_segments (0x7bdfc : word) = Some W_7bda4.
Proof. vm_refl. Qed.
Lemma D_7bda4 : decode_any W_7bda4 = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bda8 : bv 32 := 0x01d2a023.
Lemma F_7bda8 : fetch_word Plain.M.loaded_segments (0x7be00 : word) = Some W_7bda8.
Proof. vm_refl. Qed.
Lemma D_7bda8 : decode_any W_7bda8 = Some (Store SZ4 5 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdac : bv 32 := 0x00e282b3.
Lemma F_7bdac : fetch_word Plain.M.loaded_segments (0x7be04 : word) = Some W_7bdac.
Proof. vm_refl. Qed.
Lemma D_7bdac : decode_any W_7bdac = Some (Op ALU_ADD 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdb0 : bv 32 := 0x14060063.
Lemma F_7bdb0 : fetch_word Plain.M.loaded_segments (0x7be08 : word) = Some W_7bdb0.
Proof. vm_refl. Qed.
Lemma D_7bdb0 : decode_any W_7bdb0 = Some (Branch BC_EQ 12 0 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdb4 : bv 32 := 0xffc3ae83.
Lemma F_7bdb4 : fetch_word Plain.M.loaded_segments (0x7be0c : word) = Some W_7bdb4.
Proof. vm_refl. Qed.
Lemma D_7bdb4 : decode_any W_7bdb4 = Some (Load SZ4 true 29 7 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdb8 : bv 32 := 0x00fe9ebb.
Lemma F_7bdb8 : fetch_word Plain.M.loaded_segments (0x7be10 : word) = Some W_7bdb8.
Proof. vm_refl. Qed.
Lemma D_7bdb8 : decode_any W_7bdb8 = Some (Op32 ALU_SLL 29 29 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdbc : bv 32 := 0xfc0e1ae3.
Lemma F_7bdbc : fetch_word Plain.M.loaded_segments (0x7be14 : word) = Some W_7bdbc.
Proof. vm_refl. Qed.
Lemma D_7bdbc : decode_any W_7bdbc = Some (Branch BC_NE 28 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdc0 : bv 32 := 0x0003af03.
Lemma F_7bdc0 : fetch_word Plain.M.loaded_segments (0x7be18 : word) = Some W_7bdc0.
Proof. vm_refl. Qed.
Lemma D_7bdc0 : decode_any W_7bdc0 = Some (Load SZ4 true 30 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdc4 : bv 32 := 0x00befeb3.
Lemma F_7bdc4 : fetch_word Plain.M.loaded_segments (0x7be1c : word) = Some W_7bdc4.
Proof. vm_refl. Qed.
Lemma D_7bdc4 : decode_any W_7bdc4 = Some (Op ALU_AND 29 29 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdc8 : bv 32 := 0x010f5f3b.
Lemma F_7bdc8 : fetch_word Plain.M.loaded_segments (0x7be20 : word) = Some W_7bdc8.
Proof. vm_refl. Qed.
Lemma D_7bdc8 : decode_any W_7bdc8 = Some (Op32 ALU_SRL 30 30 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdcc : bv 32 := 0x011f7f33.
Lemma F_7bdcc : fetch_word Plain.M.loaded_segments (0x7be24 : word) = Some W_7bdcc.
Proof. vm_refl. Qed.
Lemma D_7bdcc : decode_any W_7bdcc = Some (Op ALU_AND 30 30 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdd0 : bv 32 := 0x01df6eb3.
Lemma F_7bdd0 : fetch_word Plain.M.loaded_segments (0x7be28 : word) = Some W_7bdd0.
Proof. vm_refl. Qed.
Lemma D_7bdd0 : decode_any W_7bdd0 = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdd4 : bv 32 := 0xfbdff06f.
Lemma F_7bdd4 : fetch_word Plain.M.loaded_segments (0x7be2c : word) = Some W_7bdd4.
Proof. vm_refl. Qed.
Lemma D_7bdd4 : decode_any W_7bdd4 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef0 : bv 32 := 0x06813083.
Lemma F_7bef0 : fetch_word Plain.M.loaded_segments (0x7bf48 : word) = Some W_7bef0.
Proof. vm_refl. Qed.
Lemma D_7bef0 : decode_any W_7bef0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef4 : bv 32 := 0x06013403.
Lemma F_7bef4 : fetch_word Plain.M.loaded_segments (0x7bf4c : word) = Some W_7bef4.
Proof. vm_refl. Qed.
Lemma D_7bef4 : decode_any W_7bef4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef8 : bv 32 := 0x05813483.
Lemma F_7bef8 : fetch_word Plain.M.loaded_segments (0x7bf50 : word) = Some W_7bef8.
Proof. vm_refl. Qed.
Lemma D_7bef8 : decode_any W_7bef8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7befc : bv 32 := 0x05013903.
Lemma F_7befc : fetch_word Plain.M.loaded_segments (0x7bf54 : word) = Some W_7befc.
Proof. vm_refl. Qed.
Lemma D_7befc : decode_any W_7befc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf00 : bv 32 := 0x04813983.
Lemma F_7bf00 : fetch_word Plain.M.loaded_segments (0x7bf58 : word) = Some W_7bf00.
Proof. vm_refl. Qed.
Lemma D_7bf00 : decode_any W_7bf00 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf04 : bv 32 := 0x04013a03.
Lemma F_7bf04 : fetch_word Plain.M.loaded_segments (0x7bf5c : word) = Some W_7bf04.
Proof. vm_refl. Qed.
Lemma D_7bf04 : decode_any W_7bf04 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf08 : bv 32 := 0x03813a83.
Lemma F_7bf08 : fetch_word Plain.M.loaded_segments (0x7bf60 : word) = Some W_7bf08.
Proof. vm_refl. Qed.
Lemma D_7bf08 : decode_any W_7bf08 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf0c : bv 32 := 0x03013b03.
Lemma F_7bf0c : fetch_word Plain.M.loaded_segments (0x7bf64 : word) = Some W_7bf0c.
Proof. vm_refl. Qed.
Lemma D_7bf0c : decode_any W_7bf0c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf10 : bv 32 := 0x02813b83.
Lemma F_7bf10 : fetch_word Plain.M.loaded_segments (0x7bf68 : word) = Some W_7bf10.
Proof. vm_refl. Qed.
Lemma D_7bf10 : decode_any W_7bf10 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf14 : bv 32 := 0x02013c03.
Lemma F_7bf14 : fetch_word Plain.M.loaded_segments (0x7bf6c : word) = Some W_7bf14.
Proof. vm_refl. Qed.
Lemma D_7bf14 : decode_any W_7bf14 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf18 : bv 32 := 0x01813c83.
Lemma F_7bf18 : fetch_word Plain.M.loaded_segments (0x7bf70 : word) = Some W_7bf18.
Proof. vm_refl. Qed.
Lemma D_7bf18 : decode_any W_7bf18 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf1c : bv 32 := 0x01013d03.
Lemma F_7bf1c : fetch_word Plain.M.loaded_segments (0x7bf74 : word) = Some W_7bf1c.
Proof. vm_refl. Qed.
Lemma D_7bf1c : decode_any W_7bf1c = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf20 : bv 32 := 0x00813d83.
Lemma F_7bf20 : fetch_word Plain.M.loaded_segments (0x7bf78 : word) = Some W_7bf20.
Proof. vm_refl. Qed.
Lemma D_7bf20 : decode_any W_7bf20 = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf24 : bv 32 := 0x07010113.
Lemma F_7bf24 : fetch_word Plain.M.loaded_segments (0x7bf7c : word) = Some W_7bf24.
Proof. vm_refl. Qed.
Lemma D_7bf24 : decode_any W_7bf24 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf28 : bv 32 := 0x00008067.
Lemma F_7bf28 : fetch_word Plain.M.loaded_segments (0x7bf80 : word) = Some W_7bf28.
Proof. vm_refl. Qed.
Lemma D_7bf28 : decode_any W_7bf28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
