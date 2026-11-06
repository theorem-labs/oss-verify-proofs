(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_8c43c : bv 32 := 0x00155593.
Lemma F_8c43c : fetch_word AsanUbsan.M.loaded_segments (0x8c43c : word) = Some W_8c43c.
Proof. vm_refl. Qed.
Lemma D_8c43c : decode_any W_8c43c = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c440 : bv 32 := 0x55555637.
Lemma F_8c440 : fetch_word AsanUbsan.M.loaded_segments (0x8c440 : word) = Some W_8c440.
Proof. vm_refl. Qed.
Lemma D_8c440 : decode_any W_8c440 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c444 : bv 32 := 0x333336b7.
Lemma F_8c444 : fetch_word AsanUbsan.M.loaded_segments (0x8c444 : word) = Some W_8c444.
Proof. vm_refl. Qed.
Lemma D_8c444 : decode_any W_8c444 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c448 : bv 32 := 0x0f0f1737.
Lemma F_8c448 : fetch_word AsanUbsan.M.loaded_segments (0x8c448 : word) = Some W_8c448.
Proof. vm_refl. Qed.
Lemma D_8c448 : decode_any W_8c448 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c44c : bv 32 := 0x010107b7.
Lemma F_8c44c : fetch_word AsanUbsan.M.loaded_segments (0x8c44c : word) = Some W_8c44c.
Proof. vm_refl. Qed.
Lemma D_8c44c : decode_any W_8c44c = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c450 : bv 32 := 0x00b56533.
Lemma F_8c450 : fetch_word AsanUbsan.M.loaded_segments (0x8c450 : word) = Some W_8c450.
Proof. vm_refl. Qed.
Lemma D_8c450 : decode_any W_8c450 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c454 : bv 32 := 0x5556059b.
Lemma F_8c454 : fetch_word AsanUbsan.M.loaded_segments (0x8c454 : word) = Some W_8c454.
Proof. vm_refl. Qed.
Lemma D_8c454 : decode_any W_8c454 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c458 : bv 32 := 0x3336861b.
Lemma F_8c458 : fetch_word AsanUbsan.M.loaded_segments (0x8c458 : word) = Some W_8c458.
Proof. vm_refl. Qed.
Lemma D_8c458 : decode_any W_8c458 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c45c : bv 32 := 0xf0f7069b.
Lemma F_8c45c : fetch_word AsanUbsan.M.loaded_segments (0x8c45c : word) = Some W_8c45c.
Proof. vm_refl. Qed.
Lemma D_8c45c : decode_any W_8c45c = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c460 : bv 32 := 0x1017871b.
Lemma F_8c460 : fetch_word AsanUbsan.M.loaded_segments (0x8c460 : word) = Some W_8c460.
Proof. vm_refl. Qed.
Lemma D_8c460 : decode_any W_8c460 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c464 : bv 32 := 0x00255793.
Lemma F_8c464 : fetch_word AsanUbsan.M.loaded_segments (0x8c464 : word) = Some W_8c464.
Proof. vm_refl. Qed.
Lemma D_8c464 : decode_any W_8c464 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c468 : bv 32 := 0x00f56533.
Lemma F_8c468 : fetch_word AsanUbsan.M.loaded_segments (0x8c468 : word) = Some W_8c468.
Proof. vm_refl. Qed.
Lemma D_8c468 : decode_any W_8c468 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c46c : bv 32 := 0x02059793.
Lemma F_8c46c : fetch_word AsanUbsan.M.loaded_segments (0x8c46c : word) = Some W_8c46c.
Proof. vm_refl. Qed.
Lemma D_8c46c : decode_any W_8c46c = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c470 : bv 32 := 0x00f585b3.
Lemma F_8c470 : fetch_word AsanUbsan.M.loaded_segments (0x8c470 : word) = Some W_8c470.
Proof. vm_refl. Qed.
Lemma D_8c470 : decode_any W_8c470 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c474 : bv 32 := 0x02061793.
Lemma F_8c474 : fetch_word AsanUbsan.M.loaded_segments (0x8c474 : word) = Some W_8c474.
Proof. vm_refl. Qed.
Lemma D_8c474 : decode_any W_8c474 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c478 : bv 32 := 0x00f60633.
Lemma F_8c478 : fetch_word AsanUbsan.M.loaded_segments (0x8c478 : word) = Some W_8c478.
Proof. vm_refl. Qed.
Lemma D_8c478 : decode_any W_8c478 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c47c : bv 32 := 0x02069793.
Lemma F_8c47c : fetch_word AsanUbsan.M.loaded_segments (0x8c47c : word) = Some W_8c47c.
Proof. vm_refl. Qed.
Lemma D_8c47c : decode_any W_8c47c = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c480 : bv 32 := 0x00f686b3.
Lemma F_8c480 : fetch_word AsanUbsan.M.loaded_segments (0x8c480 : word) = Some W_8c480.
Proof. vm_refl. Qed.
Lemma D_8c480 : decode_any W_8c480 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c484 : bv 32 := 0x02071793.
Lemma F_8c484 : fetch_word AsanUbsan.M.loaded_segments (0x8c484 : word) = Some W_8c484.
Proof. vm_refl. Qed.
Lemma D_8c484 : decode_any W_8c484 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c488 : bv 32 := 0x00f70733.
Lemma F_8c488 : fetch_word AsanUbsan.M.loaded_segments (0x8c488 : word) = Some W_8c488.
Proof. vm_refl. Qed.
Lemma D_8c488 : decode_any W_8c488 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c48c : bv 32 := 0x00455793.
Lemma F_8c48c : fetch_word AsanUbsan.M.loaded_segments (0x8c48c : word) = Some W_8c48c.
Proof. vm_refl. Qed.
Lemma D_8c48c : decode_any W_8c48c = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c490 : bv 32 := 0x00f56533.
Lemma F_8c490 : fetch_word AsanUbsan.M.loaded_segments (0x8c490 : word) = Some W_8c490.
Proof. vm_refl. Qed.
Lemma D_8c490 : decode_any W_8c490 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c494 : bv 32 := 0x00855793.
Lemma F_8c494 : fetch_word AsanUbsan.M.loaded_segments (0x8c494 : word) = Some W_8c494.
Proof. vm_refl. Qed.
Lemma D_8c494 : decode_any W_8c494 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c498 : bv 32 := 0x00f56533.
Lemma F_8c498 : fetch_word AsanUbsan.M.loaded_segments (0x8c498 : word) = Some W_8c498.
Proof. vm_refl. Qed.
Lemma D_8c498 : decode_any W_8c498 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c49c : bv 32 := 0x01055793.
Lemma F_8c49c : fetch_word AsanUbsan.M.loaded_segments (0x8c49c : word) = Some W_8c49c.
Proof. vm_refl. Qed.
Lemma D_8c49c : decode_any W_8c49c = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4a0 : bv 32 := 0x00f56533.
Lemma F_8c4a0 : fetch_word AsanUbsan.M.loaded_segments (0x8c4a0 : word) = Some W_8c4a0.
Proof. vm_refl. Qed.
Lemma D_8c4a0 : decode_any W_8c4a0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4a4 : bv 32 := 0x02055793.
Lemma F_8c4a4 : fetch_word AsanUbsan.M.loaded_segments (0x8c4a4 : word) = Some W_8c4a4.
Proof. vm_refl. Qed.
Lemma D_8c4a4 : decode_any W_8c4a4 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4a8 : bv 32 := 0x00f56533.
Lemma F_8c4a8 : fetch_word AsanUbsan.M.loaded_segments (0x8c4a8 : word) = Some W_8c4a8.
Proof. vm_refl. Qed.
Lemma D_8c4a8 : decode_any W_8c4a8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4ac : bv 32 := 0xfff54513.
Lemma F_8c4ac : fetch_word AsanUbsan.M.loaded_segments (0x8c4ac : word) = Some W_8c4ac.
Proof. vm_refl. Qed.
Lemma D_8c4ac : decode_any W_8c4ac = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4b0 : bv 32 := 0x00155793.
Lemma F_8c4b0 : fetch_word AsanUbsan.M.loaded_segments (0x8c4b0 : word) = Some W_8c4b0.
Proof. vm_refl. Qed.
Lemma D_8c4b0 : decode_any W_8c4b0 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4b4 : bv 32 := 0x00b7f5b3.
Lemma F_8c4b4 : fetch_word AsanUbsan.M.loaded_segments (0x8c4b4 : word) = Some W_8c4b4.
Proof. vm_refl. Qed.
Lemma D_8c4b4 : decode_any W_8c4b4 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4b8 : bv 32 := 0x40b50533.
Lemma F_8c4b8 : fetch_word AsanUbsan.M.loaded_segments (0x8c4b8 : word) = Some W_8c4b8.
Proof. vm_refl. Qed.
Lemma D_8c4b8 : decode_any W_8c4b8 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4bc : bv 32 := 0x00c575b3.
Lemma F_8c4bc : fetch_word AsanUbsan.M.loaded_segments (0x8c4bc : word) = Some W_8c4bc.
Proof. vm_refl. Qed.
Lemma D_8c4bc : decode_any W_8c4bc = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4c0 : bv 32 := 0x00255513.
Lemma F_8c4c0 : fetch_word AsanUbsan.M.loaded_segments (0x8c4c0 : word) = Some W_8c4c0.
Proof. vm_refl. Qed.
Lemma D_8c4c0 : decode_any W_8c4c0 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4c4 : bv 32 := 0x00c57533.
Lemma F_8c4c4 : fetch_word AsanUbsan.M.loaded_segments (0x8c4c4 : word) = Some W_8c4c4.
Proof. vm_refl. Qed.
Lemma D_8c4c4 : decode_any W_8c4c4 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4c8 : bv 32 := 0x00a58533.
Lemma F_8c4c8 : fetch_word AsanUbsan.M.loaded_segments (0x8c4c8 : word) = Some W_8c4c8.
Proof. vm_refl. Qed.
Lemma D_8c4c8 : decode_any W_8c4c8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4cc : bv 32 := 0x00455593.
Lemma F_8c4cc : fetch_word AsanUbsan.M.loaded_segments (0x8c4cc : word) = Some W_8c4cc.
Proof. vm_refl. Qed.
Lemma D_8c4cc : decode_any W_8c4cc = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4d0 : bv 32 := 0x00b50533.
Lemma F_8c4d0 : fetch_word AsanUbsan.M.loaded_segments (0x8c4d0 : word) = Some W_8c4d0.
Proof. vm_refl. Qed.
Lemma D_8c4d0 : decode_any W_8c4d0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4d4 : bv 32 := 0x00d57533.
Lemma F_8c4d4 : fetch_word AsanUbsan.M.loaded_segments (0x8c4d4 : word) = Some W_8c4d4.
Proof. vm_refl. Qed.
Lemma D_8c4d4 : decode_any W_8c4d4 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4d8 : bv 32 := 0x02e50533.
Lemma F_8c4d8 : fetch_word AsanUbsan.M.loaded_segments (0x8c4d8 : word) = Some W_8c4d8.
Proof. vm_refl. Qed.
Lemma D_8c4d8 : decode_any W_8c4d8 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4dc : bv 32 := 0x03855513.
Lemma F_8c4dc : fetch_word AsanUbsan.M.loaded_segments (0x8c4dc : word) = Some W_8c4dc.
Proof. vm_refl. Qed.
Lemma D_8c4dc : decode_any W_8c4dc = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4e0 : bv 32 := 0x40a0053b.
Lemma F_8c4e0 : fetch_word AsanUbsan.M.loaded_segments (0x8c4e0 : word) = Some W_8c4e0.
Proof. vm_refl. Qed.
Lemma D_8c4e0 : decode_any W_8c4e0 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4e4 : bv 32 := 0xfff00593.
Lemma F_8c4e4 : fetch_word AsanUbsan.M.loaded_segments (0x8c4e4 : word) = Some W_8c4e4.
Proof. vm_refl. Qed.
Lemma D_8c4e4 : decode_any W_8c4e4 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4e8 : bv 32 := 0x00a59533.
Lemma F_8c4e8 : fetch_word AsanUbsan.M.loaded_segments (0x8c4e8 : word) = Some W_8c4e8.
Proof. vm_refl. Qed.
Lemma D_8c4e8 : decode_any W_8c4e8 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_8c4ec : bv 32 := 0xfff54513.
Lemma F_8c4ec : fetch_word AsanUbsan.M.loaded_segments (0x8c4ec : word) = Some W_8c4ec.
Proof. vm_refl. Qed.
Lemma D_8c4ec : decode_any W_8c4ec = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
