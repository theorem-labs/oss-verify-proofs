(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_661dc : bv 32 := 0x060a0063.
Lemma F_661dc : fetch_word AsanUbsan.M.loaded_segments (0x6622c : word) = Some W_661dc.
Proof. vm_refl. Qed.
Lemma D_661dc : decode_any W_661dc = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_661e0 : bv 32 := 0x0a051c63.
Lemma F_661e0 : fetch_word AsanUbsan.M.loaded_segments (0x66230 : word) = Some W_661e0.
Proof. vm_refl. Qed.
Lemma D_661e0 : decode_any W_661e0 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_661f4 : bv 32 := 0xfbf48593.
Lemma F_661f4 : fetch_word AsanUbsan.M.loaded_segments (0x66244 : word) = Some W_661f4.
Proof. vm_refl. Qed.
Lemma D_661f4 : decode_any W_661f4 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_661f8 : bv 32 := 0xfbf00613.
Lemma F_661f8 : fetch_word AsanUbsan.M.loaded_segments (0x66248 : word) = Some W_661f8.
Proof. vm_refl. Qed.
Lemma D_661f8 : decode_any W_661f8 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_661fc : bv 32 := 0x12b67663.
Lemma F_661fc : fetch_word AsanUbsan.M.loaded_segments (0x6624c : word) = Some W_661fc.
Proof. vm_refl. Qed.
Lemma D_661fc : decode_any W_661fc = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_66200 : bv 32 := 0x000d7597.
Lemma F_66200 : fetch_word AsanUbsan.M.loaded_segments (0x66250 : word) = Some W_66200.
Proof. vm_refl. Qed.
Lemma D_66200 : decode_any W_66200 = Some (Auipc 11 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_66204 : bv 32 := 0x6785b583.
Lemma F_66204 : fetch_word AsanUbsan.M.loaded_segments (0x66254 : word) = Some W_66204.
Proof. vm_refl. Qed.
Lemma D_66204 : decode_any W_66204 = Some (Load SZ8 true 11 11 1656, 4%Z).
Proof. vm_refl. Qed.

Definition W_66208 : bv 32 := 0x009906b3.
Lemma F_66208 : fetch_word AsanUbsan.M.loaded_segments (0x66258 : word) = Some W_66208.
Proof. vm_refl. Qed.
Lemma D_66208 : decode_any W_66208 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6620c : bv 32 := 0x0005b603.
Lemma F_6620c : fetch_word AsanUbsan.M.loaded_segments (0x6625c : word) = Some W_6620c.
Proof. vm_refl. Qed.
Lemma D_6620c : decode_any W_6620c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66210 : bv 32 := 0x00395593.
Lemma F_66210 : fetch_word AsanUbsan.M.loaded_segments (0x66260 : word) = Some W_66210.
Proof. vm_refl. Qed.
Lemma D_66210 : decode_any W_66210 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_66214 : bv 32 := 0xfff68693.
Lemma F_66214 : fetch_word AsanUbsan.M.loaded_segments (0x66264 : word) = Some W_66214.
Proof. vm_refl. Qed.
Lemma D_66214 : decode_any W_66214 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_66218 : bv 32 := 0x0036d713.
Lemma F_66218 : fetch_word AsanUbsan.M.loaded_segments (0x66268 : word) = Some W_66218.
Proof. vm_refl. Qed.
Lemma D_66218 : decode_any W_66218 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6621c : bv 32 := 0x00b605b3.
Lemma F_6621c : fetch_word AsanUbsan.M.loaded_segments (0x6626c : word) = Some W_6621c.
Proof. vm_refl. Qed.
Lemma D_6621c : decode_any W_6621c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_66220 : bv 32 := 0x00e60633.
Lemma F_66220 : fetch_word AsanUbsan.M.loaded_segments (0x66270 : word) = Some W_66220.
Proof. vm_refl. Qed.
Lemma D_66220 : decode_any W_66220 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66224 : bv 32 := 0xff85f713.
Lemma F_66224 : fetch_word AsanUbsan.M.loaded_segments (0x66274 : word) = Some W_66224.
Proof. vm_refl. Qed.
Lemma D_66224 : decode_any W_66224 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_66228 : bv 32 := 0xff867793.
Lemma F_66228 : fetch_word AsanUbsan.M.loaded_segments (0x66278 : word) = Some W_66228.
Proof. vm_refl. Qed.
Lemma D_66228 : decode_any W_66228 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6622c : bv 32 := 0x00073703.
Lemma F_6622c : fetch_word AsanUbsan.M.loaded_segments (0x6627c : word) = Some W_6622c.
Proof. vm_refl. Qed.
Lemma D_6622c : decode_any W_6622c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66230 : bv 32 := 0x0007b783.
Lemma F_66230 : fetch_word AsanUbsan.M.loaded_segments (0x66280 : word) = Some W_66230.
Proof. vm_refl. Qed.
Lemma D_66230 : decode_any W_66230 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66234 : bv 32 := 0x00e7e733.
Lemma F_66234 : fetch_word AsanUbsan.M.loaded_segments (0x66284 : word) = Some W_66234.
Proof. vm_refl. Qed.
Lemma D_66234 : decode_any W_66234 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66238 : bv 32 := 0x0e071c63.
Lemma F_66238 : fetch_word AsanUbsan.M.loaded_segments (0x66288 : word) = Some W_66238.
Proof. vm_refl. Qed.
Lemma D_66238 : decode_any W_66238 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_66298 : bv 32 := 0x412504b3.
Lemma F_66298 : fetch_word AsanUbsan.M.loaded_segments (0x662e8 : word) = Some W_66298.
Proof. vm_refl. Qed.
Lemma D_66298 : decode_any W_66298 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6629c : bv 32 := 0x00148493.
Lemma F_6629c : fetch_word AsanUbsan.M.loaded_segments (0x662ec : word) = Some W_6629c.
Proof. vm_refl. Qed.
Lemma D_6629c : decode_any W_6629c = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_662a0 : bv 32 := 0xfff94593.
Lemma F_662a0 : fetch_word AsanUbsan.M.loaded_segments (0x662f0 : word) = Some W_662a0.
Proof. vm_refl. Qed.
Lemma D_662a0 : decode_any W_662a0 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_662a4 : bv 32 := 0x80040a13.
Lemma F_662a4 : fetch_word AsanUbsan.M.loaded_segments (0x662f4 : word) = Some W_662a4.
Proof. vm_refl. Qed.
Lemma D_662a4 : decode_any W_662a4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_662a8 : bv 32 := 0xfb0a0a13.
Lemma F_662a8 : fetch_word AsanUbsan.M.loaded_segments (0x662f8 : word) = Some W_662a8.
Proof. vm_refl. Qed.
Lemma D_662a8 : decode_any W_662a8 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_662ac : bv 32 := 0xf495f4e3.
Lemma F_662ac : fetch_word AsanUbsan.M.loaded_segments (0x662fc : word) = Some W_662ac.
Proof. vm_refl. Qed.
Lemma D_662ac : decode_any W_662ac = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_66328 : bv 32 := 0x02049e63.
Lemma F_66328 : fetch_word AsanUbsan.M.loaded_segments (0x66378 : word) = Some W_66328.
Proof. vm_refl. Qed.
Lemma D_66328 : decode_any W_66328 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_66364 : bv 32 := 0x00050a93.
Lemma F_66364 : fetch_word AsanUbsan.M.loaded_segments (0x663b4 : word) = Some W_66364.
Proof. vm_refl. Qed.
Lemma D_66364 : decode_any W_66364 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66368 : bv 32 := 0x00090513.
Lemma F_66368 : fetch_word AsanUbsan.M.loaded_segments (0x663b8 : word) = Some W_66368.
Proof. vm_refl. Qed.
Lemma D_66368 : decode_any W_66368 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6636c : bv 32 := 0x00048593.
Lemma F_6636c : fetch_word AsanUbsan.M.loaded_segments (0x663bc : word) = Some W_6636c.
Proof. vm_refl. Qed.
Lemma D_6636c : decode_any W_6636c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66370 : bv 32 := 0x2ac160ef.
Lemma F_66370 : fetch_word AsanUbsan.M.loaded_segments (0x663c0 : word) = Some W_66370.
Proof. vm_refl. Qed.
Lemma D_66370 : decode_any W_66370 = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

Definition W_66374 : bv 32 := 0x00050913.
Lemma F_66374 : fetch_word AsanUbsan.M.loaded_segments (0x663c4 : word) = Some W_66374.
Proof. vm_refl. Qed.
Lemma D_66374 : decode_any W_66374 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66378 : bv 32 := 0x000a8513.
Lemma F_66378 : fetch_word AsanUbsan.M.loaded_segments (0x663c8 : word) = Some W_66378.
Proof. vm_refl. Qed.
Lemma D_66378 : decode_any W_66378 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6637c : bv 32 := 0xec0900e3.
Lemma F_6637c : fetch_word AsanUbsan.M.loaded_segments (0x663cc : word) = Some W_6637c.
Proof. vm_refl. Qed.
Lemma D_6637c : decode_any W_6637c = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.
