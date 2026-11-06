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

Definition W_7f1e4 : bv 32 := 0x5450006f.
Lemma F_7f1e4 : fetch_word AsanUbsan.M.loaded_segments (0x7f22c : word) = Some W_7f1e4.
Proof. vm_refl. Qed.
Lemma D_7f1e4 : decode_any W_7f1e4 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e8 : bv 32 := 0x2000106f.
Lemma F_7f1e8 : fetch_word AsanUbsan.M.loaded_segments (0x7f230 : word) = Some W_7f1e8.
Proof. vm_refl. Qed.
Lemma D_7f1e8 : decode_any W_7f1e8 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1ec : bv 32 := 0x81010113.
Lemma F_7f1ec : fetch_word AsanUbsan.M.loaded_segments (0x7f234 : word) = Some W_7f1ec.
Proof. vm_refl. Qed.
Lemma D_7f1ec : decode_any W_7f1ec = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f0 : bv 32 := 0x7e113423.
Lemma F_7f1f0 : fetch_word AsanUbsan.M.loaded_segments (0x7f238 : word) = Some W_7f1f0.
Proof. vm_refl. Qed.
Lemma D_7f1f0 : decode_any W_7f1f0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f4 : bv 32 := 0x7e813023.
Lemma F_7f1f4 : fetch_word AsanUbsan.M.loaded_segments (0x7f23c : word) = Some W_7f1f4.
Proof. vm_refl. Qed.
Lemma D_7f1f4 : decode_any W_7f1f4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f8 : bv 32 := 0x7c913c23.
Lemma F_7f1f8 : fetch_word AsanUbsan.M.loaded_segments (0x7f240 : word) = Some W_7f1f8.
Proof. vm_refl. Qed.
Lemma D_7f1f8 : decode_any W_7f1f8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1fc : bv 32 := 0x7d213823.
Lemma F_7f1fc : fetch_word AsanUbsan.M.loaded_segments (0x7f244 : word) = Some W_7f1fc.
Proof. vm_refl. Qed.
Lemma D_7f1fc : decode_any W_7f1fc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f200 : bv 32 := 0x7d313423.
Lemma F_7f200 : fetch_word AsanUbsan.M.loaded_segments (0x7f248 : word) = Some W_7f200.
Proof. vm_refl. Qed.
Lemma D_7f200 : decode_any W_7f200 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f204 : bv 32 := 0x7d413023.
Lemma F_7f204 : fetch_word AsanUbsan.M.loaded_segments (0x7f24c : word) = Some W_7f204.
Proof. vm_refl. Qed.
Lemma D_7f204 : decode_any W_7f204 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f208 : bv 32 := 0x7b513c23.
Lemma F_7f208 : fetch_word AsanUbsan.M.loaded_segments (0x7f250 : word) = Some W_7f208.
Proof. vm_refl. Qed.
Lemma D_7f208 : decode_any W_7f208 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f20c : bv 32 := 0x7b613823.
Lemma F_7f20c : fetch_word AsanUbsan.M.loaded_segments (0x7f254 : word) = Some W_7f20c.
Proof. vm_refl. Qed.
Lemma D_7f20c : decode_any W_7f20c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f210 : bv 32 := 0x7b713423.
Lemma F_7f210 : fetch_word AsanUbsan.M.loaded_segments (0x7f258 : word) = Some W_7f210.
Proof. vm_refl. Qed.
Lemma D_7f210 : decode_any W_7f210 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f214 : bv 32 := 0x7f010413.
Lemma F_7f214 : fetch_word AsanUbsan.M.loaded_segments (0x7f25c : word) = Some W_7f214.
Proof. vm_refl. Qed.
Lemma D_7f214 : decode_any W_7f214 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f218 : bv 32 := 0xf9010113.
Lemma F_7f218 : fetch_word AsanUbsan.M.loaded_segments (0x7f260 : word) = Some W_7f218.
Proof. vm_refl. Qed.
Lemma D_7f218 : decode_any W_7f218 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f21c : bv 32 := 0x000d6697.
Lemma F_7f21c : fetch_word AsanUbsan.M.loaded_segments (0x7f264 : word) = Some W_7f21c.
Proof. vm_refl. Qed.
Lemma D_7f21c : decode_any W_7f21c = Some (Auipc 13 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f220 : bv 32 := 0xe046b683.
Lemma F_7f220 : fetch_word AsanUbsan.M.loaded_segments (0x7f268 : word) = Some W_7f220.
Proof. vm_refl. Qed.
Lemma D_7f220 : decode_any W_7f220 = Some (Load SZ8 true 13 13 3588, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f224 : bv 32 := 0x0006c683.
Lemma F_7f224 : fetch_word AsanUbsan.M.loaded_segments (0x7f26c : word) = Some W_7f224.
Proof. vm_refl. Qed.
Lemma D_7f224 : decode_any W_7f224 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f228 : bv 32 := 0x0e068863.
Lemma F_7f228 : fetch_word AsanUbsan.M.loaded_segments (0x7f270 : word) = Some W_7f228.
Proof. vm_refl. Qed.
Lemma D_7f228 : decode_any W_7f228 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f22c : bv 32 := 0x80040a13.
Lemma F_7f22c : fetch_word AsanUbsan.M.loaded_segments (0x7f274 : word) = Some W_7f22c.
Proof. vm_refl. Qed.
Lemma D_7f22c : decode_any W_7f22c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f230 : bv 32 := 0xfa0a0a13.
Lemma F_7f230 : fetch_word AsanUbsan.M.loaded_segments (0x7f278 : word) = Some W_7f230.
Proof. vm_refl. Qed.
Lemma D_7f230 : decode_any W_7f230 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f234 : bv 32 := 0x00c58ab3.
Lemma F_7f234 : fetch_word AsanUbsan.M.loaded_segments (0x7f27c : word) = Some W_7f234.
Proof. vm_refl. Qed.
Lemma D_7f234 : decode_any W_7f234 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f238 : bv 32 := 0x00c509b3.
Lemma F_7f238 : fetch_word AsanUbsan.M.loaded_segments (0x7f280 : word) = Some W_7f238.
Proof. vm_refl. Qed.
Lemma D_7f238 : decode_any W_7f238 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f23c : bv 32 := 0x00b50663.
Lemma F_7f23c : fetch_word AsanUbsan.M.loaded_segments (0x7f284 : word) = Some W_7f23c.
Proof. vm_refl. Qed.
Lemma D_7f23c : decode_any W_7f23c = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f240 : bv 32 := 0x0135f463.
Lemma F_7f240 : fetch_word AsanUbsan.M.loaded_segments (0x7f288 : word) = Some W_7f240.
Proof. vm_refl. Qed.
Lemma D_7f240 : decode_any W_7f240 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f244 : bv 32 := 0x1b556a63.
Lemma F_7f244 : fetch_word AsanUbsan.M.loaded_segments (0x7f28c : word) = Some W_7f244.
Proof. vm_refl. Qed.
Lemma D_7f244 : decode_any W_7f244 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f248 : bv 32 := 0xfff5c693.
Lemma F_7f248 : fetch_word AsanUbsan.M.loaded_segments (0x7f290 : word) = Some W_7f248.
Proof. vm_refl. Qed.
Lemma D_7f248 : decode_any W_7f248 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f24c : bv 32 := 0x26c6e463.
Lemma F_7f24c : fetch_word AsanUbsan.M.loaded_segments (0x7f294 : word) = Some W_7f24c.
Proof. vm_refl. Qed.
Lemma D_7f24c : decode_any W_7f24c = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f250 : bv 32 := 0xfbf60b13.
Lemma F_7f250 : fetch_word AsanUbsan.M.loaded_segments (0x7f298 : word) = Some W_7f250.
Proof. vm_refl. Qed.
Lemma D_7f250 : decode_any W_7f250 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f254 : bv 32 := 0xfbf00693.
Lemma F_7f254 : fetch_word AsanUbsan.M.loaded_segments (0x7f29c : word) = Some W_7f254.
Proof. vm_refl. Qed.
Lemma D_7f254 : decode_any W_7f254 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f258 : bv 32 := 0x2f66f263.
Lemma F_7f258 : fetch_word AsanUbsan.M.loaded_segments (0x7f2a0 : word) = Some W_7f258.
Proof. vm_refl. Qed.
Lemma D_7f258 : decode_any W_7f258 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f25c : bv 32 := 0x000d5697.
Lemma F_7f25c : fetch_word AsanUbsan.M.loaded_segments (0x7f2a4 : word) = Some W_7f25c.
Proof. vm_refl. Qed.
Lemma D_7f25c : decode_any W_7f25c = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f260 : bv 32 := 0x25c6b683.
Lemma F_7f260 : fetch_word AsanUbsan.M.loaded_segments (0x7f2a8 : word) = Some W_7f260.
Proof. vm_refl. Qed.
Lemma D_7f260 : decode_any W_7f260 = Some (Load SZ8 true 13 13 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f264 : bv 32 := 0x0006b703.
Lemma F_7f264 : fetch_word AsanUbsan.M.loaded_segments (0x7f2ac : word) = Some W_7f264.
Proof. vm_refl. Qed.
Lemma D_7f264 : decode_any W_7f264 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f268 : bv 32 := 0xfffa8a93.
Lemma F_7f268 : fetch_word AsanUbsan.M.loaded_segments (0x7f2b0 : word) = Some W_7f268.
Proof. vm_refl. Qed.
Lemma D_7f268 : decode_any W_7f268 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f26c : bv 32 := 0x0035d693.
Lemma F_7f26c : fetch_word AsanUbsan.M.loaded_segments (0x7f2b4 : word) = Some W_7f26c.
Proof. vm_refl. Qed.
Lemma D_7f26c : decode_any W_7f26c = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f270 : bv 32 := 0x003ad793.
Lemma F_7f270 : fetch_word AsanUbsan.M.loaded_segments (0x7f2b8 : word) = Some W_7f270.
Proof. vm_refl. Qed.
Lemma D_7f270 : decode_any W_7f270 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f274 : bv 32 := 0x00d706b3.
Lemma F_7f274 : fetch_word AsanUbsan.M.loaded_segments (0x7f2bc : word) = Some W_7f274.
Proof. vm_refl. Qed.
Lemma D_7f274 : decode_any W_7f274 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f278 : bv 32 := 0x00f70733.
Lemma F_7f278 : fetch_word AsanUbsan.M.loaded_segments (0x7f2c0 : word) = Some W_7f278.
Proof. vm_refl. Qed.
Lemma D_7f278 : decode_any W_7f278 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f27c : bv 32 := 0xff86f793.
Lemma F_7f27c : fetch_word AsanUbsan.M.loaded_segments (0x7f2c4 : word) = Some W_7f27c.
Proof. vm_refl. Qed.
Lemma D_7f27c : decode_any W_7f27c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f280 : bv 32 := 0xff877813.
Lemma F_7f280 : fetch_word AsanUbsan.M.loaded_segments (0x7f2c8 : word) = Some W_7f280.
Proof. vm_refl. Qed.
Lemma D_7f280 : decode_any W_7f280 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f284 : bv 32 := 0x0007b783.
Lemma F_7f284 : fetch_word AsanUbsan.M.loaded_segments (0x7f2cc : word) = Some W_7f284.
Proof. vm_refl. Qed.
Lemma D_7f284 : decode_any W_7f284 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f288 : bv 32 := 0x00083803.
Lemma F_7f288 : fetch_word AsanUbsan.M.loaded_segments (0x7f2d0 : word) = Some W_7f288.
Proof. vm_refl. Qed.
Lemma D_7f288 : decode_any W_7f288 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f28c : bv 32 := 0x00f867b3.
Lemma F_7f28c : fetch_word AsanUbsan.M.loaded_segments (0x7f2d4 : word) = Some W_7f28c.
Proof. vm_refl. Qed.
Lemma D_7f28c : decode_any W_7f28c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f290 : bv 32 := 0x2a079a63.
Lemma F_7f290 : fetch_word AsanUbsan.M.loaded_segments (0x7f2d8 : word) = Some W_7f290.
Proof. vm_refl. Qed.
Lemma D_7f290 : decode_any W_7f290 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f294 : bv 32 := 0xfff54693.
Lemma F_7f294 : fetch_word AsanUbsan.M.loaded_segments (0x7f2dc : word) = Some W_7f294.
Proof. vm_refl. Qed.
Lemma D_7f294 : decode_any W_7f294 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f298 : bv 32 := 0x0cc6ea63.
Lemma F_7f298 : fetch_word AsanUbsan.M.loaded_segments (0x7f2e0 : word) = Some W_7f298.
Proof. vm_refl. Qed.
Lemma D_7f298 : decode_any W_7f298 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f29c : bv 32 := 0xfbf00693.
Lemma F_7f29c : fetch_word AsanUbsan.M.loaded_segments (0x7f2e4 : word) = Some W_7f29c.
Proof. vm_refl. Qed.
Lemma D_7f29c : decode_any W_7f29c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a0 : bv 32 := 0x1566f863.
Lemma F_7f2a0 : fetch_word AsanUbsan.M.loaded_segments (0x7f2e8 : word) = Some W_7f2a0.
Proof. vm_refl. Qed.
Lemma D_7f2a0 : decode_any W_7f2a0 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a4 : bv 32 := 0x000d5697.
Lemma F_7f2a4 : fetch_word AsanUbsan.M.loaded_segments (0x7f2ec : word) = Some W_7f2a4.
Proof. vm_refl. Qed.
Lemma D_7f2a4 : decode_any W_7f2a4 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a8 : bv 32 := 0x2146b683.
Lemma F_7f2a8 : fetch_word AsanUbsan.M.loaded_segments (0x7f2f0 : word) = Some W_7f2a8.
Proof. vm_refl. Qed.
Lemma D_7f2a8 : decode_any W_7f2a8 = Some (Load SZ8 true 13 13 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ac : bv 32 := 0x0006b703.
Lemma F_7f2ac : fetch_word AsanUbsan.M.loaded_segments (0x7f2f4 : word) = Some W_7f2ac.
Proof. vm_refl. Qed.
Lemma D_7f2ac : decode_any W_7f2ac = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b0 : bv 32 := 0xfff98993.
Lemma F_7f2b0 : fetch_word AsanUbsan.M.loaded_segments (0x7f2f8 : word) = Some W_7f2b0.
Proof. vm_refl. Qed.
Lemma D_7f2b0 : decode_any W_7f2b0 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b4 : bv 32 := 0x00355693.
Lemma F_7f2b4 : fetch_word AsanUbsan.M.loaded_segments (0x7f2fc : word) = Some W_7f2b4.
Proof. vm_refl. Qed.
Lemma D_7f2b4 : decode_any W_7f2b4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b8 : bv 32 := 0x0039d793.
Lemma F_7f2b8 : fetch_word AsanUbsan.M.loaded_segments (0x7f300 : word) = Some W_7f2b8.
Proof. vm_refl. Qed.
Lemma D_7f2b8 : decode_any W_7f2b8 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2bc : bv 32 := 0x00d706b3.
Lemma F_7f2bc : fetch_word AsanUbsan.M.loaded_segments (0x7f304 : word) = Some W_7f2bc.
Proof. vm_refl. Qed.
Lemma D_7f2bc : decode_any W_7f2bc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c0 : bv 32 := 0x00f70733.
Lemma F_7f2c0 : fetch_word AsanUbsan.M.loaded_segments (0x7f308 : word) = Some W_7f2c0.
Proof. vm_refl. Qed.
Lemma D_7f2c0 : decode_any W_7f2c0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c4 : bv 32 := 0xff86f793.
Lemma F_7f2c4 : fetch_word AsanUbsan.M.loaded_segments (0x7f30c : word) = Some W_7f2c4.
Proof. vm_refl. Qed.
Lemma D_7f2c4 : decode_any W_7f2c4 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c8 : bv 32 := 0xff877813.
Lemma F_7f2c8 : fetch_word AsanUbsan.M.loaded_segments (0x7f310 : word) = Some W_7f2c8.
Proof. vm_refl. Qed.
Lemma D_7f2c8 : decode_any W_7f2c8 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2cc : bv 32 := 0x0007b783.
Lemma F_7f2cc : fetch_word AsanUbsan.M.loaded_segments (0x7f314 : word) = Some W_7f2cc.
Proof. vm_refl. Qed.
Lemma D_7f2cc : decode_any W_7f2cc = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d0 : bv 32 := 0x00083803.
Lemma F_7f2d0 : fetch_word AsanUbsan.M.loaded_segments (0x7f318 : word) = Some W_7f2d0.
Proof. vm_refl. Qed.
Lemma D_7f2d0 : decode_any W_7f2d0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d4 : bv 32 := 0x00f867b3.
Lemma F_7f2d4 : fetch_word AsanUbsan.M.loaded_segments (0x7f31c : word) = Some W_7f2d4.
Proof. vm_refl. Qed.
Lemma D_7f2d4 : decode_any W_7f2d4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d8 : bv 32 := 0x30079863.
Lemma F_7f2d8 : fetch_word AsanUbsan.M.loaded_segments (0x7f320 : word) = Some W_7f2d8.
Proof. vm_refl. Qed.
Lemma D_7f2d8 : decode_any W_7f2d8 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2dc : bv 32 := 0x000d7697.
Lemma F_7f2dc : fetch_word AsanUbsan.M.loaded_segments (0x7f324 : word) = Some W_7f2dc.
Proof. vm_refl. Qed.
Lemma D_7f2dc : decode_any W_7f2dc = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e0 : bv 32 := 0x1fc6b683.
Lemma F_7f2e0 : fetch_word AsanUbsan.M.loaded_segments (0x7f328 : word) = Some W_7f2e0.
Proof. vm_refl. Qed.
Lemma D_7f2e0 : decode_any W_7f2e0 = Some (Load SZ8 true 13 13 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e4 : bv 32 := 0x000680e7.
Lemma F_7f2e4 : fetch_word AsanUbsan.M.loaded_segments (0x7f32c : word) = Some W_7f2e4.
Proof. vm_refl. Qed.
Lemma D_7f2e4 : decode_any W_7f2e4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e8 : bv 32 := 0x07010113.
Lemma F_7f2e8 : fetch_word AsanUbsan.M.loaded_segments (0x7f330 : word) = Some W_7f2e8.
Proof. vm_refl. Qed.
Lemma D_7f2e8 : decode_any W_7f2e8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ec : bv 32 := 0x7e813083.
Lemma F_7f2ec : fetch_word AsanUbsan.M.loaded_segments (0x7f334 : word) = Some W_7f2ec.
Proof. vm_refl. Qed.
Lemma D_7f2ec : decode_any W_7f2ec = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f0 : bv 32 := 0x7e013403.
Lemma F_7f2f0 : fetch_word AsanUbsan.M.loaded_segments (0x7f338 : word) = Some W_7f2f0.
Proof. vm_refl. Qed.
Lemma D_7f2f0 : decode_any W_7f2f0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f4 : bv 32 := 0x7d813483.
Lemma F_7f2f4 : fetch_word AsanUbsan.M.loaded_segments (0x7f33c : word) = Some W_7f2f4.
Proof. vm_refl. Qed.
Lemma D_7f2f4 : decode_any W_7f2f4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f8 : bv 32 := 0x7d013903.
Lemma F_7f2f8 : fetch_word AsanUbsan.M.loaded_segments (0x7f340 : word) = Some W_7f2f8.
Proof. vm_refl. Qed.
Lemma D_7f2f8 : decode_any W_7f2f8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2fc : bv 32 := 0x7c813983.
Lemma F_7f2fc : fetch_word AsanUbsan.M.loaded_segments (0x7f344 : word) = Some W_7f2fc.
Proof. vm_refl. Qed.
Lemma D_7f2fc : decode_any W_7f2fc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f300 : bv 32 := 0x7c013a03.
Lemma F_7f300 : fetch_word AsanUbsan.M.loaded_segments (0x7f348 : word) = Some W_7f300.
Proof. vm_refl. Qed.
Lemma D_7f300 : decode_any W_7f300 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f304 : bv 32 := 0x7b813a83.
Lemma F_7f304 : fetch_word AsanUbsan.M.loaded_segments (0x7f34c : word) = Some W_7f304.
Proof. vm_refl. Qed.
Lemma D_7f304 : decode_any W_7f304 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f308 : bv 32 := 0x7b013b03.
Lemma F_7f308 : fetch_word AsanUbsan.M.loaded_segments (0x7f350 : word) = Some W_7f308.
Proof. vm_refl. Qed.
Lemma D_7f308 : decode_any W_7f308 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f30c : bv 32 := 0x7a813b83.
Lemma F_7f30c : fetch_word AsanUbsan.M.loaded_segments (0x7f354 : word) = Some W_7f30c.
Proof. vm_refl. Qed.
Lemma D_7f30c : decode_any W_7f30c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f310 : bv 32 := 0x7f010113.
Lemma F_7f310 : fetch_word AsanUbsan.M.loaded_segments (0x7f358 : word) = Some W_7f310.
Proof. vm_refl. Qed.
Lemma D_7f310 : decode_any W_7f310 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f314 : bv 32 := 0x00008067.
Lemma F_7f314 : fetch_word AsanUbsan.M.loaded_segments (0x7f35c : word) = Some W_7f314.
Proof. vm_refl. Qed.
Lemma D_7f314 : decode_any W_7f314 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3f0 : bv 32 := 0x22061663.
Lemma F_7f3f0 : fetch_word AsanUbsan.M.loaded_segments (0x7f438 : word) = Some W_7f3f0.
Proof. vm_refl. Qed.
Lemma D_7f3f0 : decode_any W_7f3f0 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3f4 : bv 32 := 0xee9ff06f.
Lemma F_7f3f4 : fetch_word AsanUbsan.M.loaded_segments (0x7f43c : word) = Some W_7f3f4.
Proof. vm_refl. Qed.
Lemma D_7f3f4 : decode_any W_7f3f4 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f53c : bv 32 := 0x02061e63.
Lemma F_7f53c : fetch_word AsanUbsan.M.loaded_segments (0x7f584 : word) = Some W_7f53c.
Proof. vm_refl. Qed.
Lemma D_7f53c : decode_any W_7f53c = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f540 : bv 32 := 0xd55ff06f.
Lemma F_7f540 : fetch_word AsanUbsan.M.loaded_segments (0x7f588 : word) = Some W_7f540.
Proof. vm_refl. Qed.
Lemma D_7f540 : decode_any W_7f540 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f544 : bv 32 := 0x00070783.
Lemma F_7f544 : fetch_word AsanUbsan.M.loaded_segments (0x7f58c : word) = Some W_7f544.
Proof. vm_refl. Qed.
Lemma D_7f544 : decode_any W_7f544 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f548 : bv 32 := 0x007af813.
Lemma F_7f548 : fetch_word AsanUbsan.M.loaded_segments (0x7f590 : word) = Some W_7f548.
Proof. vm_refl. Qed.
Lemma D_7f548 : decode_any W_7f548 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f54c : bv 32 := 0x00f038b3.
Lemma F_7f54c : fetch_word AsanUbsan.M.loaded_segments (0x7f594 : word) = Some W_7f54c.
Proof. vm_refl. Qed.
Lemma D_7f54c : decode_any W_7f54c = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f550 : bv 32 := 0x00f827b3.
Lemma F_7f550 : fetch_word AsanUbsan.M.loaded_segments (0x7f598 : word) = Some W_7f550.
Proof. vm_refl. Qed.
Lemma D_7f550 : decode_any W_7f550 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f554 : bv 32 := 0x0017c793.
Lemma F_7f554 : fetch_word AsanUbsan.M.loaded_segments (0x7f59c : word) = Some W_7f554.
Proof. vm_refl. Qed.
Lemma D_7f554 : decode_any W_7f554 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f558 : bv 32 := 0x00f8f7b3.
Lemma F_7f558 : fetch_word AsanUbsan.M.loaded_segments (0x7f5a0 : word) = Some W_7f558.
Proof. vm_refl. Qed.
Lemma D_7f558 : decode_any W_7f558 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f55c : bv 32 := 0x00e6fa63.
Lemma F_7f55c : fetch_word AsanUbsan.M.loaded_segments (0x7f5a4 : word) = Some W_7f55c.
Proof. vm_refl. Qed.
Lemma D_7f55c : decode_any W_7f55c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f560 : bv 32 := 0x0006c803.
Lemma F_7f560 : fetch_word AsanUbsan.M.loaded_segments (0x7f5a8 : word) = Some W_7f560.
Proof. vm_refl. Qed.
Lemma D_7f560 : decode_any W_7f560 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f564 : bv 32 := 0x00168693.
Lemma F_7f564 : fetch_word AsanUbsan.M.loaded_segments (0x7f5ac : word) = Some W_7f564.
Proof. vm_refl. Qed.
Lemma D_7f564 : decode_any W_7f564 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f568 : bv 32 := 0x00f867b3.
Lemma F_7f568 : fetch_word AsanUbsan.M.loaded_segments (0x7f5b0 : word) = Some W_7f568.
Proof. vm_refl. Qed.
Lemma D_7f568 : decode_any W_7f568 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f56c : bv 32 := 0xfee69ae3.
Lemma F_7f56c : fetch_word AsanUbsan.M.loaded_segments (0x7f5b4 : word) = Some W_7f56c.
Proof. vm_refl. Qed.
Lemma D_7f56c : decode_any W_7f56c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f570 : bv 32 := 0x0ff7f693.
Lemma F_7f570 : fetch_word AsanUbsan.M.loaded_segments (0x7f5b8 : word) = Some W_7f570.
Proof. vm_refl. Qed.
Lemma D_7f570 : decode_any W_7f570 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f574 : bv 32 := 0xd20680e3.
Lemma F_7f574 : fetch_word AsanUbsan.M.loaded_segments (0x7f5bc : word) = Some W_7f574.
Proof. vm_refl. Qed.
Lemma D_7f574 : decode_any W_7f574 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f578 : bv 32 := 0x00050a93.
Lemma F_7f578 : fetch_word AsanUbsan.M.loaded_segments (0x7f5c0 : word) = Some W_7f578.
Proof. vm_refl. Qed.
Lemma D_7f578 : decode_any W_7f578 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f57c : bv 32 := 0x00058513.
Lemma F_7f57c : fetch_word AsanUbsan.M.loaded_segments (0x7f5c4 : word) = Some W_7f57c.
Proof. vm_refl. Qed.
Lemma D_7f57c : decode_any W_7f57c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f580 : bv 32 := 0x00058b93.
Lemma F_7f580 : fetch_word AsanUbsan.M.loaded_segments (0x7f5c8 : word) = Some W_7f580.
Proof. vm_refl. Qed.
Lemma D_7f580 : decode_any W_7f580 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f584 : bv 32 := 0x00060593.
Lemma F_7f584 : fetch_word AsanUbsan.M.loaded_segments (0x7f5cc : word) = Some W_7f584.
Proof. vm_refl. Qed.
Lemma D_7f584 : decode_any W_7f584 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f588 : bv 32 := 0x00060493.
Lemma F_7f588 : fetch_word AsanUbsan.M.loaded_segments (0x7f5d0 : word) = Some W_7f588.
Proof. vm_refl. Qed.
Lemma D_7f588 : decode_any W_7f588 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f58c : bv 32 := 0x48c030ef.
Lemma F_7f58c : fetch_word AsanUbsan.M.loaded_segments (0x7f5d4 : word) = Some W_7f58c.
Proof. vm_refl. Qed.
Lemma D_7f58c : decode_any W_7f58c = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f590 : bv 32 := 0x000b8593.
Lemma F_7f590 : fetch_word AsanUbsan.M.loaded_segments (0x7f5d8 : word) = Some W_7f590.
Proof. vm_refl. Qed.
Lemma D_7f590 : decode_any W_7f590 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f594 : bv 32 := 0x00048613.
Lemma F_7f594 : fetch_word AsanUbsan.M.loaded_segments (0x7f5dc : word) = Some W_7f594.
Proof. vm_refl. Qed.
Lemma D_7f594 : decode_any W_7f594 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f598 : bv 32 := 0x00050913.
Lemma F_7f598 : fetch_word AsanUbsan.M.loaded_segments (0x7f5e0 : word) = Some W_7f598.
Proof. vm_refl. Qed.
Lemma D_7f598 : decode_any W_7f598 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f59c : bv 32 := 0x000a8513.
Lemma F_7f59c : fetch_word AsanUbsan.M.loaded_segments (0x7f5e4 : word) = Some W_7f59c.
Proof. vm_refl. Qed.
Lemma D_7f59c : decode_any W_7f59c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a0 : bv 32 := 0xce090ae3.
Lemma F_7f5a0 : fetch_word AsanUbsan.M.loaded_segments (0x7f5e8 : word) = Some W_7f5a0.
Proof. vm_refl. Qed.
Lemma D_7f5a0 : decode_any W_7f5a0 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e8 : bv 32 := 0x00070783.
Lemma F_7f5e8 : fetch_word AsanUbsan.M.loaded_segments (0x7f630 : word) = Some W_7f5e8.
Proof. vm_refl. Qed.
Lemma D_7f5e8 : decode_any W_7f5e8 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5ec : bv 32 := 0x0079f813.
Lemma F_7f5ec : fetch_word AsanUbsan.M.loaded_segments (0x7f634 : word) = Some W_7f5ec.
Proof. vm_refl. Qed.
Lemma D_7f5ec : decode_any W_7f5ec = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f0 : bv 32 := 0x00f038b3.
Lemma F_7f5f0 : fetch_word AsanUbsan.M.loaded_segments (0x7f638 : word) = Some W_7f5f0.
Proof. vm_refl. Qed.
Lemma D_7f5f0 : decode_any W_7f5f0 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f4 : bv 32 := 0x00f827b3.
Lemma F_7f5f4 : fetch_word AsanUbsan.M.loaded_segments (0x7f63c : word) = Some W_7f5f4.
Proof. vm_refl. Qed.
Lemma D_7f5f4 : decode_any W_7f5f4 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f8 : bv 32 := 0x0017c793.
Lemma F_7f5f8 : fetch_word AsanUbsan.M.loaded_segments (0x7f640 : word) = Some W_7f5f8.
Proof. vm_refl. Qed.
Lemma D_7f5f8 : decode_any W_7f5f8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5fc : bv 32 := 0x00f8f7b3.
Lemma F_7f5fc : fetch_word AsanUbsan.M.loaded_segments (0x7f644 : word) = Some W_7f5fc.
Proof. vm_refl. Qed.
Lemma D_7f5fc : decode_any W_7f5fc = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f600 : bv 32 := 0x00e6fa63.
Lemma F_7f600 : fetch_word AsanUbsan.M.loaded_segments (0x7f648 : word) = Some W_7f600.
Proof. vm_refl. Qed.
Lemma D_7f600 : decode_any W_7f600 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f604 : bv 32 := 0x0006c803.
Lemma F_7f604 : fetch_word AsanUbsan.M.loaded_segments (0x7f64c : word) = Some W_7f604.
Proof. vm_refl. Qed.
Lemma D_7f604 : decode_any W_7f604 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f608 : bv 32 := 0x00168693.
Lemma F_7f608 : fetch_word AsanUbsan.M.loaded_segments (0x7f650 : word) = Some W_7f608.
Proof. vm_refl. Qed.
Lemma D_7f608 : decode_any W_7f608 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f60c : bv 32 := 0x00f867b3.
Lemma F_7f60c : fetch_word AsanUbsan.M.loaded_segments (0x7f654 : word) = Some W_7f60c.
Proof. vm_refl. Qed.
Lemma D_7f60c : decode_any W_7f60c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f610 : bv 32 := 0xfee69ae3.
Lemma F_7f610 : fetch_word AsanUbsan.M.loaded_segments (0x7f658 : word) = Some W_7f610.
Proof. vm_refl. Qed.
Lemma D_7f610 : decode_any W_7f610 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f614 : bv 32 := 0x0ff7f693.
Lemma F_7f614 : fetch_word AsanUbsan.M.loaded_segments (0x7f65c : word) = Some W_7f614.
Proof. vm_refl. Qed.
Lemma D_7f614 : decode_any W_7f614 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f618 : bv 32 := 0xcc0682e3.
Lemma F_7f618 : fetch_word AsanUbsan.M.loaded_segments (0x7f660 : word) = Some W_7f618.
Proof. vm_refl. Qed.
Lemma D_7f618 : decode_any W_7f618 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f61c : bv 32 := 0x00050493.
Lemma F_7f61c : fetch_word AsanUbsan.M.loaded_segments (0x7f664 : word) = Some W_7f61c.
Proof. vm_refl. Qed.
Lemma D_7f61c : decode_any W_7f61c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f620 : bv 32 := 0x00058a93.
Lemma F_7f620 : fetch_word AsanUbsan.M.loaded_segments (0x7f668 : word) = Some W_7f620.
Proof. vm_refl. Qed.
Lemma D_7f620 : decode_any W_7f620 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f624 : bv 32 := 0x00060593.
Lemma F_7f624 : fetch_word AsanUbsan.M.loaded_segments (0x7f66c : word) = Some W_7f624.
Proof. vm_refl. Qed.
Lemma D_7f624 : decode_any W_7f624 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f628 : bv 32 := 0x00060913.
Lemma F_7f628 : fetch_word AsanUbsan.M.loaded_segments (0x7f670 : word) = Some W_7f628.
Proof. vm_refl. Qed.
Lemma D_7f628 : decode_any W_7f628 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f62c : bv 32 := 0x3ec030ef.
Lemma F_7f62c : fetch_word AsanUbsan.M.loaded_segments (0x7f674 : word) = Some W_7f62c.
Proof. vm_refl. Qed.
Lemma D_7f62c : decode_any W_7f62c = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f630 : bv 32 := 0x000a8593.
Lemma F_7f630 : fetch_word AsanUbsan.M.loaded_segments (0x7f678 : word) = Some W_7f630.
Proof. vm_refl. Qed.
Lemma D_7f630 : decode_any W_7f630 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f634 : bv 32 := 0x00090613.
Lemma F_7f634 : fetch_word AsanUbsan.M.loaded_segments (0x7f67c : word) = Some W_7f634.
Proof. vm_refl. Qed.
Lemma D_7f634 : decode_any W_7f634 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f638 : bv 32 := 0x00050993.
Lemma F_7f638 : fetch_word AsanUbsan.M.loaded_segments (0x7f680 : word) = Some W_7f638.
Proof. vm_refl. Qed.
Lemma D_7f638 : decode_any W_7f638 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f63c : bv 32 := 0x00048513.
Lemma F_7f63c : fetch_word AsanUbsan.M.loaded_segments (0x7f684 : word) = Some W_7f63c.
Proof. vm_refl. Qed.
Lemma D_7f63c : decode_any W_7f63c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f640 : bv 32 := 0xc8098ee3.
Lemma F_7f640 : fetch_word AsanUbsan.M.loaded_segments (0x7f688 : word) = Some W_7f640.
Proof. vm_refl. Qed.
Lemma D_7f640 : decode_any W_7f640 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f688 : bv 32 := 0x81010113.
Lemma F_7f688 : fetch_word AsanUbsan.M.loaded_segments (0x7f6d0 : word) = Some W_7f688.
Proof. vm_refl. Qed.
Lemma D_7f688 : decode_any W_7f688 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f68c : bv 32 := 0x7e113423.
Lemma F_7f68c : fetch_word AsanUbsan.M.loaded_segments (0x7f6d4 : word) = Some W_7f68c.
Proof. vm_refl. Qed.
Lemma D_7f68c : decode_any W_7f68c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f690 : bv 32 := 0x7e813023.
Lemma F_7f690 : fetch_word AsanUbsan.M.loaded_segments (0x7f6d8 : word) = Some W_7f690.
Proof. vm_refl. Qed.
Lemma D_7f690 : decode_any W_7f690 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f694 : bv 32 := 0x7c913c23.
Lemma F_7f694 : fetch_word AsanUbsan.M.loaded_segments (0x7f6dc : word) = Some W_7f694.
Proof. vm_refl. Qed.
Lemma D_7f694 : decode_any W_7f694 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f698 : bv 32 := 0x7d213823.
Lemma F_7f698 : fetch_word AsanUbsan.M.loaded_segments (0x7f6e0 : word) = Some W_7f698.
Proof. vm_refl. Qed.
Lemma D_7f698 : decode_any W_7f698 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f69c : bv 32 := 0x7d313423.
Lemma F_7f69c : fetch_word AsanUbsan.M.loaded_segments (0x7f6e4 : word) = Some W_7f69c.
Proof. vm_refl. Qed.
Lemma D_7f69c : decode_any W_7f69c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6a0 : bv 32 := 0x7d413023.
Lemma F_7f6a0 : fetch_word AsanUbsan.M.loaded_segments (0x7f6e8 : word) = Some W_7f6a0.
Proof. vm_refl. Qed.
Lemma D_7f6a0 : decode_any W_7f6a0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6a4 : bv 32 := 0x7b513c23.
Lemma F_7f6a4 : fetch_word AsanUbsan.M.loaded_segments (0x7f6ec : word) = Some W_7f6a4.
Proof. vm_refl. Qed.
Lemma D_7f6a4 : decode_any W_7f6a4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6a8 : bv 32 := 0x7f010413.
Lemma F_7f6a8 : fetch_word AsanUbsan.M.loaded_segments (0x7f6f0 : word) = Some W_7f6a8.
Proof. vm_refl. Qed.
Lemma D_7f6a8 : decode_any W_7f6a8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6ac : bv 32 := 0xfa010113.
Lemma F_7f6ac : fetch_word AsanUbsan.M.loaded_segments (0x7f6f4 : word) = Some W_7f6ac.
Proof. vm_refl. Qed.
Lemma D_7f6ac : decode_any W_7f6ac = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6b0 : bv 32 := 0x000d6697.
Lemma F_7f6b0 : fetch_word AsanUbsan.M.loaded_segments (0x7f6f8 : word) = Some W_7f6b0.
Proof. vm_refl. Qed.
Lemma D_7f6b0 : decode_any W_7f6b0 = Some (Auipc 13 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6b4 : bv 32 := 0x9706b683.
Lemma F_7f6b4 : fetch_word AsanUbsan.M.loaded_segments (0x7f6fc : word) = Some W_7f6b4.
Proof. vm_refl. Qed.
Lemma D_7f6b4 : decode_any W_7f6b4 = Some (Load SZ8 true 13 13 2416, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6b8 : bv 32 := 0x0006c683.
Lemma F_7f6b8 : fetch_word AsanUbsan.M.loaded_segments (0x7f700 : word) = Some W_7f6b8.
Proof. vm_refl. Qed.
Lemma D_7f6b8 : decode_any W_7f6b8 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6bc : bv 32 := 0x08068863.
Lemma F_7f6bc : fetch_word AsanUbsan.M.loaded_segments (0x7f704 : word) = Some W_7f6bc.
Proof. vm_refl. Qed.
Lemma D_7f6bc : decode_any W_7f6bc = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6c0 : bv 32 := 0xfff54693.
Lemma F_7f6c0 : fetch_word AsanUbsan.M.loaded_segments (0x7f708 : word) = Some W_7f6c0.
Proof. vm_refl. Qed.
Lemma D_7f6c0 : decode_any W_7f6c0 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6c4 : bv 32 := 0x80040a13.
Lemma F_7f6c4 : fetch_word AsanUbsan.M.loaded_segments (0x7f70c : word) = Some W_7f6c4.
Proof. vm_refl. Qed.
Lemma D_7f6c4 : decode_any W_7f6c4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6c8 : bv 32 := 0xfb0a0a13.
Lemma F_7f6c8 : fetch_word AsanUbsan.M.loaded_segments (0x7f710 : word) = Some W_7f6c8.
Proof. vm_refl. Qed.
Lemma D_7f6c8 : decode_any W_7f6c8 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6cc : bv 32 := 0x0cc6e663.
Lemma F_7f6cc : fetch_word AsanUbsan.M.loaded_segments (0x7f714 : word) = Some W_7f6cc.
Proof. vm_refl. Qed.
Lemma D_7f6cc : decode_any W_7f6cc = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6d0 : bv 32 := 0xfbf60693.
Lemma F_7f6d0 : fetch_word AsanUbsan.M.loaded_segments (0x7f718 : word) = Some W_7f6d0.
Proof. vm_refl. Qed.
Lemma D_7f6d0 : decode_any W_7f6d0 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6d4 : bv 32 := 0xfbf00713.
Lemma F_7f6d4 : fetch_word AsanUbsan.M.loaded_segments (0x7f71c : word) = Some W_7f6d4.
Proof. vm_refl. Qed.
Lemma D_7f6d4 : decode_any W_7f6d4 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6d8 : bv 32 := 0x14d77463.
Lemma F_7f6d8 : fetch_word AsanUbsan.M.loaded_segments (0x7f720 : word) = Some W_7f6d8.
Proof. vm_refl. Qed.
Lemma D_7f6d8 : decode_any W_7f6d8 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6dc : bv 32 := 0x000d5697.
Lemma F_7f6dc : fetch_word AsanUbsan.M.loaded_segments (0x7f724 : word) = Some W_7f6dc.
Proof. vm_refl. Qed.
Lemma D_7f6dc : decode_any W_7f6dc = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6e0 : bv 32 := 0xddc6b683.
Lemma F_7f6e0 : fetch_word AsanUbsan.M.loaded_segments (0x7f728 : word) = Some W_7f6e0.
Proof. vm_refl. Qed.
Lemma D_7f6e0 : decode_any W_7f6e0 = Some (Load SZ8 true 13 13 3548, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6e4 : bv 32 := 0x00c507b3.
Lemma F_7f6e4 : fetch_word AsanUbsan.M.loaded_segments (0x7f72c : word) = Some W_7f6e4.
Proof. vm_refl. Qed.
Lemma D_7f6e4 : decode_any W_7f6e4 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6e8 : bv 32 := 0x0006b703.
Lemma F_7f6e8 : fetch_word AsanUbsan.M.loaded_segments (0x7f730 : word) = Some W_7f6e8.
Proof. vm_refl. Qed.
Lemma D_7f6e8 : decode_any W_7f6e8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6ec : bv 32 := 0x00355693.
Lemma F_7f6ec : fetch_word AsanUbsan.M.loaded_segments (0x7f734 : word) = Some W_7f6ec.
Proof. vm_refl. Qed.
Lemma D_7f6ec : decode_any W_7f6ec = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6f0 : bv 32 := 0xfff78793.
Lemma F_7f6f0 : fetch_word AsanUbsan.M.loaded_segments (0x7f738 : word) = Some W_7f6f0.
Proof. vm_refl. Qed.
Lemma D_7f6f0 : decode_any W_7f6f0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6f4 : bv 32 := 0x0037d813.
Lemma F_7f6f4 : fetch_word AsanUbsan.M.loaded_segments (0x7f73c : word) = Some W_7f6f4.
Proof. vm_refl. Qed.
Lemma D_7f6f4 : decode_any W_7f6f4 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6f8 : bv 32 := 0x00d706b3.
Lemma F_7f6f8 : fetch_word AsanUbsan.M.loaded_segments (0x7f740 : word) = Some W_7f6f8.
Proof. vm_refl. Qed.
Lemma D_7f6f8 : decode_any W_7f6f8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6fc : bv 32 := 0x01070733.
Lemma F_7f6fc : fetch_word AsanUbsan.M.loaded_segments (0x7f744 : word) = Some W_7f6fc.
Proof. vm_refl. Qed.
Lemma D_7f6fc : decode_any W_7f6fc = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f700 : bv 32 := 0xff86f813.
Lemma F_7f700 : fetch_word AsanUbsan.M.loaded_segments (0x7f748 : word) = Some W_7f700.
Proof. vm_refl. Qed.
Lemma D_7f700 : decode_any W_7f700 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f704 : bv 32 := 0xff877893.
Lemma F_7f704 : fetch_word AsanUbsan.M.loaded_segments (0x7f74c : word) = Some W_7f704.
Proof. vm_refl. Qed.
Lemma D_7f704 : decode_any W_7f704 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f708 : bv 32 := 0x00083803.
Lemma F_7f708 : fetch_word AsanUbsan.M.loaded_segments (0x7f750 : word) = Some W_7f708.
Proof. vm_refl. Qed.
Lemma D_7f708 : decode_any W_7f708 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f70c : bv 32 := 0x0008b883.
Lemma F_7f70c : fetch_word AsanUbsan.M.loaded_segments (0x7f754 : word) = Some W_7f70c.
Proof. vm_refl. Qed.
Lemma D_7f70c : decode_any W_7f70c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f710 : bv 32 := 0x0108e833.
Lemma F_7f710 : fetch_word AsanUbsan.M.loaded_segments (0x7f758 : word) = Some W_7f710.
Proof. vm_refl. Qed.
Lemma D_7f710 : decode_any W_7f710 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f714 : bv 32 := 0x10081a63.
Lemma F_7f714 : fetch_word AsanUbsan.M.loaded_segments (0x7f75c : word) = Some W_7f714.
Proof. vm_refl. Qed.
Lemma D_7f714 : decode_any W_7f714 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f718 : bv 32 := 0x000d7697.
Lemma F_7f718 : fetch_word AsanUbsan.M.loaded_segments (0x7f760 : word) = Some W_7f718.
Proof. vm_refl. Qed.
Lemma D_7f718 : decode_any W_7f718 = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f71c : bv 32 := 0xdc86b683.
Lemma F_7f71c : fetch_word AsanUbsan.M.loaded_segments (0x7f764 : word) = Some W_7f71c.
Proof. vm_refl. Qed.
Lemma D_7f71c : decode_any W_7f71c = Some (Load SZ8 true 13 13 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f720 : bv 32 := 0x000680e7.
Lemma F_7f720 : fetch_word AsanUbsan.M.loaded_segments (0x7f768 : word) = Some W_7f720.
Proof. vm_refl. Qed.
Lemma D_7f720 : decode_any W_7f720 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f724 : bv 32 := 0x06010113.
Lemma F_7f724 : fetch_word AsanUbsan.M.loaded_segments (0x7f76c : word) = Some W_7f724.
Proof. vm_refl. Qed.
Lemma D_7f724 : decode_any W_7f724 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f728 : bv 32 := 0x7e813083.
Lemma F_7f728 : fetch_word AsanUbsan.M.loaded_segments (0x7f770 : word) = Some W_7f728.
Proof. vm_refl. Qed.
Lemma D_7f728 : decode_any W_7f728 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f72c : bv 32 := 0x7e013403.
Lemma F_7f72c : fetch_word AsanUbsan.M.loaded_segments (0x7f774 : word) = Some W_7f72c.
Proof. vm_refl. Qed.
Lemma D_7f72c : decode_any W_7f72c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f730 : bv 32 := 0x7d813483.
Lemma F_7f730 : fetch_word AsanUbsan.M.loaded_segments (0x7f778 : word) = Some W_7f730.
Proof. vm_refl. Qed.
Lemma D_7f730 : decode_any W_7f730 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f734 : bv 32 := 0x7d013903.
Lemma F_7f734 : fetch_word AsanUbsan.M.loaded_segments (0x7f77c : word) = Some W_7f734.
Proof. vm_refl. Qed.
Lemma D_7f734 : decode_any W_7f734 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f738 : bv 32 := 0x7c813983.
Lemma F_7f738 : fetch_word AsanUbsan.M.loaded_segments (0x7f780 : word) = Some W_7f738.
Proof. vm_refl. Qed.
Lemma D_7f738 : decode_any W_7f738 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f73c : bv 32 := 0x7c013a03.
Lemma F_7f73c : fetch_word AsanUbsan.M.loaded_segments (0x7f784 : word) = Some W_7f73c.
Proof. vm_refl. Qed.
Lemma D_7f73c : decode_any W_7f73c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f740 : bv 32 := 0x7b813a83.
Lemma F_7f740 : fetch_word AsanUbsan.M.loaded_segments (0x7f788 : word) = Some W_7f740.
Proof. vm_refl. Qed.
Lemma D_7f740 : decode_any W_7f740 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f744 : bv 32 := 0x7f010113.
Lemma F_7f744 : fetch_word AsanUbsan.M.loaded_segments (0x7f78c : word) = Some W_7f744.
Proof. vm_refl. Qed.
Lemma D_7f744 : decode_any W_7f744 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f748 : bv 32 := 0x00008067.
Lemma F_7f748 : fetch_word AsanUbsan.M.loaded_segments (0x7f790 : word) = Some W_7f748.
Proof. vm_refl. Qed.
Lemma D_7f748 : decode_any W_7f748 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f820 : bv 32 := 0x02061e63.
Lemma F_7f820 : fetch_word AsanUbsan.M.loaded_segments (0x7f868 : word) = Some W_7f820.
Proof. vm_refl. Qed.
Lemma D_7f820 : decode_any W_7f820 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f824 : bv 32 := 0xef5ff06f.
Lemma F_7f824 : fetch_word AsanUbsan.M.loaded_segments (0x7f86c : word) = Some W_7f824.
Proof. vm_refl. Qed.
Lemma D_7f824 : decode_any W_7f824 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f828 : bv 32 := 0x00070803.
Lemma F_7f828 : fetch_word AsanUbsan.M.loaded_segments (0x7f870 : word) = Some W_7f828.
Proof. vm_refl. Qed.
Lemma D_7f828 : decode_any W_7f828 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f82c : bv 32 := 0x0077f793.
Lemma F_7f82c : fetch_word AsanUbsan.M.loaded_segments (0x7f874 : word) = Some W_7f82c.
Proof. vm_refl. Qed.
Lemma D_7f82c : decode_any W_7f82c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f830 : bv 32 := 0x010038b3.
Lemma F_7f830 : fetch_word AsanUbsan.M.loaded_segments (0x7f878 : word) = Some W_7f830.
Proof. vm_refl. Qed.
Lemma D_7f830 : decode_any W_7f830 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f834 : bv 32 := 0x0107a7b3.
Lemma F_7f834 : fetch_word AsanUbsan.M.loaded_segments (0x7f87c : word) = Some W_7f834.
Proof. vm_refl. Qed.
Lemma D_7f834 : decode_any W_7f834 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f838 : bv 32 := 0x0017c793.
Lemma F_7f838 : fetch_word AsanUbsan.M.loaded_segments (0x7f880 : word) = Some W_7f838.
Proof. vm_refl. Qed.
Lemma D_7f838 : decode_any W_7f838 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f83c : bv 32 := 0x00f8f7b3.
Lemma F_7f83c : fetch_word AsanUbsan.M.loaded_segments (0x7f884 : word) = Some W_7f83c.
Proof. vm_refl. Qed.
Lemma D_7f83c : decode_any W_7f83c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f840 : bv 32 := 0x00e6fa63.
Lemma F_7f840 : fetch_word AsanUbsan.M.loaded_segments (0x7f888 : word) = Some W_7f840.
Proof. vm_refl. Qed.
Lemma D_7f840 : decode_any W_7f840 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f844 : bv 32 := 0x0006c803.
Lemma F_7f844 : fetch_word AsanUbsan.M.loaded_segments (0x7f88c : word) = Some W_7f844.
Proof. vm_refl. Qed.
Lemma D_7f844 : decode_any W_7f844 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f848 : bv 32 := 0x00168693.
Lemma F_7f848 : fetch_word AsanUbsan.M.loaded_segments (0x7f890 : word) = Some W_7f848.
Proof. vm_refl. Qed.
Lemma D_7f848 : decode_any W_7f848 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f84c : bv 32 := 0x00f867b3.
Lemma F_7f84c : fetch_word AsanUbsan.M.loaded_segments (0x7f894 : word) = Some W_7f84c.
Proof. vm_refl. Qed.
Lemma D_7f84c : decode_any W_7f84c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f850 : bv 32 := 0xfee69ae3.
Lemma F_7f850 : fetch_word AsanUbsan.M.loaded_segments (0x7f898 : word) = Some W_7f850.
Proof. vm_refl. Qed.
Lemma D_7f850 : decode_any W_7f850 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f854 : bv 32 := 0x0ff7f693.
Lemma F_7f854 : fetch_word AsanUbsan.M.loaded_segments (0x7f89c : word) = Some W_7f854.
Proof. vm_refl. Qed.
Lemma D_7f854 : decode_any W_7f854 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f858 : bv 32 := 0xec0680e3.
Lemma F_7f858 : fetch_word AsanUbsan.M.loaded_segments (0x7f8a0 : word) = Some W_7f858.
Proof. vm_refl. Qed.
Lemma D_7f858 : decode_any W_7f858 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f85c : bv 32 := 0x00050493.
Lemma F_7f85c : fetch_word AsanUbsan.M.loaded_segments (0x7f8a4 : word) = Some W_7f85c.
Proof. vm_refl. Qed.
Lemma D_7f85c : decode_any W_7f85c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f860 : bv 32 := 0x00058a93.
Lemma F_7f860 : fetch_word AsanUbsan.M.loaded_segments (0x7f8a8 : word) = Some W_7f860.
Proof. vm_refl. Qed.
Lemma D_7f860 : decode_any W_7f860 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f864 : bv 32 := 0x00060593.
Lemma F_7f864 : fetch_word AsanUbsan.M.loaded_segments (0x7f8ac : word) = Some W_7f864.
Proof. vm_refl. Qed.
Lemma D_7f864 : decode_any W_7f864 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f868 : bv 32 := 0x00060913.
Lemma F_7f868 : fetch_word AsanUbsan.M.loaded_segments (0x7f8b0 : word) = Some W_7f868.
Proof. vm_refl. Qed.
Lemma D_7f868 : decode_any W_7f868 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f86c : bv 32 := 0x1ac030ef.
Lemma F_7f86c : fetch_word AsanUbsan.M.loaded_segments (0x7f8b4 : word) = Some W_7f86c.
Proof. vm_refl. Qed.
Lemma D_7f86c : decode_any W_7f86c = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f870 : bv 32 := 0x000a8593.
Lemma F_7f870 : fetch_word AsanUbsan.M.loaded_segments (0x7f8b8 : word) = Some W_7f870.
Proof. vm_refl. Qed.
Lemma D_7f870 : decode_any W_7f870 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f874 : bv 32 := 0x00090613.
Lemma F_7f874 : fetch_word AsanUbsan.M.loaded_segments (0x7f8bc : word) = Some W_7f874.
Proof. vm_refl. Qed.
Lemma D_7f874 : decode_any W_7f874 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f878 : bv 32 := 0x00050993.
Lemma F_7f878 : fetch_word AsanUbsan.M.loaded_segments (0x7f8c0 : word) = Some W_7f878.
Proof. vm_refl. Qed.
Lemma D_7f878 : decode_any W_7f878 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f87c : bv 32 := 0x00048513.
Lemma F_7f87c : fetch_word AsanUbsan.M.loaded_segments (0x7f8c4 : word) = Some W_7f87c.
Proof. vm_refl. Qed.
Lemma D_7f87c : decode_any W_7f87c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f880 : bv 32 := 0xe8098ce3.
Lemma F_7f880 : fetch_word AsanUbsan.M.loaded_segments (0x7f8c8 : word) = Some W_7f880.
Proof. vm_refl. Qed.
Lemma D_7f880 : decode_any W_7f880 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c8 : bv 32 := 0x81010113.
Lemma F_7f8c8 : fetch_word AsanUbsan.M.loaded_segments (0x7f910 : word) = Some W_7f8c8.
Proof. vm_refl. Qed.
Lemma D_7f8c8 : decode_any W_7f8c8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8cc : bv 32 := 0x7e113423.
Lemma F_7f8cc : fetch_word AsanUbsan.M.loaded_segments (0x7f914 : word) = Some W_7f8cc.
Proof. vm_refl. Qed.
Lemma D_7f8cc : decode_any W_7f8cc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d0 : bv 32 := 0x7e813023.
Lemma F_7f8d0 : fetch_word AsanUbsan.M.loaded_segments (0x7f918 : word) = Some W_7f8d0.
Proof. vm_refl. Qed.
Lemma D_7f8d0 : decode_any W_7f8d0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d4 : bv 32 := 0x7c913c23.
Lemma F_7f8d4 : fetch_word AsanUbsan.M.loaded_segments (0x7f91c : word) = Some W_7f8d4.
Proof. vm_refl. Qed.
Lemma D_7f8d4 : decode_any W_7f8d4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d8 : bv 32 := 0x7d213823.
Lemma F_7f8d8 : fetch_word AsanUbsan.M.loaded_segments (0x7f920 : word) = Some W_7f8d8.
Proof. vm_refl. Qed.
Lemma D_7f8d8 : decode_any W_7f8d8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8dc : bv 32 := 0x7d313423.
Lemma F_7f8dc : fetch_word AsanUbsan.M.loaded_segments (0x7f924 : word) = Some W_7f8dc.
Proof. vm_refl. Qed.
Lemma D_7f8dc : decode_any W_7f8dc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e0 : bv 32 := 0x7d413023.
Lemma F_7f8e0 : fetch_word AsanUbsan.M.loaded_segments (0x7f928 : word) = Some W_7f8e0.
Proof. vm_refl. Qed.
Lemma D_7f8e0 : decode_any W_7f8e0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e4 : bv 32 := 0x7b513c23.
Lemma F_7f8e4 : fetch_word AsanUbsan.M.loaded_segments (0x7f92c : word) = Some W_7f8e4.
Proof. vm_refl. Qed.
Lemma D_7f8e4 : decode_any W_7f8e4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e8 : bv 32 := 0x7b613823.
Lemma F_7f8e8 : fetch_word AsanUbsan.M.loaded_segments (0x7f930 : word) = Some W_7f8e8.
Proof. vm_refl. Qed.
Lemma D_7f8e8 : decode_any W_7f8e8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8ec : bv 32 := 0x7f010413.
Lemma F_7f8ec : fetch_word AsanUbsan.M.loaded_segments (0x7f934 : word) = Some W_7f8ec.
Proof. vm_refl. Qed.
Lemma D_7f8ec : decode_any W_7f8ec = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f0 : bv 32 := 0xf9010113.
Lemma F_7f8f0 : fetch_word AsanUbsan.M.loaded_segments (0x7f938 : word) = Some W_7f8f0.
Proof. vm_refl. Qed.
Lemma D_7f8f0 : decode_any W_7f8f0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f4 : bv 32 := 0x000d5697.
Lemma F_7f8f4 : fetch_word AsanUbsan.M.loaded_segments (0x7f93c : word) = Some W_7f8f4.
Proof. vm_refl. Qed.
Lemma D_7f8f4 : decode_any W_7f8f4 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f8 : bv 32 := 0x72c6b683.
Lemma F_7f8f8 : fetch_word AsanUbsan.M.loaded_segments (0x7f940 : word) = Some W_7f8f8.
Proof. vm_refl. Qed.
Lemma D_7f8f8 : decode_any W_7f8f8 = Some (Load SZ8 true 13 13 1836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8fc : bv 32 := 0x0006c683.
Lemma F_7f8fc : fetch_word AsanUbsan.M.loaded_segments (0x7f944 : word) = Some W_7f8fc.
Proof. vm_refl. Qed.
Lemma D_7f8fc : decode_any W_7f8fc = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f900 : bv 32 := 0x0a068463.
Lemma F_7f900 : fetch_word AsanUbsan.M.loaded_segments (0x7f948 : word) = Some W_7f900.
Proof. vm_refl. Qed.
Lemma D_7f900 : decode_any W_7f900 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f904 : bv 32 := 0xfff5c693.
Lemma F_7f904 : fetch_word AsanUbsan.M.loaded_segments (0x7f94c : word) = Some W_7f904.
Proof. vm_refl. Qed.
Lemma D_7f904 : decode_any W_7f904 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f908 : bv 32 := 0x80040a13.
Lemma F_7f908 : fetch_word AsanUbsan.M.loaded_segments (0x7f950 : word) = Some W_7f908.
Proof. vm_refl. Qed.
Lemma D_7f908 : decode_any W_7f908 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f90c : bv 32 := 0xfa8a0a13.
Lemma F_7f90c : fetch_word AsanUbsan.M.loaded_segments (0x7f954 : word) = Some W_7f90c.
Proof. vm_refl. Qed.
Lemma D_7f90c : decode_any W_7f90c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f910 : bv 32 := 0x0cc6e463.
Lemma F_7f910 : fetch_word AsanUbsan.M.loaded_segments (0x7f958 : word) = Some W_7f910.
Proof. vm_refl. Qed.
Lemma D_7f910 : decode_any W_7f910 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f914 : bv 32 := 0xfbf60993.
Lemma F_7f914 : fetch_word AsanUbsan.M.loaded_segments (0x7f95c : word) = Some W_7f914.
Proof. vm_refl. Qed.
Lemma D_7f914 : decode_any W_7f914 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f918 : bv 32 := 0xfbf00693.
Lemma F_7f918 : fetch_word AsanUbsan.M.loaded_segments (0x7f960 : word) = Some W_7f918.
Proof. vm_refl. Qed.
Lemma D_7f918 : decode_any W_7f918 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f91c : bv 32 := 0x1536f263.
Lemma F_7f91c : fetch_word AsanUbsan.M.loaded_segments (0x7f964 : word) = Some W_7f91c.
Proof. vm_refl. Qed.
Lemma D_7f91c : decode_any W_7f91c = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f920 : bv 32 := 0x000d5697.
Lemma F_7f920 : fetch_word AsanUbsan.M.loaded_segments (0x7f968 : word) = Some W_7f920.
Proof. vm_refl. Qed.
Lemma D_7f920 : decode_any W_7f920 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f924 : bv 32 := 0xb986b683.
Lemma F_7f924 : fetch_word AsanUbsan.M.loaded_segments (0x7f96c : word) = Some W_7f924.
Proof. vm_refl. Qed.
Lemma D_7f924 : decode_any W_7f924 = Some (Load SZ8 true 13 13 2968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f928 : bv 32 := 0x00c587b3.
Lemma F_7f928 : fetch_word AsanUbsan.M.loaded_segments (0x7f970 : word) = Some W_7f928.
Proof. vm_refl. Qed.
Lemma D_7f928 : decode_any W_7f928 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f92c : bv 32 := 0x0006b703.
Lemma F_7f92c : fetch_word AsanUbsan.M.loaded_segments (0x7f974 : word) = Some W_7f92c.
Proof. vm_refl. Qed.
Lemma D_7f92c : decode_any W_7f92c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f930 : bv 32 := 0x0035d693.
Lemma F_7f930 : fetch_word AsanUbsan.M.loaded_segments (0x7f978 : word) = Some W_7f930.
Proof. vm_refl. Qed.
Lemma D_7f930 : decode_any W_7f930 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f934 : bv 32 := 0xfff78793.
Lemma F_7f934 : fetch_word AsanUbsan.M.loaded_segments (0x7f97c : word) = Some W_7f934.
Proof. vm_refl. Qed.
Lemma D_7f934 : decode_any W_7f934 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f938 : bv 32 := 0x0037d813.
Lemma F_7f938 : fetch_word AsanUbsan.M.loaded_segments (0x7f980 : word) = Some W_7f938.
Proof. vm_refl. Qed.
Lemma D_7f938 : decode_any W_7f938 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f93c : bv 32 := 0x00d706b3.
Lemma F_7f93c : fetch_word AsanUbsan.M.loaded_segments (0x7f984 : word) = Some W_7f93c.
Proof. vm_refl. Qed.
Lemma D_7f93c : decode_any W_7f93c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f940 : bv 32 := 0x01070733.
Lemma F_7f940 : fetch_word AsanUbsan.M.loaded_segments (0x7f988 : word) = Some W_7f940.
Proof. vm_refl. Qed.
Lemma D_7f940 : decode_any W_7f940 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f944 : bv 32 := 0xff86f813.
Lemma F_7f944 : fetch_word AsanUbsan.M.loaded_segments (0x7f98c : word) = Some W_7f944.
Proof. vm_refl. Qed.
Lemma D_7f944 : decode_any W_7f944 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f948 : bv 32 := 0xff877893.
Lemma F_7f948 : fetch_word AsanUbsan.M.loaded_segments (0x7f990 : word) = Some W_7f948.
Proof. vm_refl. Qed.
Lemma D_7f948 : decode_any W_7f948 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f94c : bv 32 := 0x00083803.
Lemma F_7f94c : fetch_word AsanUbsan.M.loaded_segments (0x7f994 : word) = Some W_7f94c.
Proof. vm_refl. Qed.
Lemma D_7f94c : decode_any W_7f94c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f950 : bv 32 := 0x0008b883.
Lemma F_7f950 : fetch_word AsanUbsan.M.loaded_segments (0x7f998 : word) = Some W_7f950.
Proof. vm_refl. Qed.
Lemma D_7f950 : decode_any W_7f950 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f954 : bv 32 := 0x0108e833.
Lemma F_7f954 : fetch_word AsanUbsan.M.loaded_segments (0x7f99c : word) = Some W_7f954.
Proof. vm_refl. Qed.
Lemma D_7f954 : decode_any W_7f954 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f958 : bv 32 := 0x18081e63.
Lemma F_7f958 : fetch_word AsanUbsan.M.loaded_segments (0x7f9a0 : word) = Some W_7f958.
Proof. vm_refl. Qed.
Lemma D_7f958 : decode_any W_7f958 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f95c : bv 32 := 0xfff54693.
Lemma F_7f95c : fetch_word AsanUbsan.M.loaded_segments (0x7f9a4 : word) = Some W_7f95c.
Proof. vm_refl. Qed.
Lemma D_7f95c : decode_any W_7f95c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f960 : bv 32 := 0x10c6e463.
Lemma F_7f960 : fetch_word AsanUbsan.M.loaded_segments (0x7f9a8 : word) = Some W_7f960.
Proof. vm_refl. Qed.
Lemma D_7f960 : decode_any W_7f960 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f964 : bv 32 := 0xfbf00693.
Lemma F_7f964 : fetch_word AsanUbsan.M.loaded_segments (0x7f9ac : word) = Some W_7f964.
Proof. vm_refl. Qed.
Lemma D_7f964 : decode_any W_7f964 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f968 : bv 32 := 0x1936f263.
Lemma F_7f968 : fetch_word AsanUbsan.M.loaded_segments (0x7f9b0 : word) = Some W_7f968.
Proof. vm_refl. Qed.
Lemma D_7f968 : decode_any W_7f968 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f96c : bv 32 := 0x000d5697.
Lemma F_7f96c : fetch_word AsanUbsan.M.loaded_segments (0x7f9b4 : word) = Some W_7f96c.
Proof. vm_refl. Qed.
Lemma D_7f96c : decode_any W_7f96c = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f970 : bv 32 := 0xb4c6b683.
Lemma F_7f970 : fetch_word AsanUbsan.M.loaded_segments (0x7f9b8 : word) = Some W_7f970.
Proof. vm_refl. Qed.
Lemma D_7f970 : decode_any W_7f970 = Some (Load SZ8 true 13 13 2892, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f974 : bv 32 := 0x00c507b3.
Lemma F_7f974 : fetch_word AsanUbsan.M.loaded_segments (0x7f9bc : word) = Some W_7f974.
Proof. vm_refl. Qed.
Lemma D_7f974 : decode_any W_7f974 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f978 : bv 32 := 0x0006b703.
Lemma F_7f978 : fetch_word AsanUbsan.M.loaded_segments (0x7f9c0 : word) = Some W_7f978.
Proof. vm_refl. Qed.
Lemma D_7f978 : decode_any W_7f978 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f97c : bv 32 := 0x00355693.
Lemma F_7f97c : fetch_word AsanUbsan.M.loaded_segments (0x7f9c4 : word) = Some W_7f97c.
Proof. vm_refl. Qed.
Lemma D_7f97c : decode_any W_7f97c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f980 : bv 32 := 0xfff78793.
Lemma F_7f980 : fetch_word AsanUbsan.M.loaded_segments (0x7f9c8 : word) = Some W_7f980.
Proof. vm_refl. Qed.
Lemma D_7f980 : decode_any W_7f980 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f984 : bv 32 := 0x0037d813.
Lemma F_7f984 : fetch_word AsanUbsan.M.loaded_segments (0x7f9cc : word) = Some W_7f984.
Proof. vm_refl. Qed.
Lemma D_7f984 : decode_any W_7f984 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f988 : bv 32 := 0x00d706b3.
Lemma F_7f988 : fetch_word AsanUbsan.M.loaded_segments (0x7f9d0 : word) = Some W_7f988.
Proof. vm_refl. Qed.
Lemma D_7f988 : decode_any W_7f988 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f98c : bv 32 := 0x01070733.
Lemma F_7f98c : fetch_word AsanUbsan.M.loaded_segments (0x7f9d4 : word) = Some W_7f98c.
Proof. vm_refl. Qed.
Lemma D_7f98c : decode_any W_7f98c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f990 : bv 32 := 0xff86f813.
Lemma F_7f990 : fetch_word AsanUbsan.M.loaded_segments (0x7f9d8 : word) = Some W_7f990.
Proof. vm_refl. Qed.
Lemma D_7f990 : decode_any W_7f990 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f994 : bv 32 := 0xff877893.
Lemma F_7f994 : fetch_word AsanUbsan.M.loaded_segments (0x7f9dc : word) = Some W_7f994.
Proof. vm_refl. Qed.
Lemma D_7f994 : decode_any W_7f994 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f998 : bv 32 := 0x00083803.
Lemma F_7f998 : fetch_word AsanUbsan.M.loaded_segments (0x7f9e0 : word) = Some W_7f998.
Proof. vm_refl. Qed.
Lemma D_7f998 : decode_any W_7f998 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f99c : bv 32 := 0x0008b883.
Lemma F_7f99c : fetch_word AsanUbsan.M.loaded_segments (0x7f9e4 : word) = Some W_7f99c.
Proof. vm_refl. Qed.
Lemma D_7f99c : decode_any W_7f99c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a0 : bv 32 := 0x0108e833.
Lemma F_7f9a0 : fetch_word AsanUbsan.M.loaded_segments (0x7f9e8 : word) = Some W_7f9a0.
Proof. vm_refl. Qed.
Lemma D_7f9a0 : decode_any W_7f9a0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a4 : bv 32 := 0x1e081a63.
Lemma F_7f9a4 : fetch_word AsanUbsan.M.loaded_segments (0x7f9ec : word) = Some W_7f9a4.
Proof. vm_refl. Qed.
Lemma D_7f9a4 : decode_any W_7f9a4 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a8 : bv 32 := 0x7b9120ef.
Lemma F_7f9a8 : fetch_word AsanUbsan.M.loaded_segments (0x7f9f0 : word) = Some W_7f9a8.
Proof. vm_refl. Qed.
Lemma D_7f9a8 : decode_any W_7f9a8 = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9ac : bv 32 := 0x07010113.
Lemma F_7f9ac : fetch_word AsanUbsan.M.loaded_segments (0x7f9f4 : word) = Some W_7f9ac.
Proof. vm_refl. Qed.
Lemma D_7f9ac : decode_any W_7f9ac = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b0 : bv 32 := 0x7e813083.
Lemma F_7f9b0 : fetch_word AsanUbsan.M.loaded_segments (0x7f9f8 : word) = Some W_7f9b0.
Proof. vm_refl. Qed.
Lemma D_7f9b0 : decode_any W_7f9b0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b4 : bv 32 := 0x7e013403.
Lemma F_7f9b4 : fetch_word AsanUbsan.M.loaded_segments (0x7f9fc : word) = Some W_7f9b4.
Proof. vm_refl. Qed.
Lemma D_7f9b4 : decode_any W_7f9b4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b8 : bv 32 := 0x7d813483.
Lemma F_7f9b8 : fetch_word AsanUbsan.M.loaded_segments (0x7fa00 : word) = Some W_7f9b8.
Proof. vm_refl. Qed.
Lemma D_7f9b8 : decode_any W_7f9b8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9bc : bv 32 := 0x7d013903.
Lemma F_7f9bc : fetch_word AsanUbsan.M.loaded_segments (0x7fa04 : word) = Some W_7f9bc.
Proof. vm_refl. Qed.
Lemma D_7f9bc : decode_any W_7f9bc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9c0 : bv 32 := 0x7c813983.
Lemma F_7f9c0 : fetch_word AsanUbsan.M.loaded_segments (0x7fa08 : word) = Some W_7f9c0.
Proof. vm_refl. Qed.
Lemma D_7f9c0 : decode_any W_7f9c0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9c4 : bv 32 := 0x7c013a03.
Lemma F_7f9c4 : fetch_word AsanUbsan.M.loaded_segments (0x7fa0c : word) = Some W_7f9c4.
Proof. vm_refl. Qed.
Lemma D_7f9c4 : decode_any W_7f9c4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9c8 : bv 32 := 0x7b813a83.
Lemma F_7f9c8 : fetch_word AsanUbsan.M.loaded_segments (0x7fa10 : word) = Some W_7f9c8.
Proof. vm_refl. Qed.
Lemma D_7f9c8 : decode_any W_7f9c8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9cc : bv 32 := 0x7b013b03.
Lemma F_7f9cc : fetch_word AsanUbsan.M.loaded_segments (0x7fa14 : word) = Some W_7f9cc.
Proof. vm_refl. Qed.
Lemma D_7f9cc : decode_any W_7f9cc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9d0 : bv 32 := 0x7f010113.
Lemma F_7f9d0 : fetch_word AsanUbsan.M.loaded_segments (0x7fa18 : word) = Some W_7f9d0.
Proof. vm_refl. Qed.
Lemma D_7f9d0 : decode_any W_7f9d0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9d4 : bv 32 := 0x00008067.
Lemma F_7f9d4 : fetch_word AsanUbsan.M.loaded_segments (0x7fa1c : word) = Some W_7f9d4.
Proof. vm_refl. Qed.
Lemma D_7f9d4 : decode_any W_7f9d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa60 : bv 32 := 0x0c061463.
Lemma F_7fa60 : fetch_word AsanUbsan.M.loaded_segments (0x7faa8 : word) = Some W_7fa60.
Proof. vm_refl. Qed.
Lemma D_7fa60 : decode_any W_7fa60 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa64 : bv 32 := 0xef9ff06f.
Lemma F_7fa64 : fetch_word AsanUbsan.M.loaded_segments (0x7faac : word) = Some W_7fa64.
Proof. vm_refl. Qed.
Lemma D_7fa64 : decode_any W_7fa64 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faec : bv 32 := 0x0e061063.
Lemma F_7faec : fetch_word AsanUbsan.M.loaded_segments (0x7fb34 : word) = Some W_7faec.
Proof. vm_refl. Qed.
Lemma D_7faec : decode_any W_7faec = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf0 : bv 32 := 0xeb9ff06f.
Lemma F_7faf0 : fetch_word AsanUbsan.M.loaded_segments (0x7fb38 : word) = Some W_7faf0.
Proof. vm_refl. Qed.
Lemma D_7faf0 : decode_any W_7faf0 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf4 : bv 32 := 0x00070803.
Lemma F_7faf4 : fetch_word AsanUbsan.M.loaded_segments (0x7fb3c : word) = Some W_7faf4.
Proof. vm_refl. Qed.
Lemma D_7faf4 : decode_any W_7faf4 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf8 : bv 32 := 0x0077f793.
Lemma F_7faf8 : fetch_word AsanUbsan.M.loaded_segments (0x7fb40 : word) = Some W_7faf8.
Proof. vm_refl. Qed.
Lemma D_7faf8 : decode_any W_7faf8 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fafc : bv 32 := 0x010038b3.
Lemma F_7fafc : fetch_word AsanUbsan.M.loaded_segments (0x7fb44 : word) = Some W_7fafc.
Proof. vm_refl. Qed.
Lemma D_7fafc : decode_any W_7fafc = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb00 : bv 32 := 0x0107a7b3.
Lemma F_7fb00 : fetch_word AsanUbsan.M.loaded_segments (0x7fb48 : word) = Some W_7fb00.
Proof. vm_refl. Qed.
Lemma D_7fb00 : decode_any W_7fb00 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb04 : bv 32 := 0x0017c793.
Lemma F_7fb04 : fetch_word AsanUbsan.M.loaded_segments (0x7fb4c : word) = Some W_7fb04.
Proof. vm_refl. Qed.
Lemma D_7fb04 : decode_any W_7fb04 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb08 : bv 32 := 0x00f8f7b3.
Lemma F_7fb08 : fetch_word AsanUbsan.M.loaded_segments (0x7fb50 : word) = Some W_7fb08.
Proof. vm_refl. Qed.
Lemma D_7fb08 : decode_any W_7fb08 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb0c : bv 32 := 0x00e6fa63.
Lemma F_7fb0c : fetch_word AsanUbsan.M.loaded_segments (0x7fb54 : word) = Some W_7fb0c.
Proof. vm_refl. Qed.
Lemma D_7fb0c : decode_any W_7fb0c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb10 : bv 32 := 0x0006c803.
Lemma F_7fb10 : fetch_word AsanUbsan.M.loaded_segments (0x7fb58 : word) = Some W_7fb10.
Proof. vm_refl. Qed.
Lemma D_7fb10 : decode_any W_7fb10 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb14 : bv 32 := 0x00168693.
Lemma F_7fb14 : fetch_word AsanUbsan.M.loaded_segments (0x7fb5c : word) = Some W_7fb14.
Proof. vm_refl. Qed.
Lemma D_7fb14 : decode_any W_7fb14 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb18 : bv 32 := 0x00f867b3.
Lemma F_7fb18 : fetch_word AsanUbsan.M.loaded_segments (0x7fb60 : word) = Some W_7fb18.
Proof. vm_refl. Qed.
Lemma D_7fb18 : decode_any W_7fb18 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb1c : bv 32 := 0xfee69ae3.
Lemma F_7fb1c : fetch_word AsanUbsan.M.loaded_segments (0x7fb64 : word) = Some W_7fb1c.
Proof. vm_refl. Qed.
Lemma D_7fb1c : decode_any W_7fb1c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb20 : bv 32 := 0x0ff7f693.
Lemma F_7fb20 : fetch_word AsanUbsan.M.loaded_segments (0x7fb68 : word) = Some W_7fb20.
Proof. vm_refl. Qed.
Lemma D_7fb20 : decode_any W_7fb20 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb24 : bv 32 := 0xe2068ce3.
Lemma F_7fb24 : fetch_word AsanUbsan.M.loaded_segments (0x7fb6c : word) = Some W_7fb24.
Proof. vm_refl. Qed.
Lemma D_7fb24 : decode_any W_7fb24 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb28 : bv 32 := 0x00050a93.
Lemma F_7fb28 : fetch_word AsanUbsan.M.loaded_segments (0x7fb70 : word) = Some W_7fb28.
Proof. vm_refl. Qed.
Lemma D_7fb28 : decode_any W_7fb28 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb2c : bv 32 := 0x00058513.
Lemma F_7fb2c : fetch_word AsanUbsan.M.loaded_segments (0x7fb74 : word) = Some W_7fb2c.
Proof. vm_refl. Qed.
Lemma D_7fb2c : decode_any W_7fb2c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb30 : bv 32 := 0x00058b13.
Lemma F_7fb30 : fetch_word AsanUbsan.M.loaded_segments (0x7fb78 : word) = Some W_7fb30.
Proof. vm_refl. Qed.
Lemma D_7fb30 : decode_any W_7fb30 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb34 : bv 32 := 0x00060593.
Lemma F_7fb34 : fetch_word AsanUbsan.M.loaded_segments (0x7fb7c : word) = Some W_7fb34.
Proof. vm_refl. Qed.
Lemma D_7fb34 : decode_any W_7fb34 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb38 : bv 32 := 0x00060493.
Lemma F_7fb38 : fetch_word AsanUbsan.M.loaded_segments (0x7fb80 : word) = Some W_7fb38.
Proof. vm_refl. Qed.
Lemma D_7fb38 : decode_any W_7fb38 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb3c : bv 32 := 0x6dd020ef.
Lemma F_7fb3c : fetch_word AsanUbsan.M.loaded_segments (0x7fb84 : word) = Some W_7fb3c.
Proof. vm_refl. Qed.
Lemma D_7fb3c : decode_any W_7fb3c = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb40 : bv 32 := 0x000b0593.
Lemma F_7fb40 : fetch_word AsanUbsan.M.loaded_segments (0x7fb88 : word) = Some W_7fb40.
Proof. vm_refl. Qed.
Lemma D_7fb40 : decode_any W_7fb40 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb44 : bv 32 := 0x00048613.
Lemma F_7fb44 : fetch_word AsanUbsan.M.loaded_segments (0x7fb8c : word) = Some W_7fb44.
Proof. vm_refl. Qed.
Lemma D_7fb44 : decode_any W_7fb44 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb48 : bv 32 := 0x00050913.
Lemma F_7fb48 : fetch_word AsanUbsan.M.loaded_segments (0x7fb90 : word) = Some W_7fb48.
Proof. vm_refl. Qed.
Lemma D_7fb48 : decode_any W_7fb48 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb4c : bv 32 := 0x000a8513.
Lemma F_7fb4c : fetch_word AsanUbsan.M.loaded_segments (0x7fb94 : word) = Some W_7fb4c.
Proof. vm_refl. Qed.
Lemma D_7fb4c : decode_any W_7fb4c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb50 : bv 32 := 0xe00906e3.
Lemma F_7fb50 : fetch_word AsanUbsan.M.loaded_segments (0x7fb98 : word) = Some W_7fb50.
Proof. vm_refl. Qed.
Lemma D_7fb50 : decode_any W_7fb50 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb98 : bv 32 := 0x00070803.
Lemma F_7fb98 : fetch_word AsanUbsan.M.loaded_segments (0x7fbe0 : word) = Some W_7fb98.
Proof. vm_refl. Qed.
Lemma D_7fb98 : decode_any W_7fb98 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb9c : bv 32 := 0x0077f793.
Lemma F_7fb9c : fetch_word AsanUbsan.M.loaded_segments (0x7fbe4 : word) = Some W_7fb9c.
Proof. vm_refl. Qed.
Lemma D_7fb9c : decode_any W_7fb9c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba0 : bv 32 := 0x010038b3.
Lemma F_7fba0 : fetch_word AsanUbsan.M.loaded_segments (0x7fbe8 : word) = Some W_7fba0.
Proof. vm_refl. Qed.
Lemma D_7fba0 : decode_any W_7fba0 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba4 : bv 32 := 0x0107a7b3.
Lemma F_7fba4 : fetch_word AsanUbsan.M.loaded_segments (0x7fbec : word) = Some W_7fba4.
Proof. vm_refl. Qed.
Lemma D_7fba4 : decode_any W_7fba4 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba8 : bv 32 := 0x0017c793.
Lemma F_7fba8 : fetch_word AsanUbsan.M.loaded_segments (0x7fbf0 : word) = Some W_7fba8.
Proof. vm_refl. Qed.
Lemma D_7fba8 : decode_any W_7fba8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbac : bv 32 := 0x00f8f7b3.
Lemma F_7fbac : fetch_word AsanUbsan.M.loaded_segments (0x7fbf4 : word) = Some W_7fbac.
Proof. vm_refl. Qed.
Lemma D_7fbac : decode_any W_7fbac = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb0 : bv 32 := 0x00e6fa63.
Lemma F_7fbb0 : fetch_word AsanUbsan.M.loaded_segments (0x7fbf8 : word) = Some W_7fbb0.
Proof. vm_refl. Qed.
Lemma D_7fbb0 : decode_any W_7fbb0 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb4 : bv 32 := 0x0006c803.
Lemma F_7fbb4 : fetch_word AsanUbsan.M.loaded_segments (0x7fbfc : word) = Some W_7fbb4.
Proof. vm_refl. Qed.
Lemma D_7fbb4 : decode_any W_7fbb4 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb8 : bv 32 := 0x00168693.
Lemma F_7fbb8 : fetch_word AsanUbsan.M.loaded_segments (0x7fc00 : word) = Some W_7fbb8.
Proof. vm_refl. Qed.
Lemma D_7fbb8 : decode_any W_7fbb8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbbc : bv 32 := 0x00f867b3.
Lemma F_7fbbc : fetch_word AsanUbsan.M.loaded_segments (0x7fc04 : word) = Some W_7fbbc.
Proof. vm_refl. Qed.
Lemma D_7fbbc : decode_any W_7fbbc = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc0 : bv 32 := 0xfee69ae3.
Lemma F_7fbc0 : fetch_word AsanUbsan.M.loaded_segments (0x7fc08 : word) = Some W_7fbc0.
Proof. vm_refl. Qed.
Lemma D_7fbc0 : decode_any W_7fbc0 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc4 : bv 32 := 0x0ff7f693.
Lemma F_7fbc4 : fetch_word AsanUbsan.M.loaded_segments (0x7fc0c : word) = Some W_7fbc4.
Proof. vm_refl. Qed.
Lemma D_7fbc4 : decode_any W_7fbc4 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc8 : bv 32 := 0xde0680e3.
Lemma F_7fbc8 : fetch_word AsanUbsan.M.loaded_segments (0x7fc10 : word) = Some W_7fbc8.
Proof. vm_refl. Qed.
Lemma D_7fbc8 : decode_any W_7fbc8 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbcc : bv 32 := 0x00050493.
Lemma F_7fbcc : fetch_word AsanUbsan.M.loaded_segments (0x7fc14 : word) = Some W_7fbcc.
Proof. vm_refl. Qed.
Lemma D_7fbcc : decode_any W_7fbcc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd0 : bv 32 := 0x00058a93.
Lemma F_7fbd0 : fetch_word AsanUbsan.M.loaded_segments (0x7fc18 : word) = Some W_7fbd0.
Proof. vm_refl. Qed.
Lemma D_7fbd0 : decode_any W_7fbd0 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd4 : bv 32 := 0x00060593.
Lemma F_7fbd4 : fetch_word AsanUbsan.M.loaded_segments (0x7fc1c : word) = Some W_7fbd4.
Proof. vm_refl. Qed.
Lemma D_7fbd4 : decode_any W_7fbd4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd8 : bv 32 := 0x00060913.
Lemma F_7fbd8 : fetch_word AsanUbsan.M.loaded_segments (0x7fc20 : word) = Some W_7fbd8.
Proof. vm_refl. Qed.
Lemma D_7fbd8 : decode_any W_7fbd8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbdc : bv 32 := 0x63d020ef.
Lemma F_7fbdc : fetch_word AsanUbsan.M.loaded_segments (0x7fc24 : word) = Some W_7fbdc.
Proof. vm_refl. Qed.
Lemma D_7fbdc : decode_any W_7fbdc = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe0 : bv 32 := 0x000a8593.
Lemma F_7fbe0 : fetch_word AsanUbsan.M.loaded_segments (0x7fc28 : word) = Some W_7fbe0.
Proof. vm_refl. Qed.
Lemma D_7fbe0 : decode_any W_7fbe0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe4 : bv 32 := 0x00090613.
Lemma F_7fbe4 : fetch_word AsanUbsan.M.loaded_segments (0x7fc2c : word) = Some W_7fbe4.
Proof. vm_refl. Qed.
Lemma D_7fbe4 : decode_any W_7fbe4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe8 : bv 32 := 0x00050993.
Lemma F_7fbe8 : fetch_word AsanUbsan.M.loaded_segments (0x7fc30 : word) = Some W_7fbe8.
Proof. vm_refl. Qed.
Lemma D_7fbe8 : decode_any W_7fbe8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbec : bv 32 := 0x00048513.
Lemma F_7fbec : fetch_word AsanUbsan.M.loaded_segments (0x7fc34 : word) = Some W_7fbec.
Proof. vm_refl. Qed.
Lemma D_7fbec : decode_any W_7fbec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf0 : bv 32 := 0xda098ce3.
Lemma F_7fbf0 : fetch_word AsanUbsan.M.loaded_segments (0x7fc38 : word) = Some W_7fbf0.
Proof. vm_refl. Qed.
Lemma D_7fbf0 : decode_any W_7fbf0 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff28 : bv 32 := 0x81010113.
Lemma F_7ff28 : fetch_word AsanUbsan.M.loaded_segments (0x7ff70 : word) = Some W_7ff28.
Proof. vm_refl. Qed.
Lemma D_7ff28 : decode_any W_7ff28 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff2c : bv 32 := 0x7e113423.
Lemma F_7ff2c : fetch_word AsanUbsan.M.loaded_segments (0x7ff74 : word) = Some W_7ff2c.
Proof. vm_refl. Qed.
Lemma D_7ff2c : decode_any W_7ff2c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff30 : bv 32 := 0x7e813023.
Lemma F_7ff30 : fetch_word AsanUbsan.M.loaded_segments (0x7ff78 : word) = Some W_7ff30.
Proof. vm_refl. Qed.
Lemma D_7ff30 : decode_any W_7ff30 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff34 : bv 32 := 0x7c913c23.
Lemma F_7ff34 : fetch_word AsanUbsan.M.loaded_segments (0x7ff7c : word) = Some W_7ff34.
Proof. vm_refl. Qed.
Lemma D_7ff34 : decode_any W_7ff34 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff38 : bv 32 := 0x7d213823.
Lemma F_7ff38 : fetch_word AsanUbsan.M.loaded_segments (0x7ff80 : word) = Some W_7ff38.
Proof. vm_refl. Qed.
Lemma D_7ff38 : decode_any W_7ff38 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff3c : bv 32 := 0x7d313423.
Lemma F_7ff3c : fetch_word AsanUbsan.M.loaded_segments (0x7ff84 : word) = Some W_7ff3c.
Proof. vm_refl. Qed.
Lemma D_7ff3c : decode_any W_7ff3c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff40 : bv 32 := 0x7d413023.
Lemma F_7ff40 : fetch_word AsanUbsan.M.loaded_segments (0x7ff88 : word) = Some W_7ff40.
Proof. vm_refl. Qed.
Lemma D_7ff40 : decode_any W_7ff40 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff44 : bv 32 := 0x7b513c23.
Lemma F_7ff44 : fetch_word AsanUbsan.M.loaded_segments (0x7ff8c : word) = Some W_7ff44.
Proof. vm_refl. Qed.
Lemma D_7ff44 : decode_any W_7ff44 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff48 : bv 32 := 0x7b613823.
Lemma F_7ff48 : fetch_word AsanUbsan.M.loaded_segments (0x7ff90 : word) = Some W_7ff48.
Proof. vm_refl. Qed.
Lemma D_7ff48 : decode_any W_7ff48 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff4c : bv 32 := 0x7b713423.
Lemma F_7ff4c : fetch_word AsanUbsan.M.loaded_segments (0x7ff94 : word) = Some W_7ff4c.
Proof. vm_refl. Qed.
Lemma D_7ff4c : decode_any W_7ff4c = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff50 : bv 32 := 0x7f010413.
Lemma F_7ff50 : fetch_word AsanUbsan.M.loaded_segments (0x7ff98 : word) = Some W_7ff50.
Proof. vm_refl. Qed.
Lemma D_7ff50 : decode_any W_7ff50 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff54 : bv 32 := 0xf9010113.
Lemma F_7ff54 : fetch_word AsanUbsan.M.loaded_segments (0x7ff9c : word) = Some W_7ff54.
Proof. vm_refl. Qed.
Lemma D_7ff54 : decode_any W_7ff54 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff58 : bv 32 := 0x000d5697.
Lemma F_7ff58 : fetch_word AsanUbsan.M.loaded_segments (0x7ffa0 : word) = Some W_7ff58.
Proof. vm_refl. Qed.
Lemma D_7ff58 : decode_any W_7ff58 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff5c : bv 32 := 0x0c86b683.
Lemma F_7ff5c : fetch_word AsanUbsan.M.loaded_segments (0x7ffa4 : word) = Some W_7ff5c.
Proof. vm_refl. Qed.
Lemma D_7ff5c : decode_any W_7ff5c = Some (Load SZ8 true 13 13 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff60 : bv 32 := 0x0006c683.
Lemma F_7ff60 : fetch_word AsanUbsan.M.loaded_segments (0x7ffa8 : word) = Some W_7ff60.
Proof. vm_refl. Qed.
Lemma D_7ff60 : decode_any W_7ff60 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff64 : bv 32 := 0x0a068463.
Lemma F_7ff64 : fetch_word AsanUbsan.M.loaded_segments (0x7ffac : word) = Some W_7ff64.
Proof. vm_refl. Qed.
Lemma D_7ff64 : decode_any W_7ff64 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff68 : bv 32 := 0xfff5c693.
Lemma F_7ff68 : fetch_word AsanUbsan.M.loaded_segments (0x7ffb0 : word) = Some W_7ff68.
Proof. vm_refl. Qed.
Lemma D_7ff68 : decode_any W_7ff68 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff6c : bv 32 := 0x80040a93.
Lemma F_7ff6c : fetch_word AsanUbsan.M.loaded_segments (0x7ffb4 : word) = Some W_7ff6c.
Proof. vm_refl. Qed.
Lemma D_7ff6c : decode_any W_7ff6c = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff70 : bv 32 := 0xfa0a8a93.
Lemma F_7ff70 : fetch_word AsanUbsan.M.loaded_segments (0x7ffb8 : word) = Some W_7ff70.
Proof. vm_refl. Qed.
Lemma D_7ff70 : decode_any W_7ff70 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff74 : bv 32 := 0x0cc6e663.
Lemma F_7ff74 : fetch_word AsanUbsan.M.loaded_segments (0x7ffbc : word) = Some W_7ff74.
Proof. vm_refl. Qed.
Lemma D_7ff74 : decode_any W_7ff74 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff78 : bv 32 := 0xfbf60a13.
Lemma F_7ff78 : fetch_word AsanUbsan.M.loaded_segments (0x7ffc0 : word) = Some W_7ff78.
Proof. vm_refl. Qed.
Lemma D_7ff78 : decode_any W_7ff78 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff7c : bv 32 := 0xfbf00693.
Lemma F_7ff7c : fetch_word AsanUbsan.M.loaded_segments (0x7ffc4 : word) = Some W_7ff7c.
Proof. vm_refl. Qed.
Lemma D_7ff7c : decode_any W_7ff7c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff80 : bv 32 := 0x1546f463.
Lemma F_7ff80 : fetch_word AsanUbsan.M.loaded_segments (0x7ffc8 : word) = Some W_7ff80.
Proof. vm_refl. Qed.
Lemma D_7ff80 : decode_any W_7ff80 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff84 : bv 32 := 0x000d4697.
Lemma F_7ff84 : fetch_word AsanUbsan.M.loaded_segments (0x7ffcc : word) = Some W_7ff84.
Proof. vm_refl. Qed.
Lemma D_7ff84 : decode_any W_7ff84 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff88 : bv 32 := 0x5346b683.
Lemma F_7ff88 : fetch_word AsanUbsan.M.loaded_segments (0x7ffd0 : word) = Some W_7ff88.
Proof. vm_refl. Qed.
Lemma D_7ff88 : decode_any W_7ff88 = Some (Load SZ8 true 13 13 1332, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff8c : bv 32 := 0x00c587b3.
Lemma F_7ff8c : fetch_word AsanUbsan.M.loaded_segments (0x7ffd4 : word) = Some W_7ff8c.
Proof. vm_refl. Qed.
Lemma D_7ff8c : decode_any W_7ff8c = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff90 : bv 32 := 0x0006b703.
Lemma F_7ff90 : fetch_word AsanUbsan.M.loaded_segments (0x7ffd8 : word) = Some W_7ff90.
Proof. vm_refl. Qed.
Lemma D_7ff90 : decode_any W_7ff90 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff94 : bv 32 := 0x0035d693.
Lemma F_7ff94 : fetch_word AsanUbsan.M.loaded_segments (0x7ffdc : word) = Some W_7ff94.
Proof. vm_refl. Qed.
Lemma D_7ff94 : decode_any W_7ff94 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff98 : bv 32 := 0xfff78793.
Lemma F_7ff98 : fetch_word AsanUbsan.M.loaded_segments (0x7ffe0 : word) = Some W_7ff98.
Proof. vm_refl. Qed.
Lemma D_7ff98 : decode_any W_7ff98 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff9c : bv 32 := 0x0037d813.
Lemma F_7ff9c : fetch_word AsanUbsan.M.loaded_segments (0x7ffe4 : word) = Some W_7ff9c.
Proof. vm_refl. Qed.
Lemma D_7ff9c : decode_any W_7ff9c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa0 : bv 32 := 0x00d706b3.
Lemma F_7ffa0 : fetch_word AsanUbsan.M.loaded_segments (0x7ffe8 : word) = Some W_7ffa0.
Proof. vm_refl. Qed.
Lemma D_7ffa0 : decode_any W_7ffa0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa4 : bv 32 := 0x01070733.
Lemma F_7ffa4 : fetch_word AsanUbsan.M.loaded_segments (0x7ffec : word) = Some W_7ffa4.
Proof. vm_refl. Qed.
Lemma D_7ffa4 : decode_any W_7ffa4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa8 : bv 32 := 0xff86f813.
Lemma F_7ffa8 : fetch_word AsanUbsan.M.loaded_segments (0x7fff0 : word) = Some W_7ffa8.
Proof. vm_refl. Qed.
Lemma D_7ffa8 : decode_any W_7ffa8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffac : bv 32 := 0xff877893.
Lemma F_7ffac : fetch_word AsanUbsan.M.loaded_segments (0x7fff4 : word) = Some W_7ffac.
Proof. vm_refl. Qed.
Lemma D_7ffac : decode_any W_7ffac = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb0 : bv 32 := 0x00083803.
Lemma F_7ffb0 : fetch_word AsanUbsan.M.loaded_segments (0x7fff8 : word) = Some W_7ffb0.
Proof. vm_refl. Qed.
Lemma D_7ffb0 : decode_any W_7ffb0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb4 : bv 32 := 0x0008b883.
Lemma F_7ffb4 : fetch_word AsanUbsan.M.loaded_segments (0x7fffc : word) = Some W_7ffb4.
Proof. vm_refl. Qed.
Lemma D_7ffb4 : decode_any W_7ffb4 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb8 : bv 32 := 0x0108e833.
Lemma F_7ffb8 : fetch_word AsanUbsan.M.loaded_segments (0x80000 : word) = Some W_7ffb8.
Proof. vm_refl. Qed.
Lemma D_7ffb8 : decode_any W_7ffb8 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffbc : bv 32 := 0x1a081063.
Lemma F_7ffbc : fetch_word AsanUbsan.M.loaded_segments (0x80004 : word) = Some W_7ffbc.
Proof. vm_refl. Qed.
Lemma D_7ffbc : decode_any W_7ffbc = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc0 : bv 32 := 0xfff54693.
Lemma F_7ffc0 : fetch_word AsanUbsan.M.loaded_segments (0x80008 : word) = Some W_7ffc0.
Proof. vm_refl. Qed.
Lemma D_7ffc0 : decode_any W_7ffc0 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc4 : bv 32 := 0x10c6e663.
Lemma F_7ffc4 : fetch_word AsanUbsan.M.loaded_segments (0x8000c : word) = Some W_7ffc4.
Proof. vm_refl. Qed.
Lemma D_7ffc4 : decode_any W_7ffc4 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc8 : bv 32 := 0xfbf00693.
Lemma F_7ffc8 : fetch_word AsanUbsan.M.loaded_segments (0x80010 : word) = Some W_7ffc8.
Proof. vm_refl. Qed.
Lemma D_7ffc8 : decode_any W_7ffc8 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffcc : bv 32 := 0x1946f463.
Lemma F_7ffcc : fetch_word AsanUbsan.M.loaded_segments (0x80014 : word) = Some W_7ffcc.
Proof. vm_refl. Qed.
Lemma D_7ffcc : decode_any W_7ffcc = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd0 : bv 32 := 0x000d4697.
Lemma F_7ffd0 : fetch_word AsanUbsan.M.loaded_segments (0x80018 : word) = Some W_7ffd0.
Proof. vm_refl. Qed.
Lemma D_7ffd0 : decode_any W_7ffd0 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd4 : bv 32 := 0x4e86b683.
Lemma F_7ffd4 : fetch_word AsanUbsan.M.loaded_segments (0x8001c : word) = Some W_7ffd4.
Proof. vm_refl. Qed.
Lemma D_7ffd4 : decode_any W_7ffd4 = Some (Load SZ8 true 13 13 1256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd8 : bv 32 := 0x00c507b3.
Lemma F_7ffd8 : fetch_word AsanUbsan.M.loaded_segments (0x80020 : word) = Some W_7ffd8.
Proof. vm_refl. Qed.
Lemma D_7ffd8 : decode_any W_7ffd8 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffdc : bv 32 := 0x0006b703.
Lemma F_7ffdc : fetch_word AsanUbsan.M.loaded_segments (0x80024 : word) = Some W_7ffdc.
Proof. vm_refl. Qed.
Lemma D_7ffdc : decode_any W_7ffdc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe0 : bv 32 := 0x00355693.
Lemma F_7ffe0 : fetch_word AsanUbsan.M.loaded_segments (0x80028 : word) = Some W_7ffe0.
Proof. vm_refl. Qed.
Lemma D_7ffe0 : decode_any W_7ffe0 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe4 : bv 32 := 0xfff78793.
Lemma F_7ffe4 : fetch_word AsanUbsan.M.loaded_segments (0x8002c : word) = Some W_7ffe4.
Proof. vm_refl. Qed.
Lemma D_7ffe4 : decode_any W_7ffe4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe8 : bv 32 := 0x0037d813.
Lemma F_7ffe8 : fetch_word AsanUbsan.M.loaded_segments (0x80030 : word) = Some W_7ffe8.
Proof. vm_refl. Qed.
Lemma D_7ffe8 : decode_any W_7ffe8 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffec : bv 32 := 0x00d706b3.
Lemma F_7ffec : fetch_word AsanUbsan.M.loaded_segments (0x80034 : word) = Some W_7ffec.
Proof. vm_refl. Qed.
Lemma D_7ffec : decode_any W_7ffec = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff0 : bv 32 := 0x01070733.
Lemma F_7fff0 : fetch_word AsanUbsan.M.loaded_segments (0x80038 : word) = Some W_7fff0.
Proof. vm_refl. Qed.
Lemma D_7fff0 : decode_any W_7fff0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff4 : bv 32 := 0xff86f813.
Lemma F_7fff4 : fetch_word AsanUbsan.M.loaded_segments (0x8003c : word) = Some W_7fff4.
Proof. vm_refl. Qed.
Lemma D_7fff4 : decode_any W_7fff4 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff8 : bv 32 := 0xff877893.
Lemma F_7fff8 : fetch_word AsanUbsan.M.loaded_segments (0x80040 : word) = Some W_7fff8.
Proof. vm_refl. Qed.
Lemma D_7fff8 : decode_any W_7fff8 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fffc : bv 32 := 0x00083803.
Lemma F_7fffc : fetch_word AsanUbsan.M.loaded_segments (0x80044 : word) = Some W_7fffc.
Proof. vm_refl. Qed.
Lemma D_7fffc : decode_any W_7fffc = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

