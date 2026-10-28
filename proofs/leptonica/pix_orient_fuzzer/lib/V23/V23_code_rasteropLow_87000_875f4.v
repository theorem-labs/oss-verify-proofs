(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_87000 : bv 32 := 0xffffc613.
Lemma F_87000 : fetch_word Ubsan.M.loaded_segments (0x87000 : word) = Some W_87000.
Proof. vm_refl. Qed.
Lemma D_87000 : decode_any W_87000 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87004 : bv 32 := 0x06013683.
Lemma F_87004 : fetch_word Ubsan.M.loaded_segments (0x87004 : word) = Some W_87004.
Proof. vm_refl. Qed.
Lemma D_87004 : decode_any W_87004 = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_87008 : bv 32 := 0xfff6c693.
Lemma F_87008 : fetch_word Ubsan.M.loaded_segments (0x87008 : word) = Some W_87008.
Proof. vm_refl. Qed.
Lemma D_87008 : decode_any W_87008 = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8700c : bv 32 := 0x00271793.
Lemma F_8700c : fetch_word Ubsan.M.loaded_segments (0x8700c : word) = Some W_8700c.
Proof. vm_refl. Qed.
Lemma D_8700c : decode_any W_8700c = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_87010 : bv 32 := 0x05813303.
Lemma F_87010 : fetch_word Ubsan.M.loaded_segments (0x87010 : word) = Some W_87010.
Proof. vm_refl. Qed.
Lemma D_87010 : decode_any W_87010 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_87014 : bv 32 := 0x00231313.
Lemma F_87014 : fetch_word Ubsan.M.loaded_segments (0x87014 : word) = Some W_87014.
Proof. vm_refl. Qed.
Lemma D_87014 : decode_any W_87014 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_87018 : bv 32 := 0x00357893.
Lemma F_87018 : fetch_word Ubsan.M.loaded_segments (0x87018 : word) = Some W_87018.
Proof. vm_refl. Qed.
Lemma D_87018 : decode_any W_87018 = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8701c : bv 32 := 0x05013903.
Lemma F_8701c : fetch_word Ubsan.M.loaded_segments (0x8701c : word) = Some W_8701c.
Proof. vm_refl. Qed.
Lemma D_8701c : decode_any W_8701c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_87020 : bv 32 := 0x02813803.
Lemma F_87020 : fetch_word Ubsan.M.loaded_segments (0x87020 : word) = Some W_87020.
Proof. vm_refl. Qed.
Lemma D_87020 : decode_any W_87020 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_87024 : bv 32 := 0x412804bb.
Lemma F_87024 : fetch_word Ubsan.M.loaded_segments (0x87024 : word) = Some W_87024.
Proof. vm_refl. Qed.
Lemma D_87024 : decode_any W_87024 = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_87028 : bv 32 := 0x03813383.
Lemma F_87028 : fetch_word Ubsan.M.loaded_segments (0x87028 : word) = Some W_87028.
Proof. vm_refl. Qed.
Lemma D_87028 : decode_any W_87028 = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8702c : bv 32 := 0x03013803.
Lemma F_8702c : fetch_word Ubsan.M.loaded_segments (0x8702c : word) = Some W_8702c.
Proof. vm_refl. Qed.
Lemma D_8702c : decode_any W_8702c = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_87030 : bv 32 := 0x007803b3.
Lemma F_87030 : fetch_word Ubsan.M.loaded_segments (0x87030 : word) = Some W_87030.
Proof. vm_refl. Qed.
Lemma D_87030 : decode_any W_87030 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_87034 : bv 32 := 0x04813283.
Lemma F_87034 : fetch_word Ubsan.M.loaded_segments (0x87034 : word) = Some W_87034.
Proof. vm_refl. Qed.
Lemma D_87034 : decode_any W_87034 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_87038 : bv 32 := 0x43f2d813.
Lemma F_87038 : fetch_word Ubsan.M.loaded_segments (0x87038 : word) = Some W_87038.
Proof. vm_refl. Qed.
Lemma D_87038 : decode_any W_87038 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_8703c : bv 32 := 0x00587e33.
Lemma F_8703c : fetch_word Ubsan.M.loaded_segments (0x8703c : word) = Some W_8703c.
Proof. vm_refl. Qed.
Lemma D_8703c : decode_any W_8703c = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_87040 : bv 32 := 0x02000813.
Lemma F_87040 : fetch_word Ubsan.M.loaded_segments (0x87040 : word) = Some W_87040.
Proof. vm_refl. Qed.
Lemma D_87040 : decode_any W_87040 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_87044 : bv 32 := 0x00813283.
Lemma F_87044 : fetch_word Ubsan.M.loaded_segments (0x87044 : word) = Some W_87044.
Proof. vm_refl. Qed.
Lemma D_87044 : decode_any W_87044 = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87048 : bv 32 := 0x0012f293.
Lemma F_87048 : fetch_word Ubsan.M.loaded_segments (0x87048 : word) = Some W_87048.
Proof. vm_refl. Qed.
Lemma D_87048 : decode_any W_87048 = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8704c : bv 32 := 0x00072713.
Lemma F_8704c : fetch_word Ubsan.M.loaded_segments (0x8704c : word) = Some W_8704c.
Proof. vm_refl. Qed.
Lemma D_8704c : decode_any W_8704c = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87050 : bv 32 := 0x01c38e33.
Lemma F_87050 : fetch_word Ubsan.M.loaded_segments (0x87050 : word) = Some W_87050.
Proof. vm_refl. Qed.
Lemma D_87050 : decode_any W_87050 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_87054 : bv 32 := 0xffb00393.
Lemma F_87054 : fetch_word Ubsan.M.loaded_segments (0x87054 : word) = Some W_87054.
Proof. vm_refl. Qed.
Lemma D_87054 : decode_any W_87054 = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_87058 : bv 32 := 0x412e09bb.
Lemma F_87058 : fetch_word Ubsan.M.loaded_segments (0x87058 : word) = Some W_87058.
Proof. vm_refl. Qed.
Lemma D_87058 : decode_any W_87058 = Some (Op32 ALU_SUB 19 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8705c : bv 32 := 0x06813e03.
Lemma F_8705c : fetch_word Ubsan.M.loaded_segments (0x8705c : word) = Some W_8705c.
Proof. vm_refl. Qed.
Lemma D_8705c : decode_any W_8705c = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_87060 : bv 32 := 0x006e0e33.
Lemma F_87060 : fetch_word Ubsan.M.loaded_segments (0x87060 : word) = Some W_87060.
Proof. vm_refl. Qed.
Lemma D_87060 : decode_any W_87060 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_87064 : bv 32 := 0x04013903.
Lemma F_87064 : fetch_word Ubsan.M.loaded_segments (0x87064 : word) = Some W_87064.
Proof. vm_refl. Qed.
Lemma D_87064 : decode_any W_87064 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_87068 : bv 32 := 0x412989bb.
Lemma F_87068 : fetch_word Ubsan.M.loaded_segments (0x87068 : word) = Some W_87068.
Proof. vm_refl. Qed.
Lemma D_87068 : decode_any W_87068 = Some (Op32 ALU_SUB 19 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8706c : bv 32 := 0x43f9da13.
Lemma F_8706c : fetch_word Ubsan.M.loaded_segments (0x8706c : word) = Some W_8706c.
Proof. vm_refl. Qed.
Lemma D_8706c : decode_any W_8706c = Some (ShiftImm ALU_SRA 20 19 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_87070 : bv 32 := 0x013a79b3.
Lemma F_87070 : fetch_word Ubsan.M.loaded_segments (0x87070 : word) = Some W_87070.
Proof. vm_refl. Qed.
Lemma D_87070 : decode_any W_87070 = Some (Op ALU_AND 19 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_87074 : bv 32 := 0x413484bb.
Lemma F_87074 : fetch_word Ubsan.M.loaded_segments (0x87074 : word) = Some W_87074.
Proof. vm_refl. Qed.
Lemma D_87074 : decode_any W_87074 = Some (Op32 ALU_SUB 9 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_87078 : bv 32 := 0x01f00993.
Lemma F_87078 : fetch_word Ubsan.M.loaded_segments (0x87078 : word) = Some W_87078.
Proof. vm_refl. Qed.
Lemma D_87078 : decode_any W_87078 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_8707c : bv 32 := 0x00050a13.
Lemma F_8707c : fetch_word Ubsan.M.loaded_segments (0x8707c : word) = Some W_8707c.
Proof. vm_refl. Qed.
Lemma D_8707c : decode_any W_8707c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87080 : bv 32 := 0x06813a83.
Lemma F_87080 : fetch_word Ubsan.M.loaded_segments (0x87080 : word) = Some W_87080.
Proof. vm_refl. Qed.
Lemma D_87080 : decode_any W_87080 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_87084 : bv 32 := 0x00ba8ab3.
Lemma F_87084 : fetch_word Ubsan.M.loaded_segments (0x87084 : word) = Some W_87084.
Proof. vm_refl. Qed.
Lemma D_87084 : decode_any W_87084 = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_87088 : bv 32 := 0x000a9463.
Lemma F_87088 : fetch_word Ubsan.M.loaded_segments (0x87088 : word) = Some W_87088.
Proof. vm_refl. Qed.
Lemma D_87088 : decode_any W_87088 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8708c : bv 32 := 0xc68fb06f.
Lemma F_8708c : fetch_word Ubsan.M.loaded_segments (0x8708c : word) = Some W_8708c.
Proof. vm_refl. Qed.
Lemma D_8708c : decode_any W_8708c = Some (Jal 0 2077800, 4%Z).
Proof. vm_refl. Qed.

Definition W_87090 : bv 32 := 0x010f1463.
Lemma F_87090 : fetch_word Ubsan.M.loaded_segments (0x87090 : word) = Some W_87090.
Proof. vm_refl. Qed.
Lemma D_87090 : decode_any W_87090 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87094 : bv 32 := 0xc60fb06f.
Lemma F_87094 : fetch_word Ubsan.M.loaded_segments (0x87094 : word) = Some W_87094.
Proof. vm_refl. Qed.
Lemma D_87094 : decode_any W_87094 = Some (Jal 0 2077792, 4%Z).
Proof. vm_refl. Qed.

Definition W_87098 : bv 32 := 0x000aab03.
Lemma F_87098 : fetch_word Ubsan.M.loaded_segments (0x87098 : word) = Some W_87098.
Proof. vm_refl. Qed.
Lemma D_87098 : decode_any W_87098 = Some (Load SZ4 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8709c : bv 32 := 0x01db1b3b.
Lemma F_8709c : fetch_word Ubsan.M.loaded_segments (0x8709c : word) = Some W_8709c.
Proof. vm_refl. Qed.
Lemma D_8709c : decode_any W_8709c = Some (Op32 ALU_SLL 22 22 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_870a0 : bv 32 := 0x02029463.
Lemma F_870a0 : fetch_word Ubsan.M.loaded_segments (0x870a0 : word) = Some W_870a0.
Proof. vm_refl. Qed.
Lemma D_870a0 : decode_any W_870a0 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_870a4 : bv 32 := 0x0153f463.
Lemma F_870a4 : fetch_word Ubsan.M.loaded_segments (0x870a4 : word) = Some W_870a4.
Proof. vm_refl. Qed.
Lemma D_870a4 : decode_any W_870a4 = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_870a8 : bv 32 := 0xc4cfb06f.
Lemma F_870a8 : fetch_word Ubsan.M.loaded_segments (0x870a8 : word) = Some W_870a8.
Proof. vm_refl. Qed.
Lemma D_870a8 : decode_any W_870a8 = Some (Jal 0 2077772, 4%Z).
Proof. vm_refl. Qed.

Definition W_870ac : bv 32 := 0x0089f463.
Lemma F_870ac : fetch_word Ubsan.M.loaded_segments (0x870ac : word) = Some W_870ac.
Proof. vm_refl. Qed.
Lemma D_870ac : decode_any W_870ac = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_870b0 : bv 32 := 0xc44fb06f.
Lemma F_870b0 : fetch_word Ubsan.M.loaded_segments (0x870b0 : word) = Some W_870b0.
Proof. vm_refl. Qed.
Lemma D_870b0 : decode_any W_870b0 = Some (Jal 0 2077764, 4%Z).
Proof. vm_refl. Qed.

Definition W_870b4 : bv 32 := 0x004aab83.
Lemma F_870b4 : fetch_word Ubsan.M.loaded_segments (0x870b4 : word) = Some W_870b4.
Proof. vm_refl. Qed.
Lemma D_870b4 : decode_any W_870b4 = Some (Load SZ4 true 23 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_870b8 : bv 32 := 0x00cb7b33.
Lemma F_870b8 : fetch_word Ubsan.M.loaded_segments (0x870b8 : word) = Some W_870b8.
Proof. vm_refl. Qed.
Lemma D_870b8 : decode_any W_870b8 = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_870bc : bv 32 := 0x008bdbbb.
Lemma F_870bc : fetch_word Ubsan.M.loaded_segments (0x870bc : word) = Some W_870bc.
Proof. vm_refl. Qed.
Lemma D_870bc : decode_any W_870bc = Some (Op32 ALU_SRL 23 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_870c0 : bv 32 := 0x01fbfbb3.
Lemma F_870c0 : fetch_word Ubsan.M.loaded_segments (0x870c0 : word) = Some W_870c0.
Proof. vm_refl. Qed.
Lemma D_870c0 : decode_any W_870c0 = Some (Op ALU_AND 23 23 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_870c4 : bv 32 := 0x016beb33.
Lemma F_870c4 : fetch_word Ubsan.M.loaded_segments (0x870c4 : word) = Some W_870c4.
Proof. vm_refl. Qed.
Lemma D_870c4 : decode_any W_870c4 = Some (Op ALU_OR 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_870c8 : bv 32 := 0x00088463.
Lemma F_870c8 : fetch_word Ubsan.M.loaded_segments (0x870c8 : word) = Some W_870c8.
Proof. vm_refl. Qed.
Lemma D_870c8 : decode_any W_870c8 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_870cc : bv 32 := 0xc28fb06f.
Lemma F_870cc : fetch_word Ubsan.M.loaded_segments (0x870cc : word) = Some W_870cc.
Proof. vm_refl. Qed.
Lemma D_870cc : decode_any W_870cc = Some (Jal 0 2077736, 4%Z).
Proof. vm_refl. Qed.

Definition W_870d0 : bv 32 := 0x00051463.
Lemma F_870d0 : fetch_word Ubsan.M.loaded_segments (0x870d0 : word) = Some W_870d0.
Proof. vm_refl. Qed.
Lemma D_870d0 : decode_any W_870d0 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_870d4 : bv 32 := 0xc20fb06f.
Lemma F_870d4 : fetch_word Ubsan.M.loaded_segments (0x870d4 : word) = Some W_870d4.
Proof. vm_refl. Qed.
Lemma D_870d4 : decode_any W_870d4 = Some (Jal 0 2077728, 4%Z).
Proof. vm_refl. Qed.

Definition W_870d8 : bv 32 := 0x00052b83.
Lemma F_870d8 : fetch_word Ubsan.M.loaded_segments (0x870d8 : word) = Some W_870d8.
Proof. vm_refl. Qed.
Lemma D_870d8 : decode_any W_870d8 = Some (Load SZ4 true 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_870dc : bv 32 := 0x06013903.
Lemma F_870dc : fetch_word Ubsan.M.loaded_segments (0x870dc : word) = Some W_870dc.
Proof. vm_refl. Qed.
Lemma D_870dc : decode_any W_870dc = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_870e0 : bv 32 := 0x012b7b33.
Lemma F_870e0 : fetch_word Ubsan.M.loaded_segments (0x870e0 : word) = Some W_870e0.
Proof. vm_refl. Qed.
Lemma D_870e0 : decode_any W_870e0 = Some (Op ALU_AND 22 22 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_870e4 : bv 32 := 0x00dbfbb3.
Lemma F_870e4 : fetch_word Ubsan.M.loaded_segments (0x870e4 : word) = Some W_870e4.
Proof. vm_refl. Qed.
Lemma D_870e4 : decode_any W_870e4 = Some (Op ALU_AND 23 23 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_870e8 : bv 32 := 0x016bebb3.
Lemma F_870e8 : fetch_word Ubsan.M.loaded_segments (0x870e8 : word) = Some W_870e8.
Proof. vm_refl. Qed.
Lemma D_870e8 : decode_any W_870e8 = Some (Op ALU_OR 23 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_870ec : bv 32 := 0x01478b33.
Lemma F_870ec : fetch_word Ubsan.M.loaded_segments (0x870ec : word) = Some W_870ec.
Proof. vm_refl. Qed.
Lemma D_870ec : decode_any W_870ec = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_870f0 : bv 32 := 0x01752023.
Lemma F_870f0 : fetch_word Ubsan.M.loaded_segments (0x870f0 : word) = Some W_870f0.
Proof. vm_refl. Qed.
Lemma D_870f0 : decode_any W_870f0 = Some (Store SZ4 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_870f4 : bv 32 := 0x000b1463.
Lemma F_870f4 : fetch_word Ubsan.M.loaded_segments (0x870f4 : word) = Some W_870f4.
Proof. vm_refl. Qed.
Lemma D_870f4 : decode_any W_870f4 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_870f8 : bv 32 := 0xbfcfb06f.
Lemma F_870f8 : fetch_word Ubsan.M.loaded_segments (0x870f8 : word) = Some W_870f8.
Proof. vm_refl. Qed.
Lemma D_870f8 : decode_any W_870f8 = Some (Jal 0 2077692, 4%Z).
Proof. vm_refl. Qed.

Definition W_870fc : bv 32 := 0x014b3a33.
Lemma F_870fc : fetch_word Ubsan.M.loaded_segments (0x870fc : word) = Some W_870fc.
Proof. vm_refl. Qed.
Lemma D_870fc : decode_any W_870fc = Some (Op ALU_SLTU 20 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_87100 : bv 32 := 0x00ea4a33.
Lemma F_87100 : fetch_word Ubsan.M.loaded_segments (0x87100 : word) = Some W_87100.
Proof. vm_refl. Qed.
Lemma D_87100 : decode_any W_87100 = Some (Op ALU_XOR 20 20 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_87104 : bv 32 := 0x001a4a13.
Lemma F_87104 : fetch_word Ubsan.M.loaded_segments (0x87104 : word) = Some W_87104.
Proof. vm_refl. Qed.
Lemma D_87104 : decode_any W_87104 = Some (OpImm ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87108 : bv 32 := 0x000a1463.
Lemma F_87108 : fetch_word Ubsan.M.loaded_segments (0x87108 : word) = Some W_87108.
Proof. vm_refl. Qed.
Lemma D_87108 : decode_any W_87108 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8710c : bv 32 := 0xbe8fb06f.
Lemma F_8710c : fetch_word Ubsan.M.loaded_segments (0x8710c : word) = Some W_8710c.
Proof. vm_refl. Qed.
Lemma D_8710c : decode_any W_8710c = Some (Jal 0 2077672, 4%Z).
Proof. vm_refl. Qed.

Definition W_87110 : bv 32 := 0x00be0a33.
Lemma F_87110 : fetch_word Ubsan.M.loaded_segments (0x87110 : word) = Some W_87110.
Proof. vm_refl. Qed.
Lemma D_87110 : decode_any W_87110 = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_87114 : bv 32 := 0x000a1463.
Lemma F_87114 : fetch_word Ubsan.M.loaded_segments (0x87114 : word) = Some W_87114.
Proof. vm_refl. Qed.
Lemma D_87114 : decode_any W_87114 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87118 : bv 32 := 0xbdcfb06f.
Lemma F_87118 : fetch_word Ubsan.M.loaded_segments (0x87118 : word) = Some W_87118.
Proof. vm_refl. Qed.
Lemma D_87118 : decode_any W_87118 = Some (Jal 0 2077660, 4%Z).
Proof. vm_refl. Qed.

Definition W_8711c : bv 32 := 0x015a3a33.
Lemma F_8711c : fetch_word Ubsan.M.loaded_segments (0x8711c : word) = Some W_8711c.
Proof. vm_refl. Qed.
Lemma D_8711c : decode_any W_8711c = Some (Op ALU_SLTU 20 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_87120 : bv 32 := 0x07813903.
Lemma F_87120 : fetch_word Ubsan.M.loaded_segments (0x87120 : word) = Some W_87120.
Proof. vm_refl. Qed.
Lemma D_87120 : decode_any W_87120 = Some (Load SZ8 true 18 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_87124 : bv 32 := 0x012a4a33.
Lemma F_87124 : fetch_word Ubsan.M.loaded_segments (0x87124 : word) = Some W_87124.
Proof. vm_refl. Qed.
Lemma D_87124 : decode_any W_87124 = Some (Op ALU_XOR 20 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_87128 : bv 32 := 0x001a4a13.
Lemma F_87128 : fetch_word Ubsan.M.loaded_segments (0x87128 : word) = Some W_87128.
Proof. vm_refl. Qed.
Lemma D_87128 : decode_any W_87128 = Some (OpImm ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8712c : bv 32 := 0x000a1463.
Lemma F_8712c : fetch_word Ubsan.M.loaded_segments (0x8712c : word) = Some W_8712c.
Proof. vm_refl. Qed.
Lemma D_8712c : decode_any W_8712c = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87130 : bv 32 := 0xbc4fb06f.
Lemma F_87130 : fetch_word Ubsan.M.loaded_segments (0x87130 : word) = Some W_87130.
Proof. vm_refl. Qed.
Lemma D_87130 : decode_any W_87130 = Some (Jal 0 2077636, 4%Z).
Proof. vm_refl. Qed.

Definition W_87134 : bv 32 := 0x0014849b.
Lemma F_87134 : fetch_word Ubsan.M.loaded_segments (0x87134 : word) = Some W_87134.
Proof. vm_refl. Qed.
Lemma D_87134 : decode_any W_87134 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87138 : bv 32 := 0x006585b3.
Lemma F_87138 : fetch_word Ubsan.M.loaded_segments (0x87138 : word) = Some W_87138.
Proof. vm_refl. Qed.
Lemma D_87138 : decode_any W_87138 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8713c : bv 32 := 0x00f50533.
Lemma F_8713c : fetch_word Ubsan.M.loaded_segments (0x8713c : word) = Some W_8713c.
Proof. vm_refl. Qed.
Lemma D_8713c : decode_any W_8713c = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_87140 : bv 32 := 0x000b0a13.
Lemma F_87140 : fetch_word Ubsan.M.loaded_segments (0x87140 : word) = Some W_87140.
Proof. vm_refl. Qed.
Lemma D_87140 : decode_any W_87140 = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87144 : bv 32 := 0xf2049ee3.
Lemma F_87144 : fetch_word Ubsan.M.loaded_segments (0x87144 : word) = Some W_87144.
Proof. vm_refl. Qed.
Lemma D_87144 : decode_any W_87144 = Some (Branch BC_NE 9 0 7996, 4%Z).
Proof. vm_refl. Qed.

Definition W_87148 : bv 32 := 0x4700006f.
Lemma F_87148 : fetch_word Ubsan.M.loaded_segments (0x87148 : word) = Some W_87148.
Proof. vm_refl. Qed.
Lemma D_87148 : decode_any W_87148 = Some (Jal 0 1136, 4%Z).
Proof. vm_refl. Qed.

Definition W_8714c : bv 32 := 0x18008263.
Lemma F_8714c : fetch_word Ubsan.M.loaded_segments (0x8714c : word) = Some W_8714c.
Proof. vm_refl. Qed.
Lemma D_8714c : decode_any W_8714c = Some (Branch BC_EQ 1 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_87150 : bv 32 := 0x00000593.
Lemma F_87150 : fetch_word Ubsan.M.loaded_segments (0x87150 : word) = Some W_87150.
Proof. vm_refl. Qed.
Lemma D_87150 : decode_any W_87150 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87154 : bv 32 := 0xffffc613.
Lemma F_87154 : fetch_word Ubsan.M.loaded_segments (0x87154 : word) = Some W_87154.
Proof. vm_refl. Qed.
Lemma D_87154 : decode_any W_87154 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87158 : bv 32 := 0x00c13023.
Lemma F_87158 : fetch_word Ubsan.M.loaded_segments (0x87158 : word) = Some W_87158.
Proof. vm_refl. Qed.
Lemma D_87158 : decode_any W_87158 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8715c : bv 32 := 0xfffdc293.
Lemma F_8715c : fetch_word Ubsan.M.loaded_segments (0x8715c : word) = Some W_8715c.
Proof. vm_refl. Qed.
Lemma D_8715c : decode_any W_8715c = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87160 : bv 32 := 0x00271393.
Lemma F_87160 : fetch_word Ubsan.M.loaded_segments (0x87160 : word) = Some W_87160.
Proof. vm_refl. Qed.
Lemma D_87160 : decode_any W_87160 = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_87164 : bv 32 := 0x05813683.
Lemma F_87164 : fetch_word Ubsan.M.loaded_segments (0x87164 : word) = Some W_87164.
Proof. vm_refl. Qed.
Lemma D_87164 : decode_any W_87164 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_87168 : bv 32 := 0x00269693.
Lemma F_87168 : fetch_word Ubsan.M.loaded_segments (0x87168 : word) = Some W_87168.
Proof. vm_refl. Qed.
Lemma D_87168 : decode_any W_87168 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8716c : bv 32 := 0x003cfb93.
Lemma F_8716c : fetch_word Ubsan.M.loaded_segments (0x8716c : word) = Some W_8716c.
Proof. vm_refl. Qed.
Lemma D_8716c : decode_any W_8716c = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_87170 : bv 32 := 0x0037f613.
Lemma F_87170 : fetch_word Ubsan.M.loaded_segments (0x87170 : word) = Some W_87170.
Proof. vm_refl. Qed.
Lemma D_87170 : decode_any W_87170 = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_87174 : bv 32 := 0x05013483.
Lemma F_87174 : fetch_word Ubsan.M.loaded_segments (0x87174 : word) = Some W_87174.
Proof. vm_refl. Qed.
Lemma D_87174 : decode_any W_87174 = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_87178 : bv 32 := 0x02813803.
Lemma F_87178 : fetch_word Ubsan.M.loaded_segments (0x87178 : word) = Some W_87178.
Proof. vm_refl. Qed.
Lemma D_87178 : decode_any W_87178 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8717c : bv 32 := 0x4098083b.
Lemma F_8717c : fetch_word Ubsan.M.loaded_segments (0x8717c : word) = Some W_8717c.
Proof. vm_refl. Qed.
Lemma D_8717c : decode_any W_8717c = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_87180 : bv 32 := 0x03813883.
Lemma F_87180 : fetch_word Ubsan.M.loaded_segments (0x87180 : word) = Some W_87180.
Proof. vm_refl. Qed.
Lemma D_87180 : decode_any W_87180 = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_87184 : bv 32 := 0x03013e03.
Lemma F_87184 : fetch_word Ubsan.M.loaded_segments (0x87184 : word) = Some W_87184.
Proof. vm_refl. Qed.
Lemma D_87184 : decode_any W_87184 = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_87188 : bv 32 := 0x011e08b3.
Lemma F_87188 : fetch_word Ubsan.M.loaded_segments (0x87188 : word) = Some W_87188.
Proof. vm_refl. Qed.
Lemma D_87188 : decode_any W_87188 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8718c : bv 32 := 0x04813a03.
Lemma F_8718c : fetch_word Ubsan.M.loaded_segments (0x8718c : word) = Some W_8718c.
Proof. vm_refl. Qed.
Lemma D_8718c : decode_any W_8718c = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_87190 : bv 32 := 0x43fa5e13.
Lemma F_87190 : fetch_word Ubsan.M.loaded_segments (0x87190 : word) = Some W_87190.
Proof. vm_refl. Qed.
Lemma D_87190 : decode_any W_87190 = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_87194 : bv 32 := 0x01013983.
Lemma F_87194 : fetch_word Ubsan.M.loaded_segments (0x87194 : word) = Some W_87194.
Proof. vm_refl. Qed.
Lemma D_87194 : decode_any W_87194 = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87198 : bv 32 := 0x0019f993.
Lemma F_87198 : fetch_word Ubsan.M.loaded_segments (0x87198 : word) = Some W_87198.
Proof. vm_refl. Qed.
Lemma D_87198 : decode_any W_87198 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8719c : bv 32 := 0x001d7c13.
Lemma F_8719c : fetch_word Ubsan.M.loaded_segments (0x8719c : word) = Some W_8719c.
Proof. vm_refl. Qed.
Lemma D_8719c : decode_any W_8719c = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_871a0 : bv 32 := 0x01f00093.
Lemma F_871a0 : fetch_word Ubsan.M.loaded_segments (0x871a0 : word) = Some W_871a0.
Proof. vm_refl. Qed.
Lemma D_871a0 : decode_any W_871a0 = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_871a4 : bv 32 := 0x014e7e33.
Lemma F_871a4 : fetch_word Ubsan.M.loaded_segments (0x871a4 : word) = Some W_871a4.
Proof. vm_refl. Qed.
Lemma D_871a4 : decode_any W_871a4 = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_871a8 : bv 32 := 0x409888bb.
Lemma F_871a8 : fetch_word Ubsan.M.loaded_segments (0x871a8 : word) = Some W_871a8.
Proof. vm_refl. Qed.
Lemma D_871a8 : decode_any W_871a8 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_871ac : bv 32 := 0x00d78a33.
Lemma F_871ac : fetch_word Ubsan.M.loaded_segments (0x871ac : word) = Some W_871ac.
Proof. vm_refl. Qed.
Lemma D_871ac : decode_any W_871ac = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_871b0 : bv 32 := 0x00163b13.
Lemma F_871b0 : fetch_word Ubsan.M.loaded_segments (0x871b0 : word) = Some W_871b0.
Proof. vm_refl. Qed.
Lemma D_871b0 : decode_any W_871b0 = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_871b4 : bv 32 := 0x04013603.
Lemma F_871b4 : fetch_word Ubsan.M.loaded_segments (0x871b4 : word) = Some W_871b4.
Proof. vm_refl. Qed.
Lemma D_871b4 : decode_any W_871b4 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_871b8 : bv 32 := 0x40c8863b.
Lemma F_871b8 : fetch_word Ubsan.M.loaded_segments (0x871b8 : word) = Some W_871b8.
Proof. vm_refl. Qed.
Lemma D_871b8 : decode_any W_871b8 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_871bc : bv 32 := 0x01c6063b.
Lemma F_871bc : fetch_word Ubsan.M.loaded_segments (0x871bc : word) = Some W_871bc.
Proof. vm_refl. Qed.
Lemma D_871bc : decode_any W_871bc = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_871c0 : bv 32 := 0x43f65893.
Lemma F_871c0 : fetch_word Ubsan.M.loaded_segments (0x871c0 : word) = Some W_871c0.
Proof. vm_refl. Qed.
Lemma D_871c0 : decode_any W_871c0 = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_871c4 : bv 32 := 0x00c8f633.
Lemma F_871c4 : fetch_word Ubsan.M.loaded_segments (0x871c4 : word) = Some W_871c4.
Proof. vm_refl. Qed.
Lemma D_871c4 : decode_any W_871c4 = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_871c8 : bv 32 := 0x40c804bb.
Lemma F_871c8 : fetch_word Ubsan.M.loaded_segments (0x871c8 : word) = Some W_871c8.
Proof. vm_refl. Qed.
Lemma D_871c8 : decode_any W_871c8 = Some (Op32 ALU_SUB 9 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_871cc : bv 32 := 0x00072e13.
Lemma F_871cc : fetch_word Ubsan.M.loaded_segments (0x871cc : word) = Some W_871cc.
Proof. vm_refl. Qed.
Lemma D_871cc : decode_any W_871cc = Some (OpImm ALU_SLT 28 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_871d0 : bv 32 := 0x000c8813.
Lemma F_871d0 : fetch_word Ubsan.M.loaded_segments (0x871d0 : word) = Some W_871d0.
Proof. vm_refl. Qed.
Lemma D_871d0 : decode_any W_871d0 = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_871d4 : bv 32 := 0x00b78d33.
Lemma F_871d4 : fetch_word Ubsan.M.loaded_segments (0x871d4 : word) = Some W_871d4.
Proof. vm_refl. Qed.
Lemma D_871d4 : decode_any W_871d4 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_871d8 : bv 32 := 0x01a03633.
Lemma F_871d8 : fetch_word Ubsan.M.loaded_segments (0x871d8 : word) = Some W_871d8.
Proof. vm_refl. Qed.
Lemma D_871d8 : decode_any W_871d8 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_871dc : bv 32 := 0x00cb7633.
Lemma F_871dc : fetch_word Ubsan.M.loaded_segments (0x871dc : word) = Some W_871dc.
Proof. vm_refl. Qed.
Lemma D_871dc : decode_any W_871dc = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_871e0 : bv 32 := 0x04098a63.
Lemma F_871e0 : fetch_word Ubsan.M.loaded_segments (0x871e0 : word) = Some W_871e0.
Proof. vm_refl. Qed.
Lemma D_871e0 : decode_any W_871e0 = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_871e4 : bv 32 := 0x00061463.
Lemma F_871e4 : fetch_word Ubsan.M.loaded_segments (0x871e4 : word) = Some W_871e4.
Proof. vm_refl. Qed.
Lemma D_871e4 : decode_any W_871e4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_871e8 : bv 32 := 0xb0cfb06f.
Lemma F_871e8 : fetch_word Ubsan.M.loaded_segments (0x871e8 : word) = Some W_871e8.
Proof. vm_refl. Qed.
Lemma D_871e8 : decode_any W_871e8 = Some (Jal 0 2077452, 4%Z).
Proof. vm_refl. Qed.

Definition W_871ec : bv 32 := 0x02000613.
Lemma F_871ec : fetch_word Ubsan.M.loaded_segments (0x871ec : word) = Some W_871ec.
Proof. vm_refl. Qed.
Lemma D_871ec : decode_any W_871ec = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_871f0 : bv 32 := 0x00cf1463.
Lemma F_871f0 : fetch_word Ubsan.M.loaded_segments (0x871f0 : word) = Some W_871f0.
Proof. vm_refl. Qed.
Lemma D_871f0 : decode_any W_871f0 = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_871f4 : bv 32 := 0xb00fb06f.
Lemma F_871f4 : fetch_word Ubsan.M.loaded_segments (0x871f4 : word) = Some W_871f4.
Proof. vm_refl. Qed.
Lemma D_871f4 : decode_any W_871f4 = Some (Jal 0 2077440, 4%Z).
Proof. vm_refl. Qed.

Definition W_871f8 : bv 32 := 0x000d2603.
Lemma F_871f8 : fetch_word Ubsan.M.loaded_segments (0x871f8 : word) = Some W_871f8.
Proof. vm_refl. Qed.
Lemma D_871f8 : decode_any W_871f8 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_871fc : bv 32 := 0x01d61abb.
Lemma F_871fc : fetch_word Ubsan.M.loaded_segments (0x871fc : word) = Some W_871fc.
Proof. vm_refl. Qed.
Lemma D_871fc : decode_any W_871fc = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_87200 : bv 32 := 0x040c1663.
Lemma F_87200 : fetch_word Ubsan.M.loaded_segments (0x87200 : word) = Some W_87200.
Proof. vm_refl. Qed.
Lemma D_87200 : decode_any W_87200 = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_87204 : bv 32 := 0xffb00613.
Lemma F_87204 : fetch_word Ubsan.M.loaded_segments (0x87204 : word) = Some W_87204.
Proof. vm_refl. Qed.
Lemma D_87204 : decode_any W_87204 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_87208 : bv 32 := 0x01a67463.
Lemma F_87208 : fetch_word Ubsan.M.loaded_segments (0x87208 : word) = Some W_87208.
Proof. vm_refl. Qed.
Lemma D_87208 : decode_any W_87208 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8720c : bv 32 := 0xae8fb06f.
Lemma F_8720c : fetch_word Ubsan.M.loaded_segments (0x8720c : word) = Some W_8720c.
Proof. vm_refl. Qed.
Lemma D_8720c : decode_any W_8720c = Some (Jal 0 2077416, 4%Z).
Proof. vm_refl. Qed.

Definition W_87210 : bv 32 := 0x0080f463.
Lemma F_87210 : fetch_word Ubsan.M.loaded_segments (0x87210 : word) = Some W_87210.
Proof. vm_refl. Qed.
Lemma D_87210 : decode_any W_87210 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87214 : bv 32 := 0xae0fb06f.
Lemma F_87214 : fetch_word Ubsan.M.loaded_segments (0x87214 : word) = Some W_87214.
Proof. vm_refl. Qed.
Lemma D_87214 : decode_any W_87214 = Some (Jal 0 2077408, 4%Z).
Proof. vm_refl. Qed.

Definition W_87218 : bv 32 := 0x004d2603.
Lemma F_87218 : fetch_word Ubsan.M.loaded_segments (0x87218 : word) = Some W_87218.
Proof. vm_refl. Qed.
Lemma D_87218 : decode_any W_87218 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8721c : bv 32 := 0x00013883.
Lemma F_8721c : fetch_word Ubsan.M.loaded_segments (0x8721c : word) = Some W_8721c.
Proof. vm_refl. Qed.
Lemma D_8721c : decode_any W_8721c = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87220 : bv 32 := 0x011af8b3.
Lemma F_87220 : fetch_word Ubsan.M.loaded_segments (0x87220 : word) = Some W_87220.
Proof. vm_refl. Qed.
Lemma D_87220 : decode_any W_87220 = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_87224 : bv 32 := 0x0086563b.
Lemma F_87224 : fetch_word Ubsan.M.loaded_segments (0x87224 : word) = Some W_87224.
Proof. vm_refl. Qed.
Lemma D_87224 : decode_any W_87224 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87228 : bv 32 := 0x01f67633.
Lemma F_87228 : fetch_word Ubsan.M.loaded_segments (0x87228 : word) = Some W_87228.
Proof. vm_refl. Qed.
Lemma D_87228 : decode_any W_87228 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_8722c : bv 32 := 0x01166ab3.
Lemma F_8722c : fetch_word Ubsan.M.loaded_segments (0x8722c : word) = Some W_8722c.
Proof. vm_refl. Qed.
Lemma D_8722c : decode_any W_8722c = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_87230 : bv 32 := 0x01c0006f.
Lemma F_87230 : fetch_word Ubsan.M.loaded_segments (0x87230 : word) = Some W_87230.
Proof. vm_refl. Qed.
Lemma D_87230 : decode_any W_87230 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_87234 : bv 32 := 0x00061463.
Lemma F_87234 : fetch_word Ubsan.M.loaded_segments (0x87234 : word) = Some W_87234.
Proof. vm_refl. Qed.
Lemma D_87234 : decode_any W_87234 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87238 : bv 32 := 0xabcfb06f.
Lemma F_87238 : fetch_word Ubsan.M.loaded_segments (0x87238 : word) = Some W_87238.
Proof. vm_refl. Qed.
Lemma D_87238 : decode_any W_87238 = Some (Jal 0 2077372, 4%Z).
Proof. vm_refl. Qed.

Definition W_8723c : bv 32 := 0x0080f463.
Lemma F_8723c : fetch_word Ubsan.M.loaded_segments (0x8723c : word) = Some W_8723c.
Proof. vm_refl. Qed.
Lemma D_8723c : decode_any W_8723c = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87240 : bv 32 := 0xab4fb06f.
Lemma F_87240 : fetch_word Ubsan.M.loaded_segments (0x87240 : word) = Some W_87240.
Proof. vm_refl. Qed.
Lemma D_87240 : decode_any W_87240 = Some (Jal 0 2077364, 4%Z).
Proof. vm_refl. Qed.

Definition W_87244 : bv 32 := 0x000d2603.
Lemma F_87244 : fetch_word Ubsan.M.loaded_segments (0x87244 : word) = Some W_87244.
Proof. vm_refl. Qed.
Lemma D_87244 : decode_any W_87244 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87248 : bv 32 := 0x00865abb.
Lemma F_87248 : fetch_word Ubsan.M.loaded_segments (0x87248 : word) = Some W_87248.
Proof. vm_refl. Qed.
Lemma D_87248 : decode_any W_87248 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8724c : bv 32 := 0x000b8463.
Lemma F_8724c : fetch_word Ubsan.M.loaded_segments (0x8724c : word) = Some W_8724c.
Proof. vm_refl. Qed.
Lemma D_8724c : decode_any W_8724c = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87250 : bv 32 := 0xaa4fb06f.
Lemma F_87250 : fetch_word Ubsan.M.loaded_segments (0x87250 : word) = Some W_87250.
Proof. vm_refl. Qed.
Lemma D_87250 : decode_any W_87250 = Some (Jal 0 2077348, 4%Z).
Proof. vm_refl. Qed.

Definition W_87254 : bv 32 := 0x000c9463.
Lemma F_87254 : fetch_word Ubsan.M.loaded_segments (0x87254 : word) = Some W_87254.
Proof. vm_refl. Qed.
Lemma D_87254 : decode_any W_87254 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87258 : bv 32 := 0xa9cfb06f.
Lemma F_87258 : fetch_word Ubsan.M.loaded_segments (0x87258 : word) = Some W_87258.
Proof. vm_refl. Qed.
Lemma D_87258 : decode_any W_87258 = Some (Jal 0 2077340, 4%Z).
Proof. vm_refl. Qed.

Definition W_8725c : bv 32 := 0x000ca603.
Lemma F_8725c : fetch_word Ubsan.M.loaded_segments (0x8725c : word) = Some W_8725c.
Proof. vm_refl. Qed.
Lemma D_8725c : decode_any W_8725c = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87260 : bv 32 := 0xfffac893.
Lemma F_87260 : fetch_word Ubsan.M.loaded_segments (0x87260 : word) = Some W_87260.
Proof. vm_refl. Qed.
Lemma D_87260 : decode_any W_87260 = Some (OpImm ALU_XOR 17 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87264 : bv 32 := 0x00567ab3.
Lemma F_87264 : fetch_word Ubsan.M.loaded_segments (0x87264 : word) = Some W_87264.
Proof. vm_refl. Qed.
Lemma D_87264 : decode_any W_87264 = Some (Op ALU_AND 21 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_87268 : bv 32 := 0x01166633.
Lemma F_87268 : fetch_word Ubsan.M.loaded_segments (0x87268 : word) = Some W_87268.
Proof. vm_refl. Qed.
Lemma D_87268 : decode_any W_87268 = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8726c : bv 32 := 0x01b67633.
Lemma F_8726c : fetch_word Ubsan.M.loaded_segments (0x8726c : word) = Some W_8726c.
Proof. vm_refl. Qed.
Lemma D_8726c : decode_any W_8726c = Some (Op ALU_AND 12 12 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_87270 : bv 32 := 0x01566633.
Lemma F_87270 : fetch_word Ubsan.M.loaded_segments (0x87270 : word) = Some W_87270.
Proof. vm_refl. Qed.
Lemma D_87270 : decode_any W_87270 = Some (Op ALU_OR 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_87274 : bv 32 := 0x01038ab3.
Lemma F_87274 : fetch_word Ubsan.M.loaded_segments (0x87274 : word) = Some W_87274.
Proof. vm_refl. Qed.
Lemma D_87274 : decode_any W_87274 = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87278 : bv 32 := 0x00cca023.
Lemma F_87278 : fetch_word Ubsan.M.loaded_segments (0x87278 : word) = Some W_87278.
Proof. vm_refl. Qed.
Lemma D_87278 : decode_any W_87278 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8727c : bv 32 := 0x000a9463.
Lemma F_8727c : fetch_word Ubsan.M.loaded_segments (0x8727c : word) = Some W_8727c.
Proof. vm_refl. Qed.
Lemma D_8727c : decode_any W_8727c = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87280 : bv 32 := 0xa74fb06f.
Lemma F_87280 : fetch_word Ubsan.M.loaded_segments (0x87280 : word) = Some W_87280.
Proof. vm_refl. Qed.
Lemma D_87280 : decode_any W_87280 = Some (Jal 0 2077300, 4%Z).
Proof. vm_refl. Qed.

Definition W_87284 : bv 32 := 0x010ab633.
Lemma F_87284 : fetch_word Ubsan.M.loaded_segments (0x87284 : word) = Some W_87284.
Proof. vm_refl. Qed.
Lemma D_87284 : decode_any W_87284 = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87288 : bv 32 := 0x01c64633.
Lemma F_87288 : fetch_word Ubsan.M.loaded_segments (0x87288 : word) = Some W_87288.
Proof. vm_refl. Qed.
Lemma D_87288 : decode_any W_87288 = Some (Op ALU_XOR 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8728c : bv 32 := 0x00164613.
Lemma F_8728c : fetch_word Ubsan.M.loaded_segments (0x8728c : word) = Some W_8728c.
Proof. vm_refl. Qed.
Lemma D_8728c : decode_any W_8728c = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87290 : bv 32 := 0x00061463.
Lemma F_87290 : fetch_word Ubsan.M.loaded_segments (0x87290 : word) = Some W_87290.
Proof. vm_refl. Qed.
Lemma D_87290 : decode_any W_87290 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87294 : bv 32 := 0xa60fb06f.
Lemma F_87294 : fetch_word Ubsan.M.loaded_segments (0x87294 : word) = Some W_87294.
Proof. vm_refl. Qed.
Lemma D_87294 : decode_any W_87294 = Some (Jal 0 2077280, 4%Z).
Proof. vm_refl. Qed.

Definition W_87298 : bv 32 := 0x00ba0633.
Lemma F_87298 : fetch_word Ubsan.M.loaded_segments (0x87298 : word) = Some W_87298.
Proof. vm_refl. Qed.
Lemma D_87298 : decode_any W_87298 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8729c : bv 32 := 0x00061463.
Lemma F_8729c : fetch_word Ubsan.M.loaded_segments (0x8729c : word) = Some W_8729c.
Proof. vm_refl. Qed.
Lemma D_8729c : decode_any W_8729c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_872a0 : bv 32 := 0xa54fb06f.
Lemma F_872a0 : fetch_word Ubsan.M.loaded_segments (0x872a0 : word) = Some W_872a0.
Proof. vm_refl. Qed.
Lemma D_872a0 : decode_any W_872a0 = Some (Jal 0 2077268, 4%Z).
Proof. vm_refl. Qed.

Definition W_872a4 : bv 32 := 0x01a63633.
Lemma F_872a4 : fetch_word Ubsan.M.loaded_segments (0x872a4 : word) = Some W_872a4.
Proof. vm_refl. Qed.
Lemma D_872a4 : decode_any W_872a4 = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_872a8 : bv 32 := 0x07813803.
Lemma F_872a8 : fetch_word Ubsan.M.loaded_segments (0x872a8 : word) = Some W_872a8.
Proof. vm_refl. Qed.
Lemma D_872a8 : decode_any W_872a8 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_872ac : bv 32 := 0x01064633.
Lemma F_872ac : fetch_word Ubsan.M.loaded_segments (0x872ac : word) = Some W_872ac.
Proof. vm_refl. Qed.
Lemma D_872ac : decode_any W_872ac = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_872b0 : bv 32 := 0x00164613.
Lemma F_872b0 : fetch_word Ubsan.M.loaded_segments (0x872b0 : word) = Some W_872b0.
Proof. vm_refl. Qed.
Lemma D_872b0 : decode_any W_872b0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_872b4 : bv 32 := 0x00061463.
Lemma F_872b4 : fetch_word Ubsan.M.loaded_segments (0x872b4 : word) = Some W_872b4.
Proof. vm_refl. Qed.
Lemma D_872b4 : decode_any W_872b4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_872b8 : bv 32 := 0xa3cfb06f.
Lemma F_872b8 : fetch_word Ubsan.M.loaded_segments (0x872b8 : word) = Some W_872b8.
Proof. vm_refl. Qed.
Lemma D_872b8 : decode_any W_872b8 = Some (Jal 0 2077244, 4%Z).
Proof. vm_refl. Qed.

Definition W_872bc : bv 32 := 0x0014849b.
Lemma F_872bc : fetch_word Ubsan.M.loaded_segments (0x872bc : word) = Some W_872bc.
Proof. vm_refl. Qed.
Lemma D_872bc : decode_any W_872bc = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_872c0 : bv 32 := 0x00d585b3.
Lemma F_872c0 : fetch_word Ubsan.M.loaded_segments (0x872c0 : word) = Some W_872c0.
Proof. vm_refl. Qed.
Lemma D_872c0 : decode_any W_872c0 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_872c4 : bv 32 := 0x007c8cb3.
Lemma F_872c4 : fetch_word Ubsan.M.loaded_segments (0x872c4 : word) = Some W_872c4.
Proof. vm_refl. Qed.
Lemma D_872c4 : decode_any W_872c4 = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_872c8 : bv 32 := 0x000a8813.
Lemma F_872c8 : fetch_word Ubsan.M.loaded_segments (0x872c8 : word) = Some W_872c8.
Proof. vm_refl. Qed.
Lemma D_872c8 : decode_any W_872c8 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_872cc : bv 32 := 0xf00494e3.
Lemma F_872cc : fetch_word Ubsan.M.loaded_segments (0x872cc : word) = Some W_872cc.
Proof. vm_refl. Qed.
Lemma D_872cc : decode_any W_872cc = Some (Branch BC_NE 9 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_872d0 : bv 32 := 0x02013583.
Lemma F_872d0 : fetch_word Ubsan.M.loaded_segments (0x872d0 : word) = Some W_872d0.
Proof. vm_refl. Qed.
Lemma D_872d0 : decode_any W_872d0 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_872d4 : bv 32 := 0x16059e63.
Lemma F_872d4 : fetch_word Ubsan.M.loaded_segments (0x872d4 : word) = Some W_872d4.
Proof. vm_refl. Qed.
Lemma D_872d4 : decode_any W_872d4 = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_872d8 : bv 32 := 0xffffc693.
Lemma F_872d8 : fetch_word Ubsan.M.loaded_segments (0x872d8 : word) = Some W_872d8.
Proof. vm_refl. Qed.
Lemma D_872d8 : decode_any W_872d8 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_872dc : bv 32 := 0x00271293.
Lemma F_872dc : fetch_word Ubsan.M.loaded_segments (0x872dc : word) = Some W_872dc.
Proof. vm_refl. Qed.
Lemma D_872dc : decode_any W_872dc = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_872e0 : bv 32 := 0x05813383.
Lemma F_872e0 : fetch_word Ubsan.M.loaded_segments (0x872e0 : word) = Some W_872e0.
Proof. vm_refl. Qed.
Lemma D_872e0 : decode_any W_872e0 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_872e4 : bv 32 := 0x00239393.
Lemma F_872e4 : fetch_word Ubsan.M.loaded_segments (0x872e4 : word) = Some W_872e4.
Proof. vm_refl. Qed.
Lemma D_872e4 : decode_any W_872e4 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_872e8 : bv 32 := 0x00337613.
Lemma F_872e8 : fetch_word Ubsan.M.loaded_segments (0x872e8 : word) = Some W_872e8.
Proof. vm_refl. Qed.
Lemma D_872e8 : decode_any W_872e8 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_872ec : bv 32 := 0x00397793.
Lemma F_872ec : fetch_word Ubsan.M.loaded_segments (0x872ec : word) = Some W_872ec.
Proof. vm_refl. Qed.
Lemma D_872ec : decode_any W_872ec = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_872f0 : bv 32 := 0x07013a03.
Lemma F_872f0 : fetch_word Ubsan.M.loaded_segments (0x872f0 : word) = Some W_872f0.
Proof. vm_refl. Qed.
Lemma D_872f0 : decode_any W_872f0 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_872f4 : bv 32 := 0x002a1a13.
Lemma F_872f4 : fetch_word Ubsan.M.loaded_segments (0x872f4 : word) = Some W_872f4.
Proof. vm_refl. Qed.
Lemma D_872f4 : decode_any W_872f4 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_872f8 : bv 32 := 0x00072b93.
Lemma F_872f8 : fetch_word Ubsan.M.loaded_segments (0x872f8 : word) = Some W_872f8.
Proof. vm_refl. Qed.
Lemma D_872f8 : decode_any W_872f8 = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_872fc : bv 32 := 0x02000c93.
Lemma F_872fc : fetch_word Ubsan.M.loaded_segments (0x872fc : word) = Some W_872fc.
Proof. vm_refl. Qed.
Lemma D_872fc : decode_any W_872fc = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_87300 : bv 32 := 0xffb00d13.
Lemma F_87300 : fetch_word Ubsan.M.loaded_segments (0x87300 : word) = Some W_87300.
Proof. vm_refl. Qed.
Lemma D_87300 : decode_any W_87300 = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_87304 : bv 32 := 0x0017b793.
Lemma F_87304 : fetch_word Ubsan.M.loaded_segments (0x87304 : word) = Some W_87304.
Proof. vm_refl. Qed.
Lemma D_87304 : decode_any W_87304 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87308 : bv 32 := 0x02f13023.
Lemma F_87308 : fetch_word Ubsan.M.loaded_segments (0x87308 : word) = Some W_87308.
Proof. vm_refl. Qed.
Lemma D_87308 : decode_any W_87308 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8730c : bv 32 := 0x00163613.
Lemma F_8730c : fetch_word Ubsan.M.loaded_segments (0x8730c : word) = Some W_8730c.
Proof. vm_refl. Qed.
Lemma D_8730c : decode_any W_8730c = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87310 : bv 32 := 0x00c13823.
Lemma F_87310 : fetch_word Ubsan.M.loaded_segments (0x87310 : word) = Some W_87310.
Proof. vm_refl. Qed.
Lemma D_87310 : decode_any W_87310 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87314 : bv 32 := 0x01f00993.
Lemma F_87314 : fetch_word Ubsan.M.loaded_segments (0x87314 : word) = Some W_87314.
Proof. vm_refl. Qed.
Lemma D_87314 : decode_any W_87314 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_87318 : bv 32 := 0x00030c13.
Lemma F_87318 : fetch_word Ubsan.M.loaded_segments (0x87318 : word) = Some W_87318.
Proof. vm_refl. Qed.
Lemma D_87318 : decode_any W_87318 = Some (OpImm ALU_ADD 24 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8731c : bv 32 := 0x00090b13.
Lemma F_8731c : fetch_word Ubsan.M.loaded_segments (0x8731c : word) = Some W_8731c.
Proof. vm_refl. Qed.
Lemma D_8731c : decode_any W_8731c = Some (OpImm ALU_ADD 22 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87320 : bv 32 := 0x07013603.
Lemma F_87320 : fetch_word Ubsan.M.loaded_segments (0x87320 : word) = Some W_87320.
Proof. vm_refl. Qed.
Lemma D_87320 : decode_any W_87320 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_87324 : bv 32 := 0x0a060e63.
Lemma F_87324 : fetch_word Ubsan.M.loaded_segments (0x87324 : word) = Some W_87324.
Proof. vm_refl. Qed.
Lemma D_87324 : decode_any W_87324 = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_87328 : bv 32 := 0x00000d93.
Lemma F_87328 : fetch_word Ubsan.M.loaded_segments (0x87328 : word) = Some W_87328.
Proof. vm_refl. Qed.
Lemma D_87328 : decode_any W_87328 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8732c : bv 32 := 0x00603833.
Lemma F_8732c : fetch_word Ubsan.M.loaded_segments (0x8732c : word) = Some W_8732c.
Proof. vm_refl. Qed.
Lemma D_8732c : decode_any W_8732c = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_87330 : bv 32 := 0x01203e33.
Lemma F_87330 : fetch_word Ubsan.M.loaded_segments (0x87330 : word) = Some W_87330.
Proof. vm_refl. Qed.
Lemma D_87330 : decode_any W_87330 = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_87334 : bv 32 := 0x01013603.
Lemma F_87334 : fetch_word Ubsan.M.loaded_segments (0x87334 : word) = Some W_87334.
Proof. vm_refl. Qed.
Lemma D_87334 : decode_any W_87334 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87338 : bv 32 := 0x010674b3.
Lemma F_87338 : fetch_word Ubsan.M.loaded_segments (0x87338 : word) = Some W_87338.
Proof. vm_refl. Qed.
Lemma D_87338 : decode_any W_87338 = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8733c : bv 32 := 0x02013603.
Lemma F_8733c : fetch_word Ubsan.M.loaded_segments (0x8733c : word) = Some W_8733c.
Proof. vm_refl. Qed.
Lemma D_8733c : decode_any W_8733c = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_87340 : bv 32 := 0x01c67ab3.
Lemma F_87340 : fetch_word Ubsan.M.loaded_segments (0x87340 : word) = Some W_87340.
Proof. vm_refl. Qed.
Lemma D_87340 : decode_any W_87340 = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_87344 : bv 32 := 0x01bc0633.
Lemma F_87344 : fetch_word Ubsan.M.loaded_segments (0x87344 : word) = Some W_87344.
Proof. vm_refl. Qed.
Lemma D_87344 : decode_any W_87344 = Some (Op ALU_ADD 12 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_87348 : bv 32 := 0x00667463.
Lemma F_87348 : fetch_word Ubsan.M.loaded_segments (0x87348 : word) = Some W_87348.
Proof. vm_refl. Qed.
Lemma D_87348 : decode_any W_87348 = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8734c : bv 32 := 0x9a8fb06f.
Lemma F_8734c : fetch_word Ubsan.M.loaded_segments (0x8734c : word) = Some W_8734c.
Proof. vm_refl. Qed.
Lemma D_8734c : decode_any W_8734c = Some (Jal 0 2077096, 4%Z).
Proof. vm_refl. Qed.

Definition W_87350 : bv 32 := 0x00163613.
Lemma F_87350 : fetch_word Ubsan.M.loaded_segments (0x87350 : word) = Some W_87350.
Proof. vm_refl. Qed.
Lemma D_87350 : decode_any W_87350 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87354 : bv 32 := 0x00c84633.
Lemma F_87354 : fetch_word Ubsan.M.loaded_segments (0x87354 : word) = Some W_87354.
Proof. vm_refl. Qed.
Lemma D_87354 : decode_any W_87354 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_87358 : bv 32 := 0x00061463.
Lemma F_87358 : fetch_word Ubsan.M.loaded_segments (0x87358 : word) = Some W_87358.
Proof. vm_refl. Qed.
Lemma D_87358 : decode_any W_87358 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8735c : bv 32 := 0x998fb06f.
Lemma F_8735c : fetch_word Ubsan.M.loaded_segments (0x8735c : word) = Some W_8735c.
Proof. vm_refl. Qed.
Lemma D_8735c : decode_any W_8735c = Some (Jal 0 2077080, 4%Z).
Proof. vm_refl. Qed.

Definition W_87360 : bv 32 := 0x00049463.
Lemma F_87360 : fetch_word Ubsan.M.loaded_segments (0x87360 : word) = Some W_87360.
Proof. vm_refl. Qed.
Lemma D_87360 : decode_any W_87360 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87364 : bv 32 := 0x990fb06f.
Lemma F_87364 : fetch_word Ubsan.M.loaded_segments (0x87364 : word) = Some W_87364.
Proof. vm_refl. Qed.
Lemma D_87364 : decode_any W_87364 = Some (Jal 0 2077072, 4%Z).
Proof. vm_refl. Qed.

Definition W_87368 : bv 32 := 0x019f1463.
Lemma F_87368 : fetch_word Ubsan.M.loaded_segments (0x87368 : word) = Some W_87368.
Proof. vm_refl. Qed.
Lemma D_87368 : decode_any W_87368 = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8736c : bv 32 := 0x988fb06f.
Lemma F_8736c : fetch_word Ubsan.M.loaded_segments (0x8736c : word) = Some W_8736c.
Proof. vm_refl. Qed.
Lemma D_8736c : decode_any W_8736c = Some (Jal 0 2077064, 4%Z).
Proof. vm_refl. Qed.

Definition W_87370 : bv 32 := 0x01b30633.
Lemma F_87370 : fetch_word Ubsan.M.loaded_segments (0x87370 : word) = Some W_87370.
Proof. vm_refl. Qed.
Lemma D_87370 : decode_any W_87370 = Some (Op ALU_ADD 12 6 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_87374 : bv 32 := 0x00cd7463.
Lemma F_87374 : fetch_word Ubsan.M.loaded_segments (0x87374 : word) = Some W_87374.
Proof. vm_refl. Qed.
Lemma D_87374 : decode_any W_87374 = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87378 : bv 32 := 0x97cfb06f.
Lemma F_87378 : fetch_word Ubsan.M.loaded_segments (0x87378 : word) = Some W_87378.
Proof. vm_refl. Qed.
Lemma D_87378 : decode_any W_87378 = Some (Jal 0 2077052, 4%Z).
Proof. vm_refl. Qed.

Definition W_8737c : bv 32 := 0x0089f463.
Lemma F_8737c : fetch_word Ubsan.M.loaded_segments (0x8737c : word) = Some W_8737c.
Proof. vm_refl. Qed.
Lemma D_8737c : decode_any W_8737c = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87380 : bv 32 := 0x974fb06f.
Lemma F_87380 : fetch_word Ubsan.M.loaded_segments (0x87380 : word) = Some W_87380.
Proof. vm_refl. Qed.
Lemma D_87380 : decode_any W_87380 = Some (Jal 0 2077044, 4%Z).
Proof. vm_refl. Qed.

Definition W_87384 : bv 32 := 0x01bb07b3.
Lemma F_87384 : fetch_word Ubsan.M.loaded_segments (0x87384 : word) = Some W_87384.
Proof. vm_refl. Qed.
Lemma D_87384 : decode_any W_87384 = Some (Op ALU_ADD 15 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_87388 : bv 32 := 0x0127f463.
Lemma F_87388 : fetch_word Ubsan.M.loaded_segments (0x87388 : word) = Some W_87388.
Proof. vm_refl. Qed.
Lemma D_87388 : decode_any W_87388 = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8738c : bv 32 := 0x968fb06f.
Lemma F_8738c : fetch_word Ubsan.M.loaded_segments (0x8738c : word) = Some W_8738c.
Proof. vm_refl. Qed.
Lemma D_8738c : decode_any W_8738c = Some (Jal 0 2077032, 4%Z).
Proof. vm_refl. Qed.

Definition W_87390 : bv 32 := 0x0017b793.
Lemma F_87390 : fetch_word Ubsan.M.loaded_segments (0x87390 : word) = Some W_87390.
Proof. vm_refl. Qed.
Lemma D_87390 : decode_any W_87390 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87394 : bv 32 := 0x00fe47b3.
Lemma F_87394 : fetch_word Ubsan.M.loaded_segments (0x87394 : word) = Some W_87394.
Proof. vm_refl. Qed.
Lemma D_87394 : decode_any W_87394 = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_87398 : bv 32 := 0x00079463.
Lemma F_87398 : fetch_word Ubsan.M.loaded_segments (0x87398 : word) = Some W_87398.
Proof. vm_refl. Qed.
Lemma D_87398 : decode_any W_87398 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8739c : bv 32 := 0x958fb06f.
Lemma F_8739c : fetch_word Ubsan.M.loaded_segments (0x8739c : word) = Some W_8739c.
Proof. vm_refl. Qed.
Lemma D_8739c : decode_any W_8739c = Some (Jal 0 2077016, 4%Z).
Proof. vm_refl. Qed.

Definition W_873a0 : bv 32 := 0x000a9463.
Lemma F_873a0 : fetch_word Ubsan.M.loaded_segments (0x873a0 : word) = Some W_873a0.
Proof. vm_refl. Qed.
Lemma D_873a0 : decode_any W_873a0 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_873a4 : bv 32 := 0x950fb06f.
Lemma F_873a4 : fetch_word Ubsan.M.loaded_segments (0x873a4 : word) = Some W_873a4.
Proof. vm_refl. Qed.
Lemma D_873a4 : decode_any W_873a4 = Some (Jal 0 2077008, 4%Z).
Proof. vm_refl. Qed.

Definition W_873a8 : bv 32 := 0x00062783.
Lemma F_873a8 : fetch_word Ubsan.M.loaded_segments (0x873a8 : word) = Some W_873a8.
Proof. vm_refl. Qed.
Lemma D_873a8 : decode_any W_873a8 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_873ac : bv 32 := 0x00462603.
Lemma F_873ac : fetch_word Ubsan.M.loaded_segments (0x873ac : word) = Some W_873ac.
Proof. vm_refl. Qed.
Lemma D_873ac : decode_any W_873ac = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_873b0 : bv 32 := 0x01b908b3.
Lemma F_873b0 : fetch_word Ubsan.M.loaded_segments (0x873b0 : word) = Some W_873b0.
Proof. vm_refl. Qed.
Lemma D_873b0 : decode_any W_873b0 = Some (Op ALU_ADD 17 18 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_873b4 : bv 32 := 0x0008a083.
Lemma F_873b4 : fetch_word Ubsan.M.loaded_segments (0x873b4 : word) = Some W_873b4.
Proof. vm_refl. Qed.
Lemma D_873b4 : decode_any W_873b4 = Some (Load SZ4 true 1 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_873b8 : bv 32 := 0x01d797bb.
Lemma F_873b8 : fetch_word Ubsan.M.loaded_segments (0x873b8 : word) = Some W_873b8.
Proof. vm_refl. Qed.
Lemma D_873b8 : decode_any W_873b8 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_873bc : bv 32 := 0x0086563b.
Lemma F_873bc : fetch_word Ubsan.M.loaded_segments (0x873bc : word) = Some W_873bc.
Proof. vm_refl. Qed.
Lemma D_873bc : decode_any W_873bc = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_873c0 : bv 32 := 0x00d7f7b3.
Lemma F_873c0 : fetch_word Ubsan.M.loaded_segments (0x873c0 : word) = Some W_873c0.
Proof. vm_refl. Qed.
Lemma D_873c0 : decode_any W_873c0 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_873c4 : bv 32 := 0x01f67633.
Lemma F_873c4 : fetch_word Ubsan.M.loaded_segments (0x873c4 : word) = Some W_873c4.
Proof. vm_refl. Qed.
Lemma D_873c4 : decode_any W_873c4 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_873c8 : bv 32 := 0x00f66633.
Lemma F_873c8 : fetch_word Ubsan.M.loaded_segments (0x873c8 : word) = Some W_873c8.
Proof. vm_refl. Qed.
Lemma D_873c8 : decode_any W_873c8 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_873cc : bv 32 := 0xfff64613.
Lemma F_873cc : fetch_word Ubsan.M.loaded_segments (0x873cc : word) = Some W_873cc.
Proof. vm_refl. Qed.
Lemma D_873cc : decode_any W_873cc = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_873d0 : bv 32 := 0x00c0e633.
Lemma F_873d0 : fetch_word Ubsan.M.loaded_segments (0x873d0 : word) = Some W_873d0.
Proof. vm_refl. Qed.
Lemma D_873d0 : decode_any W_873d0 = Some (Op ALU_OR 12 1 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_873d4 : bv 32 := 0x004d8d93.
Lemma F_873d4 : fetch_word Ubsan.M.loaded_segments (0x873d4 : word) = Some W_873d4.
Proof. vm_refl. Qed.
Lemma D_873d4 : decode_any W_873d4 = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_873d8 : bv 32 := 0x00c8a023.
Lemma F_873d8 : fetch_word Ubsan.M.loaded_segments (0x873d8 : word) = Some W_873d8.
Proof. vm_refl. Qed.
Lemma D_873d8 : decode_any W_873d8 = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_873dc : bv 32 := 0xf7ba14e3.
Lemma F_873dc : fetch_word Ubsan.M.loaded_segments (0x873dc : word) = Some W_873dc.
Proof. vm_refl. Qed.
Lemma D_873dc : decode_any W_873dc = Some (Branch BC_NE 20 27 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_873e0 : bv 32 := 0x00590633.
Lemma F_873e0 : fetch_word Ubsan.M.loaded_segments (0x873e0 : word) = Some W_873e0.
Proof. vm_refl. Qed.
Lemma D_873e0 : decode_any W_873e0 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_873e4 : bv 32 := 0x012037b3.
Lemma F_873e4 : fetch_word Ubsan.M.loaded_segments (0x873e4 : word) = Some W_873e4.
Proof. vm_refl. Qed.
Lemma D_873e4 : decode_any W_873e4 = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_873e8 : bv 32 := 0x00163813.
Lemma F_873e8 : fetch_word Ubsan.M.loaded_segments (0x873e8 : word) = Some W_873e8.
Proof. vm_refl. Qed.
Lemma D_873e8 : decode_any W_873e8 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_873ec : bv 32 := 0x01079463.
Lemma F_873ec : fetch_word Ubsan.M.loaded_segments (0x873ec : word) = Some W_873ec.
Proof. vm_refl. Qed.
Lemma D_873ec : decode_any W_873ec = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_873f0 : bv 32 := 0x904fb06f.
Lemma F_873f0 : fetch_word Ubsan.M.loaded_segments (0x873f0 : word) = Some W_873f0.
Proof. vm_refl. Qed.
Lemma D_873f0 : decode_any W_873f0 = Some (Jal 0 2076932, 4%Z).
Proof. vm_refl. Qed.

Definition W_873f4 : bv 32 := 0x01263633.
Lemma F_873f4 : fetch_word Ubsan.M.loaded_segments (0x873f4 : word) = Some W_873f4.
Proof. vm_refl. Qed.
Lemma D_873f4 : decode_any W_873f4 = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_873f8 : bv 32 := 0x01764633.
Lemma F_873f8 : fetch_word Ubsan.M.loaded_segments (0x873f8 : word) = Some W_873f8.
Proof. vm_refl. Qed.
Lemma D_873f8 : decode_any W_873f8 = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_873fc : bv 32 := 0x00164613.
Lemma F_873fc : fetch_word Ubsan.M.loaded_segments (0x873fc : word) = Some W_873fc.
Proof. vm_refl. Qed.
Lemma D_873fc : decode_any W_873fc = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87400 : bv 32 := 0x00061463.
Lemma F_87400 : fetch_word Ubsan.M.loaded_segments (0x87400 : word) = Some W_87400.
Proof. vm_refl. Qed.
Lemma D_87400 : decode_any W_87400 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87404 : bv 32 := 0x8f0fb06f.
Lemma F_87404 : fetch_word Ubsan.M.loaded_segments (0x87404 : word) = Some W_87404.
Proof. vm_refl. Qed.
Lemma D_87404 : decode_any W_87404 = Some (Jal 0 2076912, 4%Z).
Proof. vm_refl. Qed.

Definition W_87408 : bv 32 := 0x00638633.
Lemma F_87408 : fetch_word Ubsan.M.loaded_segments (0x87408 : word) = Some W_87408.
Proof. vm_refl. Qed.
Lemma D_87408 : decode_any W_87408 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8740c : bv 32 := 0x006037b3.
Lemma F_8740c : fetch_word Ubsan.M.loaded_segments (0x8740c : word) = Some W_8740c.
Proof. vm_refl. Qed.
Lemma D_8740c : decode_any W_8740c = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_87410 : bv 32 := 0x00163813.
Lemma F_87410 : fetch_word Ubsan.M.loaded_segments (0x87410 : word) = Some W_87410.
Proof. vm_refl. Qed.
Lemma D_87410 : decode_any W_87410 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87414 : bv 32 := 0x01079463.
Lemma F_87414 : fetch_word Ubsan.M.loaded_segments (0x87414 : word) = Some W_87414.
Proof. vm_refl. Qed.
Lemma D_87414 : decode_any W_87414 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87418 : bv 32 := 0x8dcfb06f.
Lemma F_87418 : fetch_word Ubsan.M.loaded_segments (0x87418 : word) = Some W_87418.
Proof. vm_refl. Qed.
Lemma D_87418 : decode_any W_87418 = Some (Jal 0 2076892, 4%Z).
Proof. vm_refl. Qed.

Definition W_8741c : bv 32 := 0x006637b3.
Lemma F_8741c : fetch_word Ubsan.M.loaded_segments (0x8741c : word) = Some W_8741c.
Proof. vm_refl. Qed.
Lemma D_8741c : decode_any W_8741c = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_87420 : bv 32 := 0x07813803.
Lemma F_87420 : fetch_word Ubsan.M.loaded_segments (0x87420 : word) = Some W_87420.
Proof. vm_refl. Qed.
Lemma D_87420 : decode_any W_87420 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_87424 : bv 32 := 0x0107c7b3.
Lemma F_87424 : fetch_word Ubsan.M.loaded_segments (0x87424 : word) = Some W_87424.
Proof. vm_refl. Qed.
Lemma D_87424 : decode_any W_87424 = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87428 : bv 32 := 0x0017c793.
Lemma F_87428 : fetch_word Ubsan.M.loaded_segments (0x87428 : word) = Some W_87428.
Proof. vm_refl. Qed.
Lemma D_87428 : decode_any W_87428 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8742c : bv 32 := 0x00079463.
Lemma F_8742c : fetch_word Ubsan.M.loaded_segments (0x8742c : word) = Some W_8742c.
Proof. vm_refl. Qed.
Lemma D_8742c : decode_any W_8742c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87430 : bv 32 := 0x8c4fb06f.
Lemma F_87430 : fetch_word Ubsan.M.loaded_segments (0x87430 : word) = Some W_87430.
Proof. vm_refl. Qed.
Lemma D_87430 : decode_any W_87430 = Some (Jal 0 2076868, 4%Z).
Proof. vm_refl. Qed.

Definition W_87434 : bv 32 := 0x00590933.
Lemma F_87434 : fetch_word Ubsan.M.loaded_segments (0x87434 : word) = Some W_87434.
Proof. vm_refl. Qed.
Lemma D_87434 : decode_any W_87434 = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_87438 : bv 32 := 0x0015859b.
Lemma F_87438 : fetch_word Ubsan.M.loaded_segments (0x87438 : word) = Some W_87438.
Proof. vm_refl. Qed.
Lemma D_87438 : decode_any W_87438 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8743c : bv 32 := 0x005b0b33.
Lemma F_8743c : fetch_word Ubsan.M.loaded_segments (0x8743c : word) = Some W_8743c.
Proof. vm_refl. Qed.
Lemma D_8743c : decode_any W_8743c = Some (Op ALU_ADD 22 22 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_87440 : bv 32 := 0x007c0c33.
Lemma F_87440 : fetch_word Ubsan.M.loaded_segments (0x87440 : word) = Some W_87440.
Proof. vm_refl. Qed.
Lemma D_87440 : decode_any W_87440 = Some (Op ALU_ADD 24 24 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_87444 : bv 32 := 0x00060313.
Lemma F_87444 : fetch_word Ubsan.M.loaded_segments (0x87444 : word) = Some W_87444.
Proof. vm_refl. Qed.
Lemma D_87444 : decode_any W_87444 = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87448 : bv 32 := 0x08013603.
Lemma F_87448 : fetch_word Ubsan.M.loaded_segments (0x87448 : word) = Some W_87448.
Proof. vm_refl. Qed.
Lemma D_87448 : decode_any W_87448 = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_8744c : bv 32 := 0xecc59ae3.
Lemma F_8744c : fetch_word Ubsan.M.loaded_segments (0x8744c : word) = Some W_8744c.
Proof. vm_refl. Qed.
Lemma D_8744c : decode_any W_8744c = Some (Branch BC_NE 11 12 7892, 4%Z).
Proof. vm_refl. Qed.

Definition W_87450 : bv 32 := 0x01813583.
Lemma F_87450 : fetch_word Ubsan.M.loaded_segments (0x87450 : word) = Some W_87450.
Proof. vm_refl. Qed.
Lemma D_87450 : decode_any W_87450 = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_87454 : bv 32 := 0x16059263.
Lemma F_87454 : fetch_word Ubsan.M.loaded_segments (0x87454 : word) = Some W_87454.
Proof. vm_refl. Qed.
Lemma D_87454 : decode_any W_87454 = Some (Branch BC_NE 11 0 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_87458 : bv 32 := 0x06813583.
Lemma F_87458 : fetch_word Ubsan.M.loaded_segments (0x87458 : word) = Some W_87458.
Proof. vm_refl. Qed.
Lemma D_87458 : decode_any W_87458 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_8745c : bv 32 := 0x0035f593.
Lemma F_8745c : fetch_word Ubsan.M.loaded_segments (0x8745c : word) = Some W_8745c.
Proof. vm_refl. Qed.
Lemma D_8745c : decode_any W_8745c = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_87460 : bv 32 := 0x00058463.
Lemma F_87460 : fetch_word Ubsan.M.loaded_segments (0x87460 : word) = Some W_87460.
Proof. vm_refl. Qed.
Lemma D_87460 : decode_any W_87460 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87464 : bv 32 := 0x890fb06f.
Lemma F_87464 : fetch_word Ubsan.M.loaded_segments (0x87464 : word) = Some W_87464.
Proof. vm_refl. Qed.
Lemma D_87464 : decode_any W_87464 = Some (Jal 0 2076816, 4%Z).
Proof. vm_refl. Qed.

Definition W_87468 : bv 32 := 0xffffc613.
Lemma F_87468 : fetch_word Ubsan.M.loaded_segments (0x87468 : word) = Some W_87468.
Proof. vm_refl. Qed.
Lemma D_87468 : decode_any W_87468 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8746c : bv 32 := 0x06013683.
Lemma F_8746c : fetch_word Ubsan.M.loaded_segments (0x8746c : word) = Some W_8746c.
Proof. vm_refl. Qed.
Lemma D_8746c : decode_any W_8746c = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_87470 : bv 32 := 0xfff6c693.
Lemma F_87470 : fetch_word Ubsan.M.loaded_segments (0x87470 : word) = Some W_87470.
Proof. vm_refl. Qed.
Lemma D_87470 : decode_any W_87470 = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87474 : bv 32 := 0x00271793.
Lemma F_87474 : fetch_word Ubsan.M.loaded_segments (0x87474 : word) = Some W_87474.
Proof. vm_refl. Qed.
Lemma D_87474 : decode_any W_87474 = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_87478 : bv 32 := 0x05813303.
Lemma F_87478 : fetch_word Ubsan.M.loaded_segments (0x87478 : word) = Some W_87478.
Proof. vm_refl. Qed.
Lemma D_87478 : decode_any W_87478 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8747c : bv 32 := 0x00231313.
Lemma F_8747c : fetch_word Ubsan.M.loaded_segments (0x8747c : word) = Some W_8747c.
Proof. vm_refl. Qed.
Lemma D_8747c : decode_any W_8747c = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_87480 : bv 32 := 0x00357893.
Lemma F_87480 : fetch_word Ubsan.M.loaded_segments (0x87480 : word) = Some W_87480.
Proof. vm_refl. Qed.
Lemma D_87480 : decode_any W_87480 = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_87484 : bv 32 := 0x05013903.
Lemma F_87484 : fetch_word Ubsan.M.loaded_segments (0x87484 : word) = Some W_87484.
Proof. vm_refl. Qed.
Lemma D_87484 : decode_any W_87484 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_87488 : bv 32 := 0x02813803.
Lemma F_87488 : fetch_word Ubsan.M.loaded_segments (0x87488 : word) = Some W_87488.
Proof. vm_refl. Qed.
Lemma D_87488 : decode_any W_87488 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8748c : bv 32 := 0x412804bb.
Lemma F_8748c : fetch_word Ubsan.M.loaded_segments (0x8748c : word) = Some W_8748c.
Proof. vm_refl. Qed.
Lemma D_8748c : decode_any W_8748c = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_87490 : bv 32 := 0x03813383.
Lemma F_87490 : fetch_word Ubsan.M.loaded_segments (0x87490 : word) = Some W_87490.
Proof. vm_refl. Qed.
Lemma D_87490 : decode_any W_87490 = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_87494 : bv 32 := 0x03013803.
Lemma F_87494 : fetch_word Ubsan.M.loaded_segments (0x87494 : word) = Some W_87494.
Proof. vm_refl. Qed.
Lemma D_87494 : decode_any W_87494 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_87498 : bv 32 := 0x007803b3.
Lemma F_87498 : fetch_word Ubsan.M.loaded_segments (0x87498 : word) = Some W_87498.
Proof. vm_refl. Qed.
Lemma D_87498 : decode_any W_87498 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8749c : bv 32 := 0x04813283.
Lemma F_8749c : fetch_word Ubsan.M.loaded_segments (0x8749c : word) = Some W_8749c.
Proof. vm_refl. Qed.
Lemma D_8749c : decode_any W_8749c = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_874a0 : bv 32 := 0x43f2d813.
Lemma F_874a0 : fetch_word Ubsan.M.loaded_segments (0x874a0 : word) = Some W_874a0.
Proof. vm_refl. Qed.
Lemma D_874a0 : decode_any W_874a0 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_874a4 : bv 32 := 0x00587e33.
Lemma F_874a4 : fetch_word Ubsan.M.loaded_segments (0x874a4 : word) = Some W_874a4.
Proof. vm_refl. Qed.
Lemma D_874a4 : decode_any W_874a4 = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_874a8 : bv 32 := 0x02000813.
Lemma F_874a8 : fetch_word Ubsan.M.loaded_segments (0x874a8 : word) = Some W_874a8.
Proof. vm_refl. Qed.
Lemma D_874a8 : decode_any W_874a8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_874ac : bv 32 := 0x00813283.
Lemma F_874ac : fetch_word Ubsan.M.loaded_segments (0x874ac : word) = Some W_874ac.
Proof. vm_refl. Qed.
Lemma D_874ac : decode_any W_874ac = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_874b0 : bv 32 := 0x0012f293.
Lemma F_874b0 : fetch_word Ubsan.M.loaded_segments (0x874b0 : word) = Some W_874b0.
Proof. vm_refl. Qed.
Lemma D_874b0 : decode_any W_874b0 = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_874b4 : bv 32 := 0x00072713.
Lemma F_874b4 : fetch_word Ubsan.M.loaded_segments (0x874b4 : word) = Some W_874b4.
Proof. vm_refl. Qed.
Lemma D_874b4 : decode_any W_874b4 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_874b8 : bv 32 := 0x01c38e33.
Lemma F_874b8 : fetch_word Ubsan.M.loaded_segments (0x874b8 : word) = Some W_874b8.
Proof. vm_refl. Qed.
Lemma D_874b8 : decode_any W_874b8 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_874bc : bv 32 := 0xffb00393.
Lemma F_874bc : fetch_word Ubsan.M.loaded_segments (0x874bc : word) = Some W_874bc.
Proof. vm_refl. Qed.
Lemma D_874bc : decode_any W_874bc = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_874c0 : bv 32 := 0x412e093b.
Lemma F_874c0 : fetch_word Ubsan.M.loaded_segments (0x874c0 : word) = Some W_874c0.
Proof. vm_refl. Qed.
Lemma D_874c0 : decode_any W_874c0 = Some (Op32 ALU_SUB 18 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_874c4 : bv 32 := 0x06813e03.
Lemma F_874c4 : fetch_word Ubsan.M.loaded_segments (0x874c4 : word) = Some W_874c4.
Proof. vm_refl. Qed.
Lemma D_874c4 : decode_any W_874c4 = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_874c8 : bv 32 := 0x006e0e33.
Lemma F_874c8 : fetch_word Ubsan.M.loaded_segments (0x874c8 : word) = Some W_874c8.
Proof. vm_refl. Qed.
Lemma D_874c8 : decode_any W_874c8 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_874cc : bv 32 := 0x04013983.
Lemma F_874cc : fetch_word Ubsan.M.loaded_segments (0x874cc : word) = Some W_874cc.
Proof. vm_refl. Qed.
Lemma D_874cc : decode_any W_874cc = Some (Load SZ8 true 19 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_874d0 : bv 32 := 0x4139093b.
Lemma F_874d0 : fetch_word Ubsan.M.loaded_segments (0x874d0 : word) = Some W_874d0.
Proof. vm_refl. Qed.
Lemma D_874d0 : decode_any W_874d0 = Some (Op32 ALU_SUB 18 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_874d4 : bv 32 := 0x43f95993.
Lemma F_874d4 : fetch_word Ubsan.M.loaded_segments (0x874d4 : word) = Some W_874d4.
Proof. vm_refl. Qed.
Lemma D_874d4 : decode_any W_874d4 = Some (ShiftImm ALU_SRA 19 18 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_874d8 : bv 32 := 0x0129f933.
Lemma F_874d8 : fetch_word Ubsan.M.loaded_segments (0x874d8 : word) = Some W_874d8.
Proof. vm_refl. Qed.
Lemma D_874d8 : decode_any W_874d8 = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_874dc : bv 32 := 0x412484bb.
Lemma F_874dc : fetch_word Ubsan.M.loaded_segments (0x874dc : word) = Some W_874dc.
Proof. vm_refl. Qed.
Lemma D_874dc : decode_any W_874dc = Some (Op32 ALU_SUB 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_874e0 : bv 32 := 0x01f00993.
Lemma F_874e0 : fetch_word Ubsan.M.loaded_segments (0x874e0 : word) = Some W_874e0.
Proof. vm_refl. Qed.
Lemma D_874e0 : decode_any W_874e0 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_874e4 : bv 32 := 0x00050a13.
Lemma F_874e4 : fetch_word Ubsan.M.loaded_segments (0x874e4 : word) = Some W_874e4.
Proof. vm_refl. Qed.
Lemma D_874e4 : decode_any W_874e4 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_874e8 : bv 32 := 0x06813a83.
Lemma F_874e8 : fetch_word Ubsan.M.loaded_segments (0x874e8 : word) = Some W_874e8.
Proof. vm_refl. Qed.
Lemma D_874e8 : decode_any W_874e8 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_874ec : bv 32 := 0x00ba8ab3.
Lemma F_874ec : fetch_word Ubsan.M.loaded_segments (0x874ec : word) = Some W_874ec.
Proof. vm_refl. Qed.
Lemma D_874ec : decode_any W_874ec = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_874f0 : bv 32 := 0x000a9463.
Lemma F_874f0 : fetch_word Ubsan.M.loaded_segments (0x874f0 : word) = Some W_874f0.
Proof. vm_refl. Qed.
Lemma D_874f0 : decode_any W_874f0 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_874f4 : bv 32 := 0x800fb06f.
Lemma F_874f4 : fetch_word Ubsan.M.loaded_segments (0x874f4 : word) = Some W_874f4.
Proof. vm_refl. Qed.
Lemma D_874f4 : decode_any W_874f4 = Some (Jal 0 2076672, 4%Z).
Proof. vm_refl. Qed.

Definition W_874f8 : bv 32 := 0x010f1463.
Lemma F_874f8 : fetch_word Ubsan.M.loaded_segments (0x874f8 : word) = Some W_874f8.
Proof. vm_refl. Qed.
Lemma D_874f8 : decode_any W_874f8 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_874fc : bv 32 := 0xff9fa06f.
Lemma F_874fc : fetch_word Ubsan.M.loaded_segments (0x874fc : word) = Some W_874fc.
Proof. vm_refl. Qed.
Lemma D_874fc : decode_any W_874fc = Some (Jal 0 2076664, 4%Z).
Proof. vm_refl. Qed.

Definition W_87500 : bv 32 := 0x000aa903.
Lemma F_87500 : fetch_word Ubsan.M.loaded_segments (0x87500 : word) = Some W_87500.
Proof. vm_refl. Qed.
Lemma D_87500 : decode_any W_87500 = Some (Load SZ4 true 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87504 : bv 32 := 0x01d91b3b.
Lemma F_87504 : fetch_word Ubsan.M.loaded_segments (0x87504 : word) = Some W_87504.
Proof. vm_refl. Qed.
Lemma D_87504 : decode_any W_87504 = Some (Op32 ALU_SLL 22 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_87508 : bv 32 := 0x02029463.
Lemma F_87508 : fetch_word Ubsan.M.loaded_segments (0x87508 : word) = Some W_87508.
Proof. vm_refl. Qed.
Lemma D_87508 : decode_any W_87508 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8750c : bv 32 := 0x0153f463.
Lemma F_8750c : fetch_word Ubsan.M.loaded_segments (0x8750c : word) = Some W_8750c.
Proof. vm_refl. Qed.
Lemma D_8750c : decode_any W_8750c = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87510 : bv 32 := 0xfe5fa06f.
Lemma F_87510 : fetch_word Ubsan.M.loaded_segments (0x87510 : word) = Some W_87510.
Proof. vm_refl. Qed.
Lemma D_87510 : decode_any W_87510 = Some (Jal 0 2076644, 4%Z).
Proof. vm_refl. Qed.

Definition W_87514 : bv 32 := 0x0089f463.
Lemma F_87514 : fetch_word Ubsan.M.loaded_segments (0x87514 : word) = Some W_87514.
Proof. vm_refl. Qed.
Lemma D_87514 : decode_any W_87514 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87518 : bv 32 := 0xfddfa06f.
Lemma F_87518 : fetch_word Ubsan.M.loaded_segments (0x87518 : word) = Some W_87518.
Proof. vm_refl. Qed.
Lemma D_87518 : decode_any W_87518 = Some (Jal 0 2076636, 4%Z).
Proof. vm_refl. Qed.

Definition W_8751c : bv 32 := 0x004aa903.
Lemma F_8751c : fetch_word Ubsan.M.loaded_segments (0x8751c : word) = Some W_8751c.
Proof. vm_refl. Qed.
Lemma D_8751c : decode_any W_8751c = Some (Load SZ4 true 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_87520 : bv 32 := 0x00cb7b33.
Lemma F_87520 : fetch_word Ubsan.M.loaded_segments (0x87520 : word) = Some W_87520.
Proof. vm_refl. Qed.
Lemma D_87520 : decode_any W_87520 = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_87524 : bv 32 := 0x0089593b.
Lemma F_87524 : fetch_word Ubsan.M.loaded_segments (0x87524 : word) = Some W_87524.
Proof. vm_refl. Qed.
Lemma D_87524 : decode_any W_87524 = Some (Op32 ALU_SRL 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87528 : bv 32 := 0x01f97933.
Lemma F_87528 : fetch_word Ubsan.M.loaded_segments (0x87528 : word) = Some W_87528.
Proof. vm_refl. Qed.
Lemma D_87528 : decode_any W_87528 = Some (Op ALU_AND 18 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_8752c : bv 32 := 0x01696b33.
Lemma F_8752c : fetch_word Ubsan.M.loaded_segments (0x8752c : word) = Some W_8752c.
Proof. vm_refl. Qed.
Lemma D_8752c : decode_any W_8752c = Some (Op ALU_OR 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_87530 : bv 32 := 0x00088463.
Lemma F_87530 : fetch_word Ubsan.M.loaded_segments (0x87530 : word) = Some W_87530.
Proof. vm_refl. Qed.
Lemma D_87530 : decode_any W_87530 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87534 : bv 32 := 0xfc1fa06f.
Lemma F_87534 : fetch_word Ubsan.M.loaded_segments (0x87534 : word) = Some W_87534.
Proof. vm_refl. Qed.
Lemma D_87534 : decode_any W_87534 = Some (Jal 0 2076608, 4%Z).
Proof. vm_refl. Qed.

Definition W_87538 : bv 32 := 0x00051463.
Lemma F_87538 : fetch_word Ubsan.M.loaded_segments (0x87538 : word) = Some W_87538.
Proof. vm_refl. Qed.
Lemma D_87538 : decode_any W_87538 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8753c : bv 32 := 0xfb9fa06f.
Lemma F_8753c : fetch_word Ubsan.M.loaded_segments (0x8753c : word) = Some W_8753c.
Proof. vm_refl. Qed.
Lemma D_8753c : decode_any W_8753c = Some (Jal 0 2076600, 4%Z).
Proof. vm_refl. Qed.

Definition W_87540 : bv 32 := 0x00052903.
Lemma F_87540 : fetch_word Ubsan.M.loaded_segments (0x87540 : word) = Some W_87540.
Proof. vm_refl. Qed.
Lemma D_87540 : decode_any W_87540 = Some (Load SZ4 true 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87544 : bv 32 := 0xfffb4b13.
Lemma F_87544 : fetch_word Ubsan.M.loaded_segments (0x87544 : word) = Some W_87544.
Proof. vm_refl. Qed.
Lemma D_87544 : decode_any W_87544 = Some (OpImm ALU_XOR 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87548 : bv 32 := 0x00d97bb3.
Lemma F_87548 : fetch_word Ubsan.M.loaded_segments (0x87548 : word) = Some W_87548.
Proof. vm_refl. Qed.
Lemma D_87548 : decode_any W_87548 = Some (Op ALU_AND 23 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8754c : bv 32 := 0x01696933.
Lemma F_8754c : fetch_word Ubsan.M.loaded_segments (0x8754c : word) = Some W_8754c.
Proof. vm_refl. Qed.
Lemma D_8754c : decode_any W_8754c = Some (Op ALU_OR 18 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_87550 : bv 32 := 0x06013b03.
Lemma F_87550 : fetch_word Ubsan.M.loaded_segments (0x87550 : word) = Some W_87550.
Proof. vm_refl. Qed.
Lemma D_87550 : decode_any W_87550 = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_87554 : bv 32 := 0x01697933.
Lemma F_87554 : fetch_word Ubsan.M.loaded_segments (0x87554 : word) = Some W_87554.
Proof. vm_refl. Qed.
Lemma D_87554 : decode_any W_87554 = Some (Op ALU_AND 18 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_87558 : bv 32 := 0x01796933.
Lemma F_87558 : fetch_word Ubsan.M.loaded_segments (0x87558 : word) = Some W_87558.
Proof. vm_refl. Qed.
Lemma D_87558 : decode_any W_87558 = Some (Op ALU_OR 18 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8755c : bv 32 := 0x01478b33.
Lemma F_8755c : fetch_word Ubsan.M.loaded_segments (0x8755c : word) = Some W_8755c.
Proof. vm_refl. Qed.
Lemma D_8755c : decode_any W_8755c = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_87560 : bv 32 := 0x01252023.
Lemma F_87560 : fetch_word Ubsan.M.loaded_segments (0x87560 : word) = Some W_87560.
Proof. vm_refl. Qed.
Lemma D_87560 : decode_any W_87560 = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87564 : bv 32 := 0x000b1463.
Lemma F_87564 : fetch_word Ubsan.M.loaded_segments (0x87564 : word) = Some W_87564.
Proof. vm_refl. Qed.
Lemma D_87564 : decode_any W_87564 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87568 : bv 32 := 0xf8dfa06f.
Lemma F_87568 : fetch_word Ubsan.M.loaded_segments (0x87568 : word) = Some W_87568.
Proof. vm_refl. Qed.
Lemma D_87568 : decode_any W_87568 = Some (Jal 0 2076556, 4%Z).
Proof. vm_refl. Qed.

Definition W_8756c : bv 32 := 0x014b3933.
Lemma F_8756c : fetch_word Ubsan.M.loaded_segments (0x8756c : word) = Some W_8756c.
Proof. vm_refl. Qed.
Lemma D_8756c : decode_any W_8756c = Some (Op ALU_SLTU 18 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_87570 : bv 32 := 0x00e94933.
Lemma F_87570 : fetch_word Ubsan.M.loaded_segments (0x87570 : word) = Some W_87570.
Proof. vm_refl. Qed.
Lemma D_87570 : decode_any W_87570 = Some (Op ALU_XOR 18 18 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_87574 : bv 32 := 0x00194913.
Lemma F_87574 : fetch_word Ubsan.M.loaded_segments (0x87574 : word) = Some W_87574.
Proof. vm_refl. Qed.
Lemma D_87574 : decode_any W_87574 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87578 : bv 32 := 0x00091463.
Lemma F_87578 : fetch_word Ubsan.M.loaded_segments (0x87578 : word) = Some W_87578.
Proof. vm_refl. Qed.
Lemma D_87578 : decode_any W_87578 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8757c : bv 32 := 0xf79fa06f.
Lemma F_8757c : fetch_word Ubsan.M.loaded_segments (0x8757c : word) = Some W_8757c.
Proof. vm_refl. Qed.
Lemma D_8757c : decode_any W_8757c = Some (Jal 0 2076536, 4%Z).
Proof. vm_refl. Qed.

Definition W_87580 : bv 32 := 0x00be0a33.
Lemma F_87580 : fetch_word Ubsan.M.loaded_segments (0x87580 : word) = Some W_87580.
Proof. vm_refl. Qed.
Lemma D_87580 : decode_any W_87580 = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_87584 : bv 32 := 0x000a1463.
Lemma F_87584 : fetch_word Ubsan.M.loaded_segments (0x87584 : word) = Some W_87584.
Proof. vm_refl. Qed.
Lemma D_87584 : decode_any W_87584 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87588 : bv 32 := 0xf6dfa06f.
Lemma F_87588 : fetch_word Ubsan.M.loaded_segments (0x87588 : word) = Some W_87588.
Proof. vm_refl. Qed.
Lemma D_87588 : decode_any W_87588 = Some (Jal 0 2076524, 4%Z).
Proof. vm_refl. Qed.

Definition W_8758c : bv 32 := 0x015a3933.
Lemma F_8758c : fetch_word Ubsan.M.loaded_segments (0x8758c : word) = Some W_8758c.
Proof. vm_refl. Qed.
Lemma D_8758c : decode_any W_8758c = Some (Op ALU_SLTU 18 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_87590 : bv 32 := 0x07813a03.
Lemma F_87590 : fetch_word Ubsan.M.loaded_segments (0x87590 : word) = Some W_87590.
Proof. vm_refl. Qed.
Lemma D_87590 : decode_any W_87590 = Some (Load SZ8 true 20 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_87594 : bv 32 := 0x01494933.
Lemma F_87594 : fetch_word Ubsan.M.loaded_segments (0x87594 : word) = Some W_87594.
Proof. vm_refl. Qed.
Lemma D_87594 : decode_any W_87594 = Some (Op ALU_XOR 18 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_87598 : bv 32 := 0x00194913.
Lemma F_87598 : fetch_word Ubsan.M.loaded_segments (0x87598 : word) = Some W_87598.
Proof. vm_refl. Qed.
Lemma D_87598 : decode_any W_87598 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8759c : bv 32 := 0x00091463.
Lemma F_8759c : fetch_word Ubsan.M.loaded_segments (0x8759c : word) = Some W_8759c.
Proof. vm_refl. Qed.
Lemma D_8759c : decode_any W_8759c = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_875a0 : bv 32 := 0xf55fa06f.
Lemma F_875a0 : fetch_word Ubsan.M.loaded_segments (0x875a0 : word) = Some W_875a0.
Proof. vm_refl. Qed.
Lemma D_875a0 : decode_any W_875a0 = Some (Jal 0 2076500, 4%Z).
Proof. vm_refl. Qed.

Definition W_875a4 : bv 32 := 0x0014849b.
Lemma F_875a4 : fetch_word Ubsan.M.loaded_segments (0x875a4 : word) = Some W_875a4.
Proof. vm_refl. Qed.
Lemma D_875a4 : decode_any W_875a4 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_875a8 : bv 32 := 0x006585b3.
Lemma F_875a8 : fetch_word Ubsan.M.loaded_segments (0x875a8 : word) = Some W_875a8.
Proof. vm_refl. Qed.
Lemma D_875a8 : decode_any W_875a8 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_875ac : bv 32 := 0x00f50533.
Lemma F_875ac : fetch_word Ubsan.M.loaded_segments (0x875ac : word) = Some W_875ac.
Proof. vm_refl. Qed.
Lemma D_875ac : decode_any W_875ac = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_875b0 : bv 32 := 0x000b0a13.
Lemma F_875b0 : fetch_word Ubsan.M.loaded_segments (0x875b0 : word) = Some W_875b0.
Proof. vm_refl. Qed.
Lemma D_875b0 : decode_any W_875b0 = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_875b4 : bv 32 := 0xf2049ae3.
Lemma F_875b4 : fetch_word Ubsan.M.loaded_segments (0x875b4 : word) = Some W_875b4.
Proof. vm_refl. Qed.
Lemma D_875b4 : decode_any W_875b4 = Some (Branch BC_NE 9 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_875b8 : bv 32 := 0x0e813083.
Lemma F_875b8 : fetch_word Ubsan.M.loaded_segments (0x875b8 : word) = Some W_875b8.
Proof. vm_refl. Qed.
Lemma D_875b8 : decode_any W_875b8 = Some (Load SZ8 true 1 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_875bc : bv 32 := 0x0e013403.
Lemma F_875bc : fetch_word Ubsan.M.loaded_segments (0x875bc : word) = Some W_875bc.
Proof. vm_refl. Qed.
Lemma D_875bc : decode_any W_875bc = Some (Load SZ8 true 8 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_875c0 : bv 32 := 0x0d813483.
Lemma F_875c0 : fetch_word Ubsan.M.loaded_segments (0x875c0 : word) = Some W_875c0.
Proof. vm_refl. Qed.
Lemma D_875c0 : decode_any W_875c0 = Some (Load SZ8 true 9 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_875c4 : bv 32 := 0x0d013903.
Lemma F_875c4 : fetch_word Ubsan.M.loaded_segments (0x875c4 : word) = Some W_875c4.
Proof. vm_refl. Qed.
Lemma D_875c4 : decode_any W_875c4 = Some (Load SZ8 true 18 2 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_875c8 : bv 32 := 0x0c813983.
Lemma F_875c8 : fetch_word Ubsan.M.loaded_segments (0x875c8 : word) = Some W_875c8.
Proof. vm_refl. Qed.
Lemma D_875c8 : decode_any W_875c8 = Some (Load SZ8 true 19 2 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_875cc : bv 32 := 0x0c013a03.
Lemma F_875cc : fetch_word Ubsan.M.loaded_segments (0x875cc : word) = Some W_875cc.
Proof. vm_refl. Qed.
Lemma D_875cc : decode_any W_875cc = Some (Load SZ8 true 20 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_875d0 : bv 32 := 0x0b813a83.
Lemma F_875d0 : fetch_word Ubsan.M.loaded_segments (0x875d0 : word) = Some W_875d0.
Proof. vm_refl. Qed.
Lemma D_875d0 : decode_any W_875d0 = Some (Load SZ8 true 21 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_875d4 : bv 32 := 0x0b013b03.
Lemma F_875d4 : fetch_word Ubsan.M.loaded_segments (0x875d4 : word) = Some W_875d4.
Proof. vm_refl. Qed.
Lemma D_875d4 : decode_any W_875d4 = Some (Load SZ8 true 22 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_875d8 : bv 32 := 0x0a813b83.
Lemma F_875d8 : fetch_word Ubsan.M.loaded_segments (0x875d8 : word) = Some W_875d8.
Proof. vm_refl. Qed.
Lemma D_875d8 : decode_any W_875d8 = Some (Load SZ8 true 23 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_875dc : bv 32 := 0x0a013c03.
Lemma F_875dc : fetch_word Ubsan.M.loaded_segments (0x875dc : word) = Some W_875dc.
Proof. vm_refl. Qed.
Lemma D_875dc : decode_any W_875dc = Some (Load SZ8 true 24 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_875e0 : bv 32 := 0x09813c83.
Lemma F_875e0 : fetch_word Ubsan.M.loaded_segments (0x875e0 : word) = Some W_875e0.
Proof. vm_refl. Qed.
Lemma D_875e0 : decode_any W_875e0 = Some (Load SZ8 true 25 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_875e4 : bv 32 := 0x09013d03.
Lemma F_875e4 : fetch_word Ubsan.M.loaded_segments (0x875e4 : word) = Some W_875e4.
Proof. vm_refl. Qed.
Lemma D_875e4 : decode_any W_875e4 = Some (Load SZ8 true 26 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_875e8 : bv 32 := 0x08813d83.
Lemma F_875e8 : fetch_word Ubsan.M.loaded_segments (0x875e8 : word) = Some W_875e8.
Proof. vm_refl. Qed.
Lemma D_875e8 : decode_any W_875e8 = Some (Load SZ8 true 27 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_875ec : bv 32 := 0x0f010113.
Lemma F_875ec : fetch_word Ubsan.M.loaded_segments (0x875ec : word) = Some W_875ec.
Proof. vm_refl. Qed.
Lemma D_875ec : decode_any W_875ec = Some (OpImm ALU_ADD 2 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_875f0 : bv 32 := 0x00008067.
Lemma F_875f0 : fetch_word Ubsan.M.loaded_segments (0x875f0 : word) = Some W_875f0.
Proof. vm_refl. Qed.
Lemma D_875f0 : decode_any W_875f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
