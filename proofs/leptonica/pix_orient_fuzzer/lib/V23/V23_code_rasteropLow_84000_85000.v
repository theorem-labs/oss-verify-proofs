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

Definition W_84000 : bv 32 := 0x00031463.
Lemma F_84000 : fetch_word Ubsan.M.loaded_segments (0x84000 : word) = Some W_84000.
Proof. vm_refl. Qed.
Lemma D_84000 : decode_any W_84000 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84004 : bv 32 := 0xcf0fe06f.
Lemma F_84004 : fetch_word Ubsan.M.loaded_segments (0x84004 : word) = Some W_84004.
Proof. vm_refl. Qed.
Lemma D_84004 : decode_any W_84004 = Some (Jal 0 2090224, 4%Z).
Proof. vm_refl. Qed.

Definition W_84008 : bv 32 := 0x00b80333.
Lemma F_84008 : fetch_word Ubsan.M.loaded_segments (0x84008 : word) = Some W_84008.
Proof. vm_refl. Qed.
Lemma D_84008 : decode_any W_84008 = Some (Op ALU_ADD 6 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8400c : bv 32 := 0x00031463.
Lemma F_8400c : fetch_word Ubsan.M.loaded_segments (0x8400c : word) = Some W_8400c.
Proof. vm_refl. Qed.
Lemma D_8400c : decode_any W_8400c = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84010 : bv 32 := 0xce4fe06f.
Lemma F_84010 : fetch_word Ubsan.M.loaded_segments (0x84010 : word) = Some W_84010.
Proof. vm_refl. Qed.
Lemma D_84010 : decode_any W_84010 = Some (Jal 0 2090212, 4%Z).
Proof. vm_refl. Qed.

Definition W_84014 : bv 32 := 0x01833333.
Lemma F_84014 : fetch_word Ubsan.M.loaded_segments (0x84014 : word) = Some W_84014.
Proof. vm_refl. Qed.
Lemma D_84014 : decode_any W_84014 = Some (Op ALU_SLTU 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_84018 : bv 32 := 0x01c34333.
Lemma F_84018 : fetch_word Ubsan.M.loaded_segments (0x84018 : word) = Some W_84018.
Proof. vm_refl. Qed.
Lemma D_84018 : decode_any W_84018 = Some (Op ALU_XOR 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8401c : bv 32 := 0x00134313.
Lemma F_8401c : fetch_word Ubsan.M.loaded_segments (0x8401c : word) = Some W_8401c.
Proof. vm_refl. Qed.
Lemma D_8401c : decode_any W_8401c = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84020 : bv 32 := 0x00031463.
Lemma F_84020 : fetch_word Ubsan.M.loaded_segments (0x84020 : word) = Some W_84020.
Proof. vm_refl. Qed.
Lemma D_84020 : decode_any W_84020 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84024 : bv 32 := 0xcd0fe06f.
Lemma F_84024 : fetch_word Ubsan.M.loaded_segments (0x84024 : word) = Some W_84024.
Proof. vm_refl. Qed.
Lemma D_84024 : decode_any W_84024 = Some (Jal 0 2090192, 4%Z).
Proof. vm_refl. Qed.

Definition W_84028 : bv 32 := 0x0013839b.
Lemma F_84028 : fetch_word Ubsan.M.loaded_segments (0x84028 : word) = Some W_84028.
Proof. vm_refl. Qed.
Lemma D_84028 : decode_any W_84028 = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8402c : bv 32 := 0x011585b3.
Lemma F_8402c : fetch_word Ubsan.M.loaded_segments (0x8402c : word) = Some W_8402c.
Proof. vm_refl. Qed.
Lemma D_8402c : decode_any W_8402c = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84030 : bv 32 := 0x00da0a33.
Lemma F_84030 : fetch_word Ubsan.M.loaded_segments (0x84030 : word) = Some W_84030.
Proof. vm_refl. Qed.
Lemma D_84030 : decode_any W_84030 = Some (Op ALU_ADD 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84034 : bv 32 := 0x000c8993.
Lemma F_84034 : fetch_word Ubsan.M.loaded_segments (0x84034 : word) = Some W_84034.
Proof. vm_refl. Qed.
Lemma D_84034 : decode_any W_84034 = Some (OpImm ALU_ADD 19 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84038 : bv 32 := 0xf6039ee3.
Lemma F_84038 : fetch_word Ubsan.M.loaded_segments (0x84038 : word) = Some W_84038.
Proof. vm_refl. Qed.
Lemma D_84038 : decode_any W_84038 = Some (Branch BC_NE 7 0 8060, 4%Z).
Proof. vm_refl. Qed.

Definition W_8403c : bv 32 := 0x100b1e63.
Lemma F_8403c : fetch_word Ubsan.M.loaded_segments (0x8403c : word) = Some W_8403c.
Proof. vm_refl. Qed.
Lemma D_8403c : decode_any W_8403c = Some (Branch BC_NE 22 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_84040 : bv 32 := 0x00000593.
Lemma F_84040 : fetch_word Ubsan.M.loaded_segments (0x84040 : word) = Some W_84040.
Proof. vm_refl. Qed.
Lemma D_84040 : decode_any W_84040 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84044 : bv 32 := 0x00271613.
Lemma F_84044 : fetch_word Ubsan.M.loaded_segments (0x84044 : word) = Some W_84044.
Proof. vm_refl. Qed.
Lemma D_84044 : decode_any W_84044 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84048 : bv 32 := 0x05813303.
Lemma F_84048 : fetch_word Ubsan.M.loaded_segments (0x84048 : word) = Some W_84048.
Proof. vm_refl. Qed.
Lemma D_84048 : decode_any W_84048 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8404c : bv 32 := 0x00231693.
Lemma F_8404c : fetch_word Ubsan.M.loaded_segments (0x8404c : word) = Some W_8404c.
Proof. vm_refl. Qed.
Lemma D_8404c : decode_any W_8404c = Some (ShiftImm ALU_SLL 13 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84050 : bv 32 := 0x00397793.
Lemma F_84050 : fetch_word Ubsan.M.loaded_segments (0x84050 : word) = Some W_84050.
Proof. vm_refl. Qed.
Lemma D_84050 : decode_any W_84050 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84054 : bv 32 := 0x00347813.
Lemma F_84054 : fetch_word Ubsan.M.loaded_segments (0x84054 : word) = Some W_84054.
Proof. vm_refl. Qed.
Lemma D_84054 : decode_any W_84054 = Some (OpImm ALU_AND 16 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84058 : bv 32 := 0x002f9893.
Lemma F_84058 : fetch_word Ubsan.M.loaded_segments (0x84058 : word) = Some W_84058.
Proof. vm_refl. Qed.
Lemma D_84058 : decode_any W_84058 = Some (ShiftImm ALU_SLL 17 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8405c : bv 32 := 0x00072293.
Lemma F_8405c : fetch_word Ubsan.M.loaded_segments (0x8405c : word) = Some W_8405c.
Proof. vm_refl. Qed.
Lemma D_8405c : decode_any W_8405c = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84060 : bv 32 := 0x00032393.
Lemma F_84060 : fetch_word Ubsan.M.loaded_segments (0x84060 : word) = Some W_84060.
Proof. vm_refl. Qed.
Lemma D_84060 : decode_any W_84060 = Some (OpImm ALU_SLT 7 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84064 : bv 32 := 0x00183993.
Lemma F_84064 : fetch_word Ubsan.M.loaded_segments (0x84064 : word) = Some W_84064.
Proof. vm_refl. Qed.
Lemma D_84064 : decode_any W_84064 = Some (OpImm ALU_SLTU 19 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84068 : bv 32 := 0x0017ba13.
Lemma F_84068 : fetch_word Ubsan.M.loaded_segments (0x84068 : word) = Some W_84068.
Proof. vm_refl. Qed.
Lemma D_84068 : decode_any W_84068 = Some (OpImm ALU_SLTU 20 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8406c : bv 32 := 0x00090e13.
Lemma F_8406c : fetch_word Ubsan.M.loaded_segments (0x8406c : word) = Some W_8406c.
Proof. vm_refl. Qed.
Lemma D_8406c : decode_any W_8406c = Some (OpImm ALU_ADD 28 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84070 : bv 32 := 0x00040a93.
Lemma F_84070 : fetch_word Ubsan.M.loaded_segments (0x84070 : word) = Some W_84070.
Proof. vm_refl. Qed.
Lemma D_84070 : decode_any W_84070 = Some (OpImm ALU_ADD 21 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84074 : bv 32 := 0x060f8c63.
Lemma F_84074 : fetch_word Ubsan.M.loaded_segments (0x84074 : word) = Some W_84074.
Proof. vm_refl. Qed.
Lemma D_84074 : decode_any W_84074 = Some (Branch BC_EQ 31 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84078 : bv 32 := 0x00000793.
Lemma F_84078 : fetch_word Ubsan.M.loaded_segments (0x84078 : word) = Some W_84078.
Proof. vm_refl. Qed.
Lemma D_84078 : decode_any W_84078 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8407c : bv 32 := 0x01203833.
Lemma F_8407c : fetch_word Ubsan.M.loaded_segments (0x8407c : word) = Some W_8407c.
Proof. vm_refl. Qed.
Lemma D_8407c : decode_any W_8407c = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84080 : bv 32 := 0x00803b33.
Lemma F_84080 : fetch_word Ubsan.M.loaded_segments (0x84080 : word) = Some W_84080.
Proof. vm_refl. Qed.
Lemma D_84080 : decode_any W_84080 = Some (Op ALU_SLTU 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84084 : bv 32 := 0x010a7bb3.
Lemma F_84084 : fetch_word Ubsan.M.loaded_segments (0x84084 : word) = Some W_84084.
Proof. vm_refl. Qed.
Lemma D_84084 : decode_any W_84084 = Some (Op ALU_AND 23 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84088 : bv 32 := 0x0169fc33.
Lemma F_84088 : fetch_word Ubsan.M.loaded_segments (0x84088 : word) = Some W_84088.
Proof. vm_refl. Qed.
Lemma D_84088 : decode_any W_84088 = Some (Op ALU_AND 24 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8408c : bv 32 := 0x00fe0333.
Lemma F_8408c : fetch_word Ubsan.M.loaded_segments (0x8408c : word) = Some W_8408c.
Proof. vm_refl. Qed.
Lemma D_8408c : decode_any W_8408c = Some (Op ALU_ADD 6 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84090 : bv 32 := 0x01237463.
Lemma F_84090 : fetch_word Ubsan.M.loaded_segments (0x84090 : word) = Some W_84090.
Proof. vm_refl. Qed.
Lemma D_84090 : decode_any W_84090 = Some (Branch BC_GEU 6 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84094 : bv 32 := 0xc60fe06f.
Lemma F_84094 : fetch_word Ubsan.M.loaded_segments (0x84094 : word) = Some W_84094.
Proof. vm_refl. Qed.
Lemma D_84094 : decode_any W_84094 = Some (Jal 0 2090080, 4%Z).
Proof. vm_refl. Qed.

Definition W_84098 : bv 32 := 0x00133313.
Lemma F_84098 : fetch_word Ubsan.M.loaded_segments (0x84098 : word) = Some W_84098.
Proof. vm_refl. Qed.
Lemma D_84098 : decode_any W_84098 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8409c : bv 32 := 0x00684333.
Lemma F_8409c : fetch_word Ubsan.M.loaded_segments (0x8409c : word) = Some W_8409c.
Proof. vm_refl. Qed.
Lemma D_8409c : decode_any W_8409c = Some (Op ALU_XOR 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_840a0 : bv 32 := 0x00031463.
Lemma F_840a0 : fetch_word Ubsan.M.loaded_segments (0x840a0 : word) = Some W_840a0.
Proof. vm_refl. Qed.
Lemma D_840a0 : decode_any W_840a0 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840a4 : bv 32 := 0xc50fe06f.
Lemma F_840a4 : fetch_word Ubsan.M.loaded_segments (0x840a4 : word) = Some W_840a4.
Proof. vm_refl. Qed.
Lemma D_840a4 : decode_any W_840a4 = Some (Jal 0 2090064, 4%Z).
Proof. vm_refl. Qed.

Definition W_840a8 : bv 32 := 0x000b9463.
Lemma F_840a8 : fetch_word Ubsan.M.loaded_segments (0x840a8 : word) = Some W_840a8.
Proof. vm_refl. Qed.
Lemma D_840a8 : decode_any W_840a8 = Some (Branch BC_NE 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840ac : bv 32 := 0xc48fe06f.
Lemma F_840ac : fetch_word Ubsan.M.loaded_segments (0x840ac : word) = Some W_840ac.
Proof. vm_refl. Qed.
Lemma D_840ac : decode_any W_840ac = Some (Jal 0 2090056, 4%Z).
Proof. vm_refl. Qed.

Definition W_840b0 : bv 32 := 0x00fa8333.
Lemma F_840b0 : fetch_word Ubsan.M.loaded_segments (0x840b0 : word) = Some W_840b0.
Proof. vm_refl. Qed.
Lemma D_840b0 : decode_any W_840b0 = Some (Op ALU_ADD 6 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_840b4 : bv 32 := 0x00837463.
Lemma F_840b4 : fetch_word Ubsan.M.loaded_segments (0x840b4 : word) = Some W_840b4.
Proof. vm_refl. Qed.
Lemma D_840b4 : decode_any W_840b4 = Some (Branch BC_GEU 6 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840b8 : bv 32 := 0xc3cfe06f.
Lemma F_840b8 : fetch_word Ubsan.M.loaded_segments (0x840b8 : word) = Some W_840b8.
Proof. vm_refl. Qed.
Lemma D_840b8 : decode_any W_840b8 = Some (Jal 0 2090044, 4%Z).
Proof. vm_refl. Qed.

Definition W_840bc : bv 32 := 0x00133313.
Lemma F_840bc : fetch_word Ubsan.M.loaded_segments (0x840bc : word) = Some W_840bc.
Proof. vm_refl. Qed.
Lemma D_840bc : decode_any W_840bc = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_840c0 : bv 32 := 0x006b4333.
Lemma F_840c0 : fetch_word Ubsan.M.loaded_segments (0x840c0 : word) = Some W_840c0.
Proof. vm_refl. Qed.
Lemma D_840c0 : decode_any W_840c0 = Some (Op ALU_XOR 6 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_840c4 : bv 32 := 0x00031463.
Lemma F_840c4 : fetch_word Ubsan.M.loaded_segments (0x840c4 : word) = Some W_840c4.
Proof. vm_refl. Qed.
Lemma D_840c4 : decode_any W_840c4 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840c8 : bv 32 := 0xc2cfe06f.
Lemma F_840c8 : fetch_word Ubsan.M.loaded_segments (0x840c8 : word) = Some W_840c8.
Proof. vm_refl. Qed.
Lemma D_840c8 : decode_any W_840c8 = Some (Jal 0 2090028, 4%Z).
Proof. vm_refl. Qed.

Definition W_840cc : bv 32 := 0x000c1463.
Lemma F_840cc : fetch_word Ubsan.M.loaded_segments (0x840cc : word) = Some W_840cc.
Proof. vm_refl. Qed.
Lemma D_840cc : decode_any W_840cc = Some (Branch BC_NE 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840d0 : bv 32 := 0xc24fe06f.
Lemma F_840d0 : fetch_word Ubsan.M.loaded_segments (0x840d0 : word) = Some W_840d0.
Proof. vm_refl. Qed.
Lemma D_840d0 : decode_any W_840d0 = Some (Jal 0 2090020, 4%Z).
Proof. vm_refl. Qed.

Definition W_840d4 : bv 32 := 0x00f90333.
Lemma F_840d4 : fetch_word Ubsan.M.loaded_segments (0x840d4 : word) = Some W_840d4.
Proof. vm_refl. Qed.
Lemma D_840d4 : decode_any W_840d4 = Some (Op ALU_ADD 6 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_840d8 : bv 32 := 0x00032303.
Lemma F_840d8 : fetch_word Ubsan.M.loaded_segments (0x840d8 : word) = Some W_840d8.
Proof. vm_refl. Qed.
Lemma D_840d8 : decode_any W_840d8 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_840dc : bv 32 := 0x00f40cb3.
Lemma F_840dc : fetch_word Ubsan.M.loaded_segments (0x840dc : word) = Some W_840dc.
Proof. vm_refl. Qed.
Lemma D_840dc : decode_any W_840dc = Some (Op ALU_ADD 25 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_840e0 : bv 32 := 0x00478793.
Lemma F_840e0 : fetch_word Ubsan.M.loaded_segments (0x840e0 : word) = Some W_840e0.
Proof. vm_refl. Qed.
Lemma D_840e0 : decode_any W_840e0 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_840e4 : bv 32 := 0x006ca023.
Lemma F_840e4 : fetch_word Ubsan.M.loaded_segments (0x840e4 : word) = Some W_840e4.
Proof. vm_refl. Qed.
Lemma D_840e4 : decode_any W_840e4 = Some (Store SZ4 25 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_840e8 : bv 32 := 0xfaf892e3.
Lemma F_840e8 : fetch_word Ubsan.M.loaded_segments (0x840e8 : word) = Some W_840e8.
Proof. vm_refl. Qed.
Lemma D_840e8 : decode_any W_840e8 = Some (Branch BC_NE 17 15 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_840ec : bv 32 := 0x00c407b3.
Lemma F_840ec : fetch_word Ubsan.M.loaded_segments (0x840ec : word) = Some W_840ec.
Proof. vm_refl. Qed.
Lemma D_840ec : decode_any W_840ec = Some (Op ALU_ADD 15 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_840f0 : bv 32 := 0x00803833.
Lemma F_840f0 : fetch_word Ubsan.M.loaded_segments (0x840f0 : word) = Some W_840f0.
Proof. vm_refl. Qed.
Lemma D_840f0 : decode_any W_840f0 = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840f4 : bv 32 := 0x0017b313.
Lemma F_840f4 : fetch_word Ubsan.M.loaded_segments (0x840f4 : word) = Some W_840f4.
Proof. vm_refl. Qed.
Lemma D_840f4 : decode_any W_840f4 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_840f8 : bv 32 := 0x00681463.
Lemma F_840f8 : fetch_word Ubsan.M.loaded_segments (0x840f8 : word) = Some W_840f8.
Proof. vm_refl. Qed.
Lemma D_840f8 : decode_any W_840f8 = Some (Branch BC_NE 16 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_840fc : bv 32 := 0xbf8fe06f.
Lemma F_840fc : fetch_word Ubsan.M.loaded_segments (0x840fc : word) = Some W_840fc.
Proof. vm_refl. Qed.
Lemma D_840fc : decode_any W_840fc = Some (Jal 0 2089976, 4%Z).
Proof. vm_refl. Qed.

Definition W_84100 : bv 32 := 0x0087b7b3.
Lemma F_84100 : fetch_word Ubsan.M.loaded_segments (0x84100 : word) = Some W_84100.
Proof. vm_refl. Qed.
Lemma D_84100 : decode_any W_84100 = Some (Op ALU_SLTU 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84104 : bv 32 := 0x0057c7b3.
Lemma F_84104 : fetch_word Ubsan.M.loaded_segments (0x84104 : word) = Some W_84104.
Proof. vm_refl. Qed.
Lemma D_84104 : decode_any W_84104 = Some (Op ALU_XOR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84108 : bv 32 := 0x0017c793.
Lemma F_84108 : fetch_word Ubsan.M.loaded_segments (0x84108 : word) = Some W_84108.
Proof. vm_refl. Qed.
Lemma D_84108 : decode_any W_84108 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8410c : bv 32 := 0x00079463.
Lemma F_8410c : fetch_word Ubsan.M.loaded_segments (0x8410c : word) = Some W_8410c.
Proof. vm_refl. Qed.
Lemma D_8410c : decode_any W_8410c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84110 : bv 32 := 0xbe4fe06f.
Lemma F_84110 : fetch_word Ubsan.M.loaded_segments (0x84110 : word) = Some W_84110.
Proof. vm_refl. Qed.
Lemma D_84110 : decode_any W_84110 = Some (Jal 0 2089956, 4%Z).
Proof. vm_refl. Qed.

Definition W_84114 : bv 32 := 0x012687b3.
Lemma F_84114 : fetch_word Ubsan.M.loaded_segments (0x84114 : word) = Some W_84114.
Proof. vm_refl. Qed.
Lemma D_84114 : decode_any W_84114 = Some (Op ALU_ADD 15 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84118 : bv 32 := 0x01203833.
Lemma F_84118 : fetch_word Ubsan.M.loaded_segments (0x84118 : word) = Some W_84118.
Proof. vm_refl. Qed.
Lemma D_84118 : decode_any W_84118 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8411c : bv 32 := 0x0017b313.
Lemma F_8411c : fetch_word Ubsan.M.loaded_segments (0x8411c : word) = Some W_8411c.
Proof. vm_refl. Qed.
Lemma D_8411c : decode_any W_8411c = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84120 : bv 32 := 0x00681463.
Lemma F_84120 : fetch_word Ubsan.M.loaded_segments (0x84120 : word) = Some W_84120.
Proof. vm_refl. Qed.
Lemma D_84120 : decode_any W_84120 = Some (Branch BC_NE 16 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84124 : bv 32 := 0xbd0fe06f.
Lemma F_84124 : fetch_word Ubsan.M.loaded_segments (0x84124 : word) = Some W_84124.
Proof. vm_refl. Qed.
Lemma D_84124 : decode_any W_84124 = Some (Jal 0 2089936, 4%Z).
Proof. vm_refl. Qed.

Definition W_84128 : bv 32 := 0x0127b833.
Lemma F_84128 : fetch_word Ubsan.M.loaded_segments (0x84128 : word) = Some W_84128.
Proof. vm_refl. Qed.
Lemma D_84128 : decode_any W_84128 = Some (Op ALU_SLTU 16 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8412c : bv 32 := 0x00784833.
Lemma F_8412c : fetch_word Ubsan.M.loaded_segments (0x8412c : word) = Some W_8412c.
Proof. vm_refl. Qed.
Lemma D_8412c : decode_any W_8412c = Some (Op ALU_XOR 16 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84130 : bv 32 := 0x00184813.
Lemma F_84130 : fetch_word Ubsan.M.loaded_segments (0x84130 : word) = Some W_84130.
Proof. vm_refl. Qed.
Lemma D_84130 : decode_any W_84130 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84134 : bv 32 := 0x00081463.
Lemma F_84134 : fetch_word Ubsan.M.loaded_segments (0x84134 : word) = Some W_84134.
Proof. vm_refl. Qed.
Lemma D_84134 : decode_any W_84134 = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84138 : bv 32 := 0xbbcfe06f.
Lemma F_84138 : fetch_word Ubsan.M.loaded_segments (0x84138 : word) = Some W_84138.
Proof. vm_refl. Qed.
Lemma D_84138 : decode_any W_84138 = Some (Jal 0 2089916, 4%Z).
Proof. vm_refl. Qed.

Definition W_8413c : bv 32 := 0x00c40433.
Lemma F_8413c : fetch_word Ubsan.M.loaded_segments (0x8413c : word) = Some W_8413c.
Proof. vm_refl. Qed.
Lemma D_8413c : decode_any W_8413c = Some (Op ALU_ADD 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84140 : bv 32 := 0x0015859b.
Lemma F_84140 : fetch_word Ubsan.M.loaded_segments (0x84140 : word) = Some W_84140.
Proof. vm_refl. Qed.
Lemma D_84140 : decode_any W_84140 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84144 : bv 32 := 0x00ca8ab3.
Lemma F_84144 : fetch_word Ubsan.M.loaded_segments (0x84144 : word) = Some W_84144.
Proof. vm_refl. Qed.
Lemma D_84144 : decode_any W_84144 = Some (Op ALU_ADD 21 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84148 : bv 32 := 0x00de0e33.
Lemma F_84148 : fetch_word Ubsan.M.loaded_segments (0x84148 : word) = Some W_84148.
Proof. vm_refl. Qed.
Lemma D_84148 : decode_any W_84148 = Some (Op ALU_ADD 28 28 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8414c : bv 32 := 0x00078913.
Lemma F_8414c : fetch_word Ubsan.M.loaded_segments (0x8414c : word) = Some W_8414c.
Proof. vm_refl. Qed.
Lemma D_8414c : decode_any W_8414c = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84150 : bv 32 := 0x08013783.
Lemma F_84150 : fetch_word Ubsan.M.loaded_segments (0x84150 : word) = Some W_84150.
Proof. vm_refl. Qed.
Lemma D_84150 : decode_any W_84150 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_84154 : bv 32 := 0xf2f590e3.
Lemma F_84154 : fetch_word Ubsan.M.loaded_segments (0x84154 : word) = Some W_84154.
Proof. vm_refl. Qed.
Lemma D_84154 : decode_any W_84154 = Some (Branch BC_NE 11 15 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_84158 : bv 32 := 0x00048463.
Lemma F_84158 : fetch_word Ubsan.M.loaded_segments (0x84158 : word) = Some W_84158.
Proof. vm_refl. Qed.
Lemma D_84158 : decode_any W_84158 = Some (Branch BC_EQ 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8415c : bv 32 := 0x45c0306f.
Lemma F_8415c : fetch_word Ubsan.M.loaded_segments (0x8415c : word) = Some W_8415c.
Proof. vm_refl. Qed.
Lemma D_8415c : decode_any W_8415c = Some (Jal 0 13404, 4%Z).
Proof. vm_refl. Qed.

Definition W_84160 : bv 32 := 0x00357593.
Lemma F_84160 : fetch_word Ubsan.M.loaded_segments (0x84160 : word) = Some W_84160.
Proof. vm_refl. Qed.
Lemma D_84160 : decode_any W_84160 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84164 : bv 32 := 0x00058463.
Lemma F_84164 : fetch_word Ubsan.M.loaded_segments (0x84164 : word) = Some W_84164.
Proof. vm_refl. Qed.
Lemma D_84164 : decode_any W_84164 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84168 : bv 32 := 0xb8cfe06f.
Lemma F_84168 : fetch_word Ubsan.M.loaded_segments (0x84168 : word) = Some W_84168.
Proof. vm_refl. Qed.
Lemma D_84168 : decode_any W_84168 = Some (Jal 0 2089868, 4%Z).
Proof. vm_refl. Qed.

Definition W_8416c : bv 32 := 0xfffec613.
Lemma F_8416c : fetch_word Ubsan.M.loaded_segments (0x8416c : word) = Some W_8416c.
Proof. vm_refl. Qed.
Lemma D_8416c : decode_any W_8416c = Some (OpImm ALU_XOR 12 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84170 : bv 32 := 0x00271693.
Lemma F_84170 : fetch_word Ubsan.M.loaded_segments (0x84170 : word) = Some W_84170.
Proof. vm_refl. Qed.
Lemma D_84170 : decode_any W_84170 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84174 : bv 32 := 0x05813e03.
Lemma F_84174 : fetch_word Ubsan.M.loaded_segments (0x84174 : word) = Some W_84174.
Proof. vm_refl. Qed.
Lemma D_84174 : decode_any W_84174 = Some (Load SZ8 true 28 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84178 : bv 32 := 0x002e1793.
Lemma F_84178 : fetch_word Ubsan.M.loaded_segments (0x84178 : word) = Some W_84178.
Proof. vm_refl. Qed.
Lemma D_84178 : decode_any W_84178 = Some (ShiftImm ALU_SLL 15 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8417c : bv 32 := 0x03813883.
Lemma F_8417c : fetch_word Ubsan.M.loaded_segments (0x8417c : word) = Some W_8417c.
Proof. vm_refl. Qed.
Lemma D_8417c : decode_any W_8417c = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84180 : bv 32 := 0x03013803.
Lemma F_84180 : fetch_word Ubsan.M.loaded_segments (0x84180 : word) = Some W_84180.
Proof. vm_refl. Qed.
Lemma D_84180 : decode_any W_84180 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_84184 : bv 32 := 0x011808b3.
Lemma F_84184 : fetch_word Ubsan.M.loaded_segments (0x84184 : word) = Some W_84184.
Proof. vm_refl. Qed.
Lemma D_84184 : decode_any W_84184 = Some (Op ALU_ADD 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84188 : bv 32 := 0x04813283.
Lemma F_84188 : fetch_word Ubsan.M.loaded_segments (0x84188 : word) = Some W_84188.
Proof. vm_refl. Qed.
Lemma D_84188 : decode_any W_84188 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8418c : bv 32 := 0x43f2d813.
Lemma F_8418c : fetch_word Ubsan.M.loaded_segments (0x8418c : word) = Some W_8418c.
Proof. vm_refl. Qed.
Lemma D_8418c : decode_any W_8418c = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84190 : bv 32 := 0x005872b3.
Lemma F_84190 : fetch_word Ubsan.M.loaded_segments (0x84190 : word) = Some W_84190.
Proof. vm_refl. Qed.
Lemma D_84190 : decode_any W_84190 = Some (Op ALU_AND 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84194 : bv 32 := 0x003f7813.
Lemma F_84194 : fetch_word Ubsan.M.loaded_segments (0x84194 : word) = Some W_84194.
Proof. vm_refl. Qed.
Lemma D_84194 : decode_any W_84194 = Some (OpImm ALU_AND 16 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84198 : bv 32 := 0x05013383.
Lemma F_84198 : fetch_word Ubsan.M.loaded_segments (0x84198 : word) = Some W_84198.
Proof. vm_refl. Qed.
Lemma D_84198 : decode_any W_84198 = Some (Load SZ8 true 7 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8419c : bv 32 := 0x02813303.
Lemma F_8419c : fetch_word Ubsan.M.loaded_segments (0x8419c : word) = Some W_8419c.
Proof. vm_refl. Qed.
Lemma D_8419c : decode_any W_8419c = Some (Load SZ8 true 6 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_841a0 : bv 32 := 0x4073033b.
Lemma F_841a0 : fetch_word Ubsan.M.loaded_segments (0x841a0 : word) = Some W_841a0.
Proof. vm_refl. Qed.
Lemma D_841a0 : decode_any W_841a0 = Some (Op32 ALU_SUB 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_841a4 : bv 32 := 0x00072713.
Lemma F_841a4 : fetch_word Ubsan.M.loaded_segments (0x841a4 : word) = Some W_841a4.
Proof. vm_refl. Qed.
Lemma D_841a4 : decode_any W_841a4 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_841a8 : bv 32 := 0x005882b3.
Lemma F_841a8 : fetch_word Ubsan.M.loaded_segments (0x841a8 : word) = Some W_841a8.
Proof. vm_refl. Qed.
Lemma D_841a8 : decode_any W_841a8 = Some (Op ALU_ADD 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_841ac : bv 32 := 0x00ff08b3.
Lemma F_841ac : fetch_word Ubsan.M.loaded_segments (0x841ac : word) = Some W_841ac.
Proof. vm_refl. Qed.
Lemma D_841ac : decode_any W_841ac = Some (Op ALU_ADD 17 30 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_841b0 : bv 32 := 0x407282bb.
Lemma F_841b0 : fetch_word Ubsan.M.loaded_segments (0x841b0 : word) = Some W_841b0.
Proof. vm_refl. Qed.
Lemma D_841b0 : decode_any W_841b0 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_841b4 : bv 32 := 0x04013383.
Lemma F_841b4 : fetch_word Ubsan.M.loaded_segments (0x841b4 : word) = Some W_841b4.
Proof. vm_refl. Qed.
Lemma D_841b4 : decode_any W_841b4 = Some (Load SZ8 true 7 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_841b8 : bv 32 := 0x407282bb.
Lemma F_841b8 : fetch_word Ubsan.M.loaded_segments (0x841b8 : word) = Some W_841b8.
Proof. vm_refl. Qed.
Lemma D_841b8 : decode_any W_841b8 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_841bc : bv 32 := 0x43f2d393.
Lemma F_841bc : fetch_word Ubsan.M.loaded_segments (0x841bc : word) = Some W_841bc.
Proof. vm_refl. Qed.
Lemma D_841bc : decode_any W_841bc = Some (ShiftImm ALU_SRA 7 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_841c0 : bv 32 := 0x0053f2b3.
Lemma F_841c0 : fetch_word Ubsan.M.loaded_segments (0x841c0 : word) = Some W_841c0.
Proof. vm_refl. Qed.
Lemma D_841c0 : decode_any W_841c0 = Some (Op ALU_AND 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_841c4 : bv 32 := 0x405302bb.
Lemma F_841c4 : fetch_word Ubsan.M.loaded_segments (0x841c4 : word) = Some W_841c4.
Proof. vm_refl. Qed.
Lemma D_841c4 : decode_any W_841c4 = Some (Op32 ALU_SUB 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_841c8 : bv 32 := 0x000e2313.
Lemma F_841c8 : fetch_word Ubsan.M.loaded_segments (0x841c8 : word) = Some W_841c8.
Proof. vm_refl. Qed.
Lemma D_841c8 : decode_any W_841c8 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_841cc : bv 32 := 0x00050393.
Lemma F_841cc : fetch_word Ubsan.M.loaded_segments (0x841cc : word) = Some W_841cc.
Proof. vm_refl. Qed.
Lemma D_841cc : decode_any W_841cc = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_841d0 : bv 32 := 0x00051463.
Lemma F_841d0 : fetch_word Ubsan.M.loaded_segments (0x841d0 : word) = Some W_841d0.
Proof. vm_refl. Qed.
Lemma D_841d0 : decode_any W_841d0 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_841d4 : bv 32 := 0xb20fe06f.
Lemma F_841d4 : fetch_word Ubsan.M.loaded_segments (0x841d4 : word) = Some W_841d4.
Proof. vm_refl. Qed.
Lemma D_841d4 : decode_any W_841d4 = Some (Jal 0 2089760, 4%Z).
Proof. vm_refl. Qed.

Definition W_841d8 : bv 32 := 0x00080463.
Lemma F_841d8 : fetch_word Ubsan.M.loaded_segments (0x841d8 : word) = Some W_841d8.
Proof. vm_refl. Qed.
Lemma D_841d8 : decode_any W_841d8 = Some (Branch BC_EQ 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_841dc : bv 32 := 0xb18fe06f.
Lemma F_841dc : fetch_word Ubsan.M.loaded_segments (0x841dc : word) = Some W_841dc.
Proof. vm_refl. Qed.
Lemma D_841dc : decode_any W_841dc = Some (Jal 0 2089752, 4%Z).
Proof. vm_refl. Qed.

Definition W_841e0 : bv 32 := 0x00bf0e33.
Lemma F_841e0 : fetch_word Ubsan.M.loaded_segments (0x841e0 : word) = Some W_841e0.
Proof. vm_refl. Qed.
Lemma D_841e0 : decode_any W_841e0 = Some (Op ALU_ADD 28 30 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_841e4 : bv 32 := 0x000e1463.
Lemma F_841e4 : fetch_word Ubsan.M.loaded_segments (0x841e4 : word) = Some W_841e4.
Proof. vm_refl. Qed.
Lemma D_841e4 : decode_any W_841e4 = Some (Branch BC_NE 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_841e8 : bv 32 := 0xb0cfe06f.
Lemma F_841e8 : fetch_word Ubsan.M.loaded_segments (0x841e8 : word) = Some W_841e8.
Proof. vm_refl. Qed.
Lemma D_841e8 : decode_any W_841e8 = Some (Jal 0 2089740, 4%Z).
Proof. vm_refl. Qed.

Definition W_841ec : bv 32 := 0x00052f83.
Lemma F_841ec : fetch_word Ubsan.M.loaded_segments (0x841ec : word) = Some W_841ec.
Proof. vm_refl. Qed.
Lemma D_841ec : decode_any W_841ec = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_841f0 : bv 32 := 0x000e2403.
Lemma F_841f0 : fetch_word Ubsan.M.loaded_segments (0x841f0 : word) = Some W_841f0.
Proof. vm_refl. Qed.
Lemma D_841f0 : decode_any W_841f0 = Some (Load SZ4 true 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_841f4 : bv 32 := 0x00cfffb3.
Lemma F_841f4 : fetch_word Ubsan.M.loaded_segments (0x841f4 : word) = Some W_841f4.
Proof. vm_refl. Qed.
Lemma D_841f4 : decode_any W_841f4 = Some (Op ALU_AND 31 31 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_841f8 : bv 32 := 0x01d47433.
Lemma F_841f8 : fetch_word Ubsan.M.loaded_segments (0x841f8 : word) = Some W_841f8.
Proof. vm_refl. Qed.
Lemma D_841f8 : decode_any W_841f8 = Some (Op ALU_AND 8 8 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_841fc : bv 32 := 0x01f46433.
Lemma F_841fc : fetch_word Ubsan.M.loaded_segments (0x841fc : word) = Some W_841fc.
Proof. vm_refl. Qed.
Lemma D_841fc : decode_any W_841fc = Some (Op ALU_OR 8 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84200 : bv 32 := 0x00768fb3.
Lemma F_84200 : fetch_word Ubsan.M.loaded_segments (0x84200 : word) = Some W_84200.
Proof. vm_refl. Qed.
Lemma D_84200 : decode_any W_84200 = Some (Op ALU_ADD 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84204 : bv 32 := 0x00852023.
Lemma F_84204 : fetch_word Ubsan.M.loaded_segments (0x84204 : word) = Some W_84204.
Proof. vm_refl. Qed.
Lemma D_84204 : decode_any W_84204 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84208 : bv 32 := 0x000f9463.
Lemma F_84208 : fetch_word Ubsan.M.loaded_segments (0x84208 : word) = Some W_84208.
Proof. vm_refl. Qed.
Lemma D_84208 : decode_any W_84208 = Some (Branch BC_NE 31 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8420c : bv 32 := 0xae8fe06f.
Lemma F_8420c : fetch_word Ubsan.M.loaded_segments (0x8420c : word) = Some W_8420c.
Proof. vm_refl. Qed.
Lemma D_8420c : decode_any W_8420c = Some (Jal 0 2089704, 4%Z).
Proof. vm_refl. Qed.

Definition W_84210 : bv 32 := 0x007fb3b3.
Lemma F_84210 : fetch_word Ubsan.M.loaded_segments (0x84210 : word) = Some W_84210.
Proof. vm_refl. Qed.
Lemma D_84210 : decode_any W_84210 = Some (Op ALU_SLTU 7 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84214 : bv 32 := 0x00e3c3b3.
Lemma F_84214 : fetch_word Ubsan.M.loaded_segments (0x84214 : word) = Some W_84214.
Proof. vm_refl. Qed.
Lemma D_84214 : decode_any W_84214 = Some (Op ALU_XOR 7 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_84218 : bv 32 := 0x0013c393.
Lemma F_84218 : fetch_word Ubsan.M.loaded_segments (0x84218 : word) = Some W_84218.
Proof. vm_refl. Qed.
Lemma D_84218 : decode_any W_84218 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8421c : bv 32 := 0x00039463.
Lemma F_8421c : fetch_word Ubsan.M.loaded_segments (0x8421c : word) = Some W_8421c.
Proof. vm_refl. Qed.
Lemma D_8421c : decode_any W_8421c = Some (Branch BC_NE 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84220 : bv 32 := 0xad4fe06f.
Lemma F_84220 : fetch_word Ubsan.M.loaded_segments (0x84220 : word) = Some W_84220.
Proof. vm_refl. Qed.
Lemma D_84220 : decode_any W_84220 = Some (Jal 0 2089684, 4%Z).
Proof. vm_refl. Qed.

Definition W_84224 : bv 32 := 0x00b883b3.
Lemma F_84224 : fetch_word Ubsan.M.loaded_segments (0x84224 : word) = Some W_84224.
Proof. vm_refl. Qed.
Lemma D_84224 : decode_any W_84224 = Some (Op ALU_ADD 7 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84228 : bv 32 := 0x00039463.
Lemma F_84228 : fetch_word Ubsan.M.loaded_segments (0x84228 : word) = Some W_84228.
Proof. vm_refl. Qed.
Lemma D_84228 : decode_any W_84228 = Some (Branch BC_NE 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8422c : bv 32 := 0xac8fe06f.
Lemma F_8422c : fetch_word Ubsan.M.loaded_segments (0x8422c : word) = Some W_8422c.
Proof. vm_refl. Qed.
Lemma D_8422c : decode_any W_8422c = Some (Jal 0 2089672, 4%Z).
Proof. vm_refl. Qed.

Definition W_84230 : bv 32 := 0x01c3b3b3.
Lemma F_84230 : fetch_word Ubsan.M.loaded_segments (0x84230 : word) = Some W_84230.
Proof. vm_refl. Qed.
Lemma D_84230 : decode_any W_84230 = Some (Op ALU_SLTU 7 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84234 : bv 32 := 0x0063c3b3.
Lemma F_84234 : fetch_word Ubsan.M.loaded_segments (0x84234 : word) = Some W_84234.
Proof. vm_refl. Qed.
Lemma D_84234 : decode_any W_84234 = Some (Op ALU_XOR 7 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84238 : bv 32 := 0x0013c393.
Lemma F_84238 : fetch_word Ubsan.M.loaded_segments (0x84238 : word) = Some W_84238.
Proof. vm_refl. Qed.
Lemma D_84238 : decode_any W_84238 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8423c : bv 32 := 0x00039463.
Lemma F_8423c : fetch_word Ubsan.M.loaded_segments (0x8423c : word) = Some W_8423c.
Proof. vm_refl. Qed.
Lemma D_8423c : decode_any W_8423c = Some (Branch BC_NE 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84240 : bv 32 := 0xab4fe06f.
Lemma F_84240 : fetch_word Ubsan.M.loaded_segments (0x84240 : word) = Some W_84240.
Proof. vm_refl. Qed.
Lemma D_84240 : decode_any W_84240 = Some (Jal 0 2089652, 4%Z).
Proof. vm_refl. Qed.

Definition W_84244 : bv 32 := 0x0012829b.
Lemma F_84244 : fetch_word Ubsan.M.loaded_segments (0x84244 : word) = Some W_84244.
Proof. vm_refl. Qed.
Lemma D_84244 : decode_any W_84244 = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84248 : bv 32 := 0x00f585b3.
Lemma F_84248 : fetch_word Ubsan.M.loaded_segments (0x84248 : word) = Some W_84248.
Proof. vm_refl. Qed.
Lemma D_84248 : decode_any W_84248 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8424c : bv 32 := 0x00d50533.
Lemma F_8424c : fetch_word Ubsan.M.loaded_segments (0x8424c : word) = Some W_8424c.
Proof. vm_refl. Qed.
Lemma D_8424c : decode_any W_8424c = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84250 : bv 32 := 0x000f8393.
Lemma F_84250 : fetch_word Ubsan.M.loaded_segments (0x84250 : word) = Some W_84250.
Proof. vm_refl. Qed.
Lemma D_84250 : decode_any W_84250 = Some (OpImm ALU_ADD 7 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84254 : bv 32 := 0xf6029ee3.
Lemma F_84254 : fetch_word Ubsan.M.loaded_segments (0x84254 : word) = Some W_84254.
Proof. vm_refl. Qed.
Lemma D_84254 : decode_any W_84254 = Some (Branch BC_NE 5 0 8060, 4%Z).
Proof. vm_refl. Qed.

Definition W_84258 : bv 32 := 0x3600306f.
Lemma F_84258 : fetch_word Ubsan.M.loaded_segments (0x84258 : word) = Some W_84258.
Proof. vm_refl. Qed.
Lemma D_84258 : decode_any W_84258 = Some (Jal 0 13152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8425c : bv 32 := 0x10008263.
Lemma F_8425c : fetch_word Ubsan.M.loaded_segments (0x8425c : word) = Some W_8425c.
Proof. vm_refl. Qed.
Lemma D_8425c : decode_any W_8425c = Some (Branch BC_EQ 1 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_84260 : bv 32 := 0x003a7593.
Lemma F_84260 : fetch_word Ubsan.M.loaded_segments (0x84260 : word) = Some W_84260.
Proof. vm_refl. Qed.
Lemma D_84260 : decode_any W_84260 = Some (OpImm ALU_AND 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84264 : bv 32 := 0x00058463.
Lemma F_84264 : fetch_word Ubsan.M.loaded_segments (0x84264 : word) = Some W_84264.
Proof. vm_refl. Qed.
Lemma D_84264 : decode_any W_84264 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84268 : bv 32 := 0xa8cfe06f.
Lemma F_84268 : fetch_word Ubsan.M.loaded_segments (0x84268 : word) = Some W_84268.
Proof. vm_refl. Qed.
Lemma D_84268 : decode_any W_84268 = Some (Jal 0 2089612, 4%Z).
Proof. vm_refl. Qed.

Definition W_8426c : bv 32 := 0xfffbc613.
Lemma F_8426c : fetch_word Ubsan.M.loaded_segments (0x8426c : word) = Some W_8426c.
Proof. vm_refl. Qed.
Lemma D_8426c : decode_any W_8426c = Some (OpImm ALU_XOR 12 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84270 : bv 32 := 0x00271693.
Lemma F_84270 : fetch_word Ubsan.M.loaded_segments (0x84270 : word) = Some W_84270.
Proof. vm_refl. Qed.
Lemma D_84270 : decode_any W_84270 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84274 : bv 32 := 0x05813983.
Lemma F_84274 : fetch_word Ubsan.M.loaded_segments (0x84274 : word) = Some W_84274.
Proof. vm_refl. Qed.
Lemma D_84274 : decode_any W_84274 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84278 : bv 32 := 0x00299893.
Lemma F_84278 : fetch_word Ubsan.M.loaded_segments (0x84278 : word) = Some W_84278.
Proof. vm_refl. Qed.
Lemma D_84278 : decode_any W_84278 = Some (ShiftImm ALU_SLL 17 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8427c : bv 32 := 0x003af293.
Lemma F_8427c : fetch_word Ubsan.M.loaded_segments (0x8427c : word) = Some W_8427c.
Proof. vm_refl. Qed.
Lemma D_8427c : decode_any W_8427c = Some (OpImm ALU_AND 5 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84280 : bv 32 := 0x05013e03.
Lemma F_84280 : fetch_word Ubsan.M.loaded_segments (0x84280 : word) = Some W_84280.
Proof. vm_refl. Qed.
Lemma D_84280 : decode_any W_84280 = Some (Load SZ8 true 28 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_84284 : bv 32 := 0x02813783.
Lemma F_84284 : fetch_word Ubsan.M.loaded_segments (0x84284 : word) = Some W_84284.
Proof. vm_refl. Qed.
Lemma D_84284 : decode_any W_84284 = Some (Load SZ8 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84288 : bv 32 := 0x41c7833b.
Lemma F_84288 : fetch_word Ubsan.M.loaded_segments (0x84288 : word) = Some W_84288.
Proof. vm_refl. Qed.
Lemma D_84288 : decode_any W_84288 = Some (Op32 ALU_SUB 6 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8428c : bv 32 := 0x03813803.
Lemma F_8428c : fetch_word Ubsan.M.loaded_segments (0x8428c : word) = Some W_8428c.
Proof. vm_refl. Qed.
Lemma D_8428c : decode_any W_8428c = Some (Load SZ8 true 16 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84290 : bv 32 := 0x03013783.
Lemma F_84290 : fetch_word Ubsan.M.loaded_segments (0x84290 : word) = Some W_84290.
Proof. vm_refl. Qed.
Lemma D_84290 : decode_any W_84290 = Some (Load SZ8 true 15 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_84294 : bv 32 := 0x01078833.
Lemma F_84294 : fetch_word Ubsan.M.loaded_segments (0x84294 : word) = Some W_84294.
Proof. vm_refl. Qed.
Lemma D_84294 : decode_any W_84294 = Some (Op ALU_ADD 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84298 : bv 32 := 0x04813c03.
Lemma F_84298 : fetch_word Ubsan.M.loaded_segments (0x84298 : word) = Some W_84298.
Proof. vm_refl. Qed.
Lemma D_84298 : decode_any W_84298 = Some (Load SZ8 true 24 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8429c : bv 32 := 0x43fc5393.
Lemma F_8429c : fetch_word Ubsan.M.loaded_segments (0x8429c : word) = Some W_8429c.
Proof. vm_refl. Qed.
Lemma D_8429c : decode_any W_8429c = Some (ShiftImm ALU_SRA 7 24 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_842a0 : bv 32 := 0x00072793.
Lemma F_842a0 : fetch_word Ubsan.M.loaded_segments (0x842a0 : word) = Some W_842a0.
Proof. vm_refl. Qed.
Lemma D_842a0 : decode_any W_842a0 = Some (OpImm ALU_SLT 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_842a4 : bv 32 := 0x0183f3b3.
Lemma F_842a4 : fetch_word Ubsan.M.loaded_segments (0x842a4 : word) = Some W_842a4.
Proof. vm_refl. Qed.
Lemma D_842a4 : decode_any W_842a4 = Some (Op ALU_AND 7 7 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_842a8 : bv 32 := 0x41c80e3b.
Lemma F_842a8 : fetch_word Ubsan.M.loaded_segments (0x842a8 : word) = Some W_842a8.
Proof. vm_refl. Qed.
Lemma D_842a8 : decode_any W_842a8 = Some (Op32 ALU_SUB 28 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_842ac : bv 32 := 0x011a8833.
Lemma F_842ac : fetch_word Ubsan.M.loaded_segments (0x842ac : word) = Some W_842ac.
Proof. vm_refl. Qed.
Lemma D_842ac : decode_any W_842ac = Some (Op ALU_ADD 16 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_842b0 : bv 32 := 0x04013c03.
Lemma F_842b0 : fetch_word Ubsan.M.loaded_segments (0x842b0 : word) = Some W_842b0.
Proof. vm_refl. Qed.
Lemma D_842b0 : decode_any W_842b0 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_842b4 : bv 32 := 0x418e0e3b.
Lemma F_842b4 : fetch_word Ubsan.M.loaded_segments (0x842b4 : word) = Some W_842b4.
Proof. vm_refl. Qed.
Lemma D_842b4 : decode_any W_842b4 = Some (Op32 ALU_SUB 28 28 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_842b8 : bv 32 := 0x007e03bb.
Lemma F_842b8 : fetch_word Ubsan.M.loaded_segments (0x842b8 : word) = Some W_842b8.
Proof. vm_refl. Qed.
Lemma D_842b8 : decode_any W_842b8 = Some (Op32 ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_842bc : bv 32 := 0x43f3de13.
Lemma F_842bc : fetch_word Ubsan.M.loaded_segments (0x842bc : word) = Some W_842bc.
Proof. vm_refl. Qed.
Lemma D_842bc : decode_any W_842bc = Some (ShiftImm ALU_SRA 28 7 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_842c0 : bv 32 := 0x007e73b3.
Lemma F_842c0 : fetch_word Ubsan.M.loaded_segments (0x842c0 : word) = Some W_842c0.
Proof. vm_refl. Qed.
Lemma D_842c0 : decode_any W_842c0 = Some (Op ALU_AND 7 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_842c4 : bv 32 := 0x407303bb.
Lemma F_842c4 : fetch_word Ubsan.M.loaded_segments (0x842c4 : word) = Some W_842c4.
Proof. vm_refl. Qed.
Lemma D_842c4 : decode_any W_842c4 = Some (Op32 ALU_SUB 7 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_842c8 : bv 32 := 0x0009ae13.
Lemma F_842c8 : fetch_word Ubsan.M.loaded_segments (0x842c8 : word) = Some W_842c8.
Proof. vm_refl. Qed.
Lemma D_842c8 : decode_any W_842c8 = Some (OpImm ALU_SLT 28 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_842cc : bv 32 := 0x000a0993.
Lemma F_842cc : fetch_word Ubsan.M.loaded_segments (0x842cc : word) = Some W_842cc.
Proof. vm_refl. Qed.
Lemma D_842cc : decode_any W_842cc = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_842d0 : bv 32 := 0x000a1463.
Lemma F_842d0 : fetch_word Ubsan.M.loaded_segments (0x842d0 : word) = Some W_842d0.
Proof. vm_refl. Qed.
Lemma D_842d0 : decode_any W_842d0 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_842d4 : bv 32 := 0xa20fe06f.
Lemma F_842d4 : fetch_word Ubsan.M.loaded_segments (0x842d4 : word) = Some W_842d4.
Proof. vm_refl. Qed.
Lemma D_842d4 : decode_any W_842d4 = Some (Jal 0 2089504, 4%Z).
Proof. vm_refl. Qed.

Definition W_842d8 : bv 32 := 0x00028463.
Lemma F_842d8 : fetch_word Ubsan.M.loaded_segments (0x842d8 : word) = Some W_842d8.
Proof. vm_refl. Qed.
Lemma D_842d8 : decode_any W_842d8 = Some (Branch BC_EQ 5 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_842dc : bv 32 := 0xa18fe06f.
Lemma F_842dc : fetch_word Ubsan.M.loaded_segments (0x842dc : word) = Some W_842dc.
Proof. vm_refl. Qed.
Lemma D_842dc : decode_any W_842dc = Some (Jal 0 2089496, 4%Z).
Proof. vm_refl. Qed.

Definition W_842e0 : bv 32 := 0x00ba8c33.
Lemma F_842e0 : fetch_word Ubsan.M.loaded_segments (0x842e0 : word) = Some W_842e0.
Proof. vm_refl. Qed.
Lemma D_842e0 : decode_any W_842e0 = Some (Op ALU_ADD 24 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_842e4 : bv 32 := 0x000c1463.
Lemma F_842e4 : fetch_word Ubsan.M.loaded_segments (0x842e4 : word) = Some W_842e4.
Proof. vm_refl. Qed.
Lemma D_842e4 : decode_any W_842e4 = Some (Branch BC_NE 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_842e8 : bv 32 := 0xa0cfe06f.
Lemma F_842e8 : fetch_word Ubsan.M.loaded_segments (0x842e8 : word) = Some W_842e8.
Proof. vm_refl. Qed.
Lemma D_842e8 : decode_any W_842e8 = Some (Jal 0 2089484, 4%Z).
Proof. vm_refl. Qed.

Definition W_842ec : bv 32 := 0x000a2303.
Lemma F_842ec : fetch_word Ubsan.M.loaded_segments (0x842ec : word) = Some W_842ec.
Proof. vm_refl. Qed.
Lemma D_842ec : decode_any W_842ec = Some (Load SZ4 true 6 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_842f0 : bv 32 := 0x000c2c83.
Lemma F_842f0 : fetch_word Ubsan.M.loaded_segments (0x842f0 : word) = Some W_842f0.
Proof. vm_refl. Qed.
Lemma D_842f0 : decode_any W_842f0 = Some (Load SZ4 true 25 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_842f4 : bv 32 := 0x00c37d33.
Lemma F_842f4 : fetch_word Ubsan.M.loaded_segments (0x842f4 : word) = Some W_842f4.
Proof. vm_refl. Qed.
Lemma D_842f4 : decode_any W_842f4 = Some (Op ALU_AND 26 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_842f8 : bv 32 := 0xfffccc93.
Lemma F_842f8 : fetch_word Ubsan.M.loaded_segments (0x842f8 : word) = Some W_842f8.
Proof. vm_refl. Qed.
Lemma D_842f8 : decode_any W_842f8 = Some (OpImm ALU_XOR 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_842fc : bv 32 := 0x01936333.
Lemma F_842fc : fetch_word Ubsan.M.loaded_segments (0x842fc : word) = Some W_842fc.
Proof. vm_refl. Qed.
Lemma D_842fc : decode_any W_842fc = Some (Op ALU_OR 6 6 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_84300 : bv 32 := 0x01737333.
Lemma F_84300 : fetch_word Ubsan.M.loaded_segments (0x84300 : word) = Some W_84300.
Proof. vm_refl. Qed.
Lemma D_84300 : decode_any W_84300 = Some (Op ALU_AND 6 6 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_84304 : bv 32 := 0x01a36333.
Lemma F_84304 : fetch_word Ubsan.M.loaded_segments (0x84304 : word) = Some W_84304.
Proof. vm_refl. Qed.
Lemma D_84304 : decode_any W_84304 = Some (Op ALU_OR 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_84308 : bv 32 := 0x01368cb3.
Lemma F_84308 : fetch_word Ubsan.M.loaded_segments (0x84308 : word) = Some W_84308.
Proof. vm_refl. Qed.
Lemma D_84308 : decode_any W_84308 = Some (Op ALU_ADD 25 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8430c : bv 32 := 0x006a2023.
Lemma F_8430c : fetch_word Ubsan.M.loaded_segments (0x8430c : word) = Some W_8430c.
Proof. vm_refl. Qed.
Lemma D_8430c : decode_any W_8430c = Some (Store SZ4 20 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84310 : bv 32 := 0x000c9463.
Lemma F_84310 : fetch_word Ubsan.M.loaded_segments (0x84310 : word) = Some W_84310.
Proof. vm_refl. Qed.
Lemma D_84310 : decode_any W_84310 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84314 : bv 32 := 0x9e0fe06f.
Lemma F_84314 : fetch_word Ubsan.M.loaded_segments (0x84314 : word) = Some W_84314.
Proof. vm_refl. Qed.
Lemma D_84314 : decode_any W_84314 = Some (Jal 0 2089440, 4%Z).
Proof. vm_refl. Qed.

Definition W_84318 : bv 32 := 0x013cb333.
Lemma F_84318 : fetch_word Ubsan.M.loaded_segments (0x84318 : word) = Some W_84318.
Proof. vm_refl. Qed.
Lemma D_84318 : decode_any W_84318 = Some (Op ALU_SLTU 6 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8431c : bv 32 := 0x00f34333.
Lemma F_8431c : fetch_word Ubsan.M.loaded_segments (0x8431c : word) = Some W_8431c.
Proof. vm_refl. Qed.
Lemma D_8431c : decode_any W_8431c = Some (Op ALU_XOR 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84320 : bv 32 := 0x00134313.
Lemma F_84320 : fetch_word Ubsan.M.loaded_segments (0x84320 : word) = Some W_84320.
Proof. vm_refl. Qed.
Lemma D_84320 : decode_any W_84320 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84324 : bv 32 := 0x00031463.
Lemma F_84324 : fetch_word Ubsan.M.loaded_segments (0x84324 : word) = Some W_84324.
Proof. vm_refl. Qed.
Lemma D_84324 : decode_any W_84324 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84328 : bv 32 := 0x9ccfe06f.
Lemma F_84328 : fetch_word Ubsan.M.loaded_segments (0x84328 : word) = Some W_84328.
Proof. vm_refl. Qed.
Lemma D_84328 : decode_any W_84328 = Some (Jal 0 2089420, 4%Z).
Proof. vm_refl. Qed.

Definition W_8432c : bv 32 := 0x00b80333.
Lemma F_8432c : fetch_word Ubsan.M.loaded_segments (0x8432c : word) = Some W_8432c.
Proof. vm_refl. Qed.
Lemma D_8432c : decode_any W_8432c = Some (Op ALU_ADD 6 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84330 : bv 32 := 0x00031463.
Lemma F_84330 : fetch_word Ubsan.M.loaded_segments (0x84330 : word) = Some W_84330.
Proof. vm_refl. Qed.
Lemma D_84330 : decode_any W_84330 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84334 : bv 32 := 0x9c0fe06f.
Lemma F_84334 : fetch_word Ubsan.M.loaded_segments (0x84334 : word) = Some W_84334.
Proof. vm_refl. Qed.
Lemma D_84334 : decode_any W_84334 = Some (Jal 0 2089408, 4%Z).
Proof. vm_refl. Qed.

Definition W_84338 : bv 32 := 0x01833333.
Lemma F_84338 : fetch_word Ubsan.M.loaded_segments (0x84338 : word) = Some W_84338.
Proof. vm_refl. Qed.
Lemma D_84338 : decode_any W_84338 = Some (Op ALU_SLTU 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8433c : bv 32 := 0x01c34333.
Lemma F_8433c : fetch_word Ubsan.M.loaded_segments (0x8433c : word) = Some W_8433c.
Proof. vm_refl. Qed.
Lemma D_8433c : decode_any W_8433c = Some (Op ALU_XOR 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84340 : bv 32 := 0x00134313.
Lemma F_84340 : fetch_word Ubsan.M.loaded_segments (0x84340 : word) = Some W_84340.
Proof. vm_refl. Qed.
Lemma D_84340 : decode_any W_84340 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84344 : bv 32 := 0x00031463.
Lemma F_84344 : fetch_word Ubsan.M.loaded_segments (0x84344 : word) = Some W_84344.
Proof. vm_refl. Qed.
Lemma D_84344 : decode_any W_84344 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84348 : bv 32 := 0x9acfe06f.
Lemma F_84348 : fetch_word Ubsan.M.loaded_segments (0x84348 : word) = Some W_84348.
Proof. vm_refl. Qed.
Lemma D_84348 : decode_any W_84348 = Some (Jal 0 2089388, 4%Z).
Proof. vm_refl. Qed.

Definition W_8434c : bv 32 := 0x0013839b.
Lemma F_8434c : fetch_word Ubsan.M.loaded_segments (0x8434c : word) = Some W_8434c.
Proof. vm_refl. Qed.
Lemma D_8434c : decode_any W_8434c = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84350 : bv 32 := 0x011585b3.
Lemma F_84350 : fetch_word Ubsan.M.loaded_segments (0x84350 : word) = Some W_84350.
Proof. vm_refl. Qed.
Lemma D_84350 : decode_any W_84350 = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84354 : bv 32 := 0x00da0a33.
Lemma F_84354 : fetch_word Ubsan.M.loaded_segments (0x84354 : word) = Some W_84354.
Proof. vm_refl. Qed.
Lemma D_84354 : decode_any W_84354 = Some (Op ALU_ADD 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84358 : bv 32 := 0x000c8993.
Lemma F_84358 : fetch_word Ubsan.M.loaded_segments (0x84358 : word) = Some W_84358.
Proof. vm_refl. Qed.
Lemma D_84358 : decode_any W_84358 = Some (OpImm ALU_ADD 19 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8435c : bv 32 := 0xf6039ae3.
Lemma F_8435c : fetch_word Ubsan.M.loaded_segments (0x8435c : word) = Some W_8435c.
Proof. vm_refl. Qed.
Lemma D_8435c : decode_any W_8435c = Some (Branch BC_NE 7 0 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_84360 : bv 32 := 0x120b1463.
Lemma F_84360 : fetch_word Ubsan.M.loaded_segments (0x84360 : word) = Some W_84360.
Proof. vm_refl. Qed.
Lemma D_84360 : decode_any W_84360 = Some (Branch BC_NE 22 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_84364 : bv 32 := 0x00000593.
Lemma F_84364 : fetch_word Ubsan.M.loaded_segments (0x84364 : word) = Some W_84364.
Proof. vm_refl. Qed.
Lemma D_84364 : decode_any W_84364 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84368 : bv 32 := 0x00271613.
Lemma F_84368 : fetch_word Ubsan.M.loaded_segments (0x84368 : word) = Some W_84368.
Proof. vm_refl. Qed.
Lemma D_84368 : decode_any W_84368 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8436c : bv 32 := 0x05813303.
Lemma F_8436c : fetch_word Ubsan.M.loaded_segments (0x8436c : word) = Some W_8436c.
Proof. vm_refl. Qed.
Lemma D_8436c : decode_any W_8436c = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84370 : bv 32 := 0x00231693.
Lemma F_84370 : fetch_word Ubsan.M.loaded_segments (0x84370 : word) = Some W_84370.
Proof. vm_refl. Qed.
Lemma D_84370 : decode_any W_84370 = Some (ShiftImm ALU_SLL 13 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84374 : bv 32 := 0x00397793.
Lemma F_84374 : fetch_word Ubsan.M.loaded_segments (0x84374 : word) = Some W_84374.
Proof. vm_refl. Qed.
Lemma D_84374 : decode_any W_84374 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84378 : bv 32 := 0x00347813.
Lemma F_84378 : fetch_word Ubsan.M.loaded_segments (0x84378 : word) = Some W_84378.
Proof. vm_refl. Qed.
Lemma D_84378 : decode_any W_84378 = Some (OpImm ALU_AND 16 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8437c : bv 32 := 0x002f9893.
Lemma F_8437c : fetch_word Ubsan.M.loaded_segments (0x8437c : word) = Some W_8437c.
Proof. vm_refl. Qed.
Lemma D_8437c : decode_any W_8437c = Some (ShiftImm ALU_SLL 17 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84380 : bv 32 := 0x00072293.
Lemma F_84380 : fetch_word Ubsan.M.loaded_segments (0x84380 : word) = Some W_84380.
Proof. vm_refl. Qed.
Lemma D_84380 : decode_any W_84380 = Some (OpImm ALU_SLT 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84384 : bv 32 := 0x00032393.
Lemma F_84384 : fetch_word Ubsan.M.loaded_segments (0x84384 : word) = Some W_84384.
Proof. vm_refl. Qed.
Lemma D_84384 : decode_any W_84384 = Some (OpImm ALU_SLT 7 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84388 : bv 32 := 0x00183993.
Lemma F_84388 : fetch_word Ubsan.M.loaded_segments (0x84388 : word) = Some W_84388.
Proof. vm_refl. Qed.
Lemma D_84388 : decode_any W_84388 = Some (OpImm ALU_SLTU 19 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8438c : bv 32 := 0x0017ba13.
Lemma F_8438c : fetch_word Ubsan.M.loaded_segments (0x8438c : word) = Some W_8438c.
Proof. vm_refl. Qed.
Lemma D_8438c : decode_any W_8438c = Some (OpImm ALU_SLTU 20 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84390 : bv 32 := 0x00090a93.
Lemma F_84390 : fetch_word Ubsan.M.loaded_segments (0x84390 : word) = Some W_84390.
Proof. vm_refl. Qed.
Lemma D_84390 : decode_any W_84390 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84394 : bv 32 := 0x00040b13.
Lemma F_84394 : fetch_word Ubsan.M.loaded_segments (0x84394 : word) = Some W_84394.
Proof. vm_refl. Qed.
Lemma D_84394 : decode_any W_84394 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84398 : bv 32 := 0x080f8263.
Lemma F_84398 : fetch_word Ubsan.M.loaded_segments (0x84398 : word) = Some W_84398.
Proof. vm_refl. Qed.
Lemma D_84398 : decode_any W_84398 = Some (Branch BC_EQ 31 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_8439c : bv 32 := 0x00000793.
Lemma F_8439c : fetch_word Ubsan.M.loaded_segments (0x8439c : word) = Some W_8439c.
Proof. vm_refl. Qed.
Lemma D_8439c : decode_any W_8439c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_843a0 : bv 32 := 0x01203833.
Lemma F_843a0 : fetch_word Ubsan.M.loaded_segments (0x843a0 : word) = Some W_843a0.
Proof. vm_refl. Qed.
Lemma D_843a0 : decode_any W_843a0 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_843a4 : bv 32 := 0x00803e33.
Lemma F_843a4 : fetch_word Ubsan.M.loaded_segments (0x843a4 : word) = Some W_843a4.
Proof. vm_refl. Qed.
Lemma D_843a4 : decode_any W_843a4 = Some (Op ALU_SLTU 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843a8 : bv 32 := 0x010a7bb3.
Lemma F_843a8 : fetch_word Ubsan.M.loaded_segments (0x843a8 : word) = Some W_843a8.
Proof. vm_refl. Qed.
Lemma D_843a8 : decode_any W_843a8 = Some (Op ALU_AND 23 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_843ac : bv 32 := 0x01c9fc33.
Lemma F_843ac : fetch_word Ubsan.M.loaded_segments (0x843ac : word) = Some W_843ac.
Proof. vm_refl. Qed.
Lemma D_843ac : decode_any W_843ac = Some (Op ALU_AND 24 19 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_843b0 : bv 32 := 0x00fa8333.
Lemma F_843b0 : fetch_word Ubsan.M.loaded_segments (0x843b0 : word) = Some W_843b0.
Proof. vm_refl. Qed.
Lemma D_843b0 : decode_any W_843b0 = Some (Op ALU_ADD 6 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_843b4 : bv 32 := 0x01237463.
Lemma F_843b4 : fetch_word Ubsan.M.loaded_segments (0x843b4 : word) = Some W_843b4.
Proof. vm_refl. Qed.
Lemma D_843b4 : decode_any W_843b4 = Some (Branch BC_GEU 6 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843b8 : bv 32 := 0x93cfe06f.
Lemma F_843b8 : fetch_word Ubsan.M.loaded_segments (0x843b8 : word) = Some W_843b8.
Proof. vm_refl. Qed.
Lemma D_843b8 : decode_any W_843b8 = Some (Jal 0 2089276, 4%Z).
Proof. vm_refl. Qed.

Definition W_843bc : bv 32 := 0x00133313.
Lemma F_843bc : fetch_word Ubsan.M.loaded_segments (0x843bc : word) = Some W_843bc.
Proof. vm_refl. Qed.
Lemma D_843bc : decode_any W_843bc = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_843c0 : bv 32 := 0x00684333.
Lemma F_843c0 : fetch_word Ubsan.M.loaded_segments (0x843c0 : word) = Some W_843c0.
Proof. vm_refl. Qed.
Lemma D_843c0 : decode_any W_843c0 = Some (Op ALU_XOR 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_843c4 : bv 32 := 0x00031463.
Lemma F_843c4 : fetch_word Ubsan.M.loaded_segments (0x843c4 : word) = Some W_843c4.
Proof. vm_refl. Qed.
Lemma D_843c4 : decode_any W_843c4 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843c8 : bv 32 := 0x92cfe06f.
Lemma F_843c8 : fetch_word Ubsan.M.loaded_segments (0x843c8 : word) = Some W_843c8.
Proof. vm_refl. Qed.
Lemma D_843c8 : decode_any W_843c8 = Some (Jal 0 2089260, 4%Z).
Proof. vm_refl. Qed.

Definition W_843cc : bv 32 := 0x000b9463.
Lemma F_843cc : fetch_word Ubsan.M.loaded_segments (0x843cc : word) = Some W_843cc.
Proof. vm_refl. Qed.
Lemma D_843cc : decode_any W_843cc = Some (Branch BC_NE 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843d0 : bv 32 := 0x924fe06f.
Lemma F_843d0 : fetch_word Ubsan.M.loaded_segments (0x843d0 : word) = Some W_843d0.
Proof. vm_refl. Qed.
Lemma D_843d0 : decode_any W_843d0 = Some (Jal 0 2089252, 4%Z).
Proof. vm_refl. Qed.

Definition W_843d4 : bv 32 := 0x00fb0333.
Lemma F_843d4 : fetch_word Ubsan.M.loaded_segments (0x843d4 : word) = Some W_843d4.
Proof. vm_refl. Qed.
Lemma D_843d4 : decode_any W_843d4 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_843d8 : bv 32 := 0x00837463.
Lemma F_843d8 : fetch_word Ubsan.M.loaded_segments (0x843d8 : word) = Some W_843d8.
Proof. vm_refl. Qed.
Lemma D_843d8 : decode_any W_843d8 = Some (Branch BC_GEU 6 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843dc : bv 32 := 0x918fe06f.
Lemma F_843dc : fetch_word Ubsan.M.loaded_segments (0x843dc : word) = Some W_843dc.
Proof. vm_refl. Qed.
Lemma D_843dc : decode_any W_843dc = Some (Jal 0 2089240, 4%Z).
Proof. vm_refl. Qed.

Definition W_843e0 : bv 32 := 0x00133313.
Lemma F_843e0 : fetch_word Ubsan.M.loaded_segments (0x843e0 : word) = Some W_843e0.
Proof. vm_refl. Qed.
Lemma D_843e0 : decode_any W_843e0 = Some (OpImm ALU_SLTU 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_843e4 : bv 32 := 0x006e4333.
Lemma F_843e4 : fetch_word Ubsan.M.loaded_segments (0x843e4 : word) = Some W_843e4.
Proof. vm_refl. Qed.
Lemma D_843e4 : decode_any W_843e4 = Some (Op ALU_XOR 6 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_843e8 : bv 32 := 0x00031463.
Lemma F_843e8 : fetch_word Ubsan.M.loaded_segments (0x843e8 : word) = Some W_843e8.
Proof. vm_refl. Qed.
Lemma D_843e8 : decode_any W_843e8 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843ec : bv 32 := 0x908fe06f.
Lemma F_843ec : fetch_word Ubsan.M.loaded_segments (0x843ec : word) = Some W_843ec.
Proof. vm_refl. Qed.
Lemma D_843ec : decode_any W_843ec = Some (Jal 0 2089224, 4%Z).
Proof. vm_refl. Qed.

Definition W_843f0 : bv 32 := 0x000c1463.
Lemma F_843f0 : fetch_word Ubsan.M.loaded_segments (0x843f0 : word) = Some W_843f0.
Proof. vm_refl. Qed.
Lemma D_843f0 : decode_any W_843f0 = Some (Branch BC_NE 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_843f4 : bv 32 := 0x900fe06f.
Lemma F_843f4 : fetch_word Ubsan.M.loaded_segments (0x843f4 : word) = Some W_843f4.
Proof. vm_refl. Qed.
Lemma D_843f4 : decode_any W_843f4 = Some (Jal 0 2089216, 4%Z).
Proof. vm_refl. Qed.

Definition W_843f8 : bv 32 := 0x00f90333.
Lemma F_843f8 : fetch_word Ubsan.M.loaded_segments (0x843f8 : word) = Some W_843f8.
Proof. vm_refl. Qed.
Lemma D_843f8 : decode_any W_843f8 = Some (Op ALU_ADD 6 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_843fc : bv 32 := 0x00f40cb3.
Lemma F_843fc : fetch_word Ubsan.M.loaded_segments (0x843fc : word) = Some W_843fc.
Proof. vm_refl. Qed.
Lemma D_843fc : decode_any W_843fc = Some (Op ALU_ADD 25 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84400 : bv 32 := 0x00032303.
Lemma F_84400 : fetch_word Ubsan.M.loaded_segments (0x84400 : word) = Some W_84400.
Proof. vm_refl. Qed.
Lemma D_84400 : decode_any W_84400 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84404 : bv 32 := 0x000cad03.
Lemma F_84404 : fetch_word Ubsan.M.loaded_segments (0x84404 : word) = Some W_84404.
Proof. vm_refl. Qed.
Lemma D_84404 : decode_any W_84404 = Some (Load SZ4 true 26 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84408 : bv 32 := 0xfff34313.
Lemma F_84408 : fetch_word Ubsan.M.loaded_segments (0x84408 : word) = Some W_84408.
Proof. vm_refl. Qed.
Lemma D_84408 : decode_any W_84408 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8440c : bv 32 := 0x006d6333.
Lemma F_8440c : fetch_word Ubsan.M.loaded_segments (0x8440c : word) = Some W_8440c.
Proof. vm_refl. Qed.
Lemma D_8440c : decode_any W_8440c = Some (Op ALU_OR 6 26 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84410 : bv 32 := 0x00478793.
Lemma F_84410 : fetch_word Ubsan.M.loaded_segments (0x84410 : word) = Some W_84410.
Proof. vm_refl. Qed.
Lemma D_84410 : decode_any W_84410 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84414 : bv 32 := 0x006ca023.
Lemma F_84414 : fetch_word Ubsan.M.loaded_segments (0x84414 : word) = Some W_84414.
Proof. vm_refl. Qed.
Lemma D_84414 : decode_any W_84414 = Some (Store SZ4 25 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84418 : bv 32 := 0xf8f89ce3.
Lemma F_84418 : fetch_word Ubsan.M.loaded_segments (0x84418 : word) = Some W_84418.
Proof. vm_refl. Qed.
Lemma D_84418 : decode_any W_84418 = Some (Branch BC_NE 17 15 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8441c : bv 32 := 0x00c407b3.
Lemma F_8441c : fetch_word Ubsan.M.loaded_segments (0x8441c : word) = Some W_8441c.
Proof. vm_refl. Qed.
Lemma D_8441c : decode_any W_8441c = Some (Op ALU_ADD 15 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84420 : bv 32 := 0x00803833.
Lemma F_84420 : fetch_word Ubsan.M.loaded_segments (0x84420 : word) = Some W_84420.
Proof. vm_refl. Qed.
Lemma D_84420 : decode_any W_84420 = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84424 : bv 32 := 0x0017b313.
Lemma F_84424 : fetch_word Ubsan.M.loaded_segments (0x84424 : word) = Some W_84424.
Proof. vm_refl. Qed.
Lemma D_84424 : decode_any W_84424 = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84428 : bv 32 := 0x00681463.
Lemma F_84428 : fetch_word Ubsan.M.loaded_segments (0x84428 : word) = Some W_84428.
Proof. vm_refl. Qed.
Lemma D_84428 : decode_any W_84428 = Some (Branch BC_NE 16 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8442c : bv 32 := 0x8c8fe06f.
Lemma F_8442c : fetch_word Ubsan.M.loaded_segments (0x8442c : word) = Some W_8442c.
Proof. vm_refl. Qed.
Lemma D_8442c : decode_any W_8442c = Some (Jal 0 2089160, 4%Z).
Proof. vm_refl. Qed.

Definition W_84430 : bv 32 := 0x0087b7b3.
Lemma F_84430 : fetch_word Ubsan.M.loaded_segments (0x84430 : word) = Some W_84430.
Proof. vm_refl. Qed.
Lemma D_84430 : decode_any W_84430 = Some (Op ALU_SLTU 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84434 : bv 32 := 0x0057c7b3.
Lemma F_84434 : fetch_word Ubsan.M.loaded_segments (0x84434 : word) = Some W_84434.
Proof. vm_refl. Qed.
Lemma D_84434 : decode_any W_84434 = Some (Op ALU_XOR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84438 : bv 32 := 0x0017c793.
Lemma F_84438 : fetch_word Ubsan.M.loaded_segments (0x84438 : word) = Some W_84438.
Proof. vm_refl. Qed.
Lemma D_84438 : decode_any W_84438 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8443c : bv 32 := 0x00079463.
Lemma F_8443c : fetch_word Ubsan.M.loaded_segments (0x8443c : word) = Some W_8443c.
Proof. vm_refl. Qed.
Lemma D_8443c : decode_any W_8443c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84440 : bv 32 := 0x8b4fe06f.
Lemma F_84440 : fetch_word Ubsan.M.loaded_segments (0x84440 : word) = Some W_84440.
Proof. vm_refl. Qed.
Lemma D_84440 : decode_any W_84440 = Some (Jal 0 2089140, 4%Z).
Proof. vm_refl. Qed.

Definition W_84444 : bv 32 := 0x012687b3.
Lemma F_84444 : fetch_word Ubsan.M.loaded_segments (0x84444 : word) = Some W_84444.
Proof. vm_refl. Qed.
Lemma D_84444 : decode_any W_84444 = Some (Op ALU_ADD 15 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84448 : bv 32 := 0x01203833.
Lemma F_84448 : fetch_word Ubsan.M.loaded_segments (0x84448 : word) = Some W_84448.
Proof. vm_refl. Qed.
Lemma D_84448 : decode_any W_84448 = Some (Op ALU_SLTU 16 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8444c : bv 32 := 0x0017b313.
Lemma F_8444c : fetch_word Ubsan.M.loaded_segments (0x8444c : word) = Some W_8444c.
Proof. vm_refl. Qed.
Lemma D_8444c : decode_any W_8444c = Some (OpImm ALU_SLTU 6 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84450 : bv 32 := 0x00681463.
Lemma F_84450 : fetch_word Ubsan.M.loaded_segments (0x84450 : word) = Some W_84450.
Proof. vm_refl. Qed.
Lemma D_84450 : decode_any W_84450 = Some (Branch BC_NE 16 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84454 : bv 32 := 0x8a0fe06f.
Lemma F_84454 : fetch_word Ubsan.M.loaded_segments (0x84454 : word) = Some W_84454.
Proof. vm_refl. Qed.
Lemma D_84454 : decode_any W_84454 = Some (Jal 0 2089120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84458 : bv 32 := 0x0127b833.
Lemma F_84458 : fetch_word Ubsan.M.loaded_segments (0x84458 : word) = Some W_84458.
Proof. vm_refl. Qed.
Lemma D_84458 : decode_any W_84458 = Some (Op ALU_SLTU 16 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8445c : bv 32 := 0x00784833.
Lemma F_8445c : fetch_word Ubsan.M.loaded_segments (0x8445c : word) = Some W_8445c.
Proof. vm_refl. Qed.
Lemma D_8445c : decode_any W_8445c = Some (Op ALU_XOR 16 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84460 : bv 32 := 0x00184813.
Lemma F_84460 : fetch_word Ubsan.M.loaded_segments (0x84460 : word) = Some W_84460.
Proof. vm_refl. Qed.
Lemma D_84460 : decode_any W_84460 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84464 : bv 32 := 0x00081463.
Lemma F_84464 : fetch_word Ubsan.M.loaded_segments (0x84464 : word) = Some W_84464.
Proof. vm_refl. Qed.
Lemma D_84464 : decode_any W_84464 = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84468 : bv 32 := 0x88cfe06f.
Lemma F_84468 : fetch_word Ubsan.M.loaded_segments (0x84468 : word) = Some W_84468.
Proof. vm_refl. Qed.
Lemma D_84468 : decode_any W_84468 = Some (Jal 0 2089100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8446c : bv 32 := 0x00c40433.
Lemma F_8446c : fetch_word Ubsan.M.loaded_segments (0x8446c : word) = Some W_8446c.
Proof. vm_refl. Qed.
Lemma D_8446c : decode_any W_8446c = Some (Op ALU_ADD 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84470 : bv 32 := 0x0015859b.
Lemma F_84470 : fetch_word Ubsan.M.loaded_segments (0x84470 : word) = Some W_84470.
Proof. vm_refl. Qed.
Lemma D_84470 : decode_any W_84470 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84474 : bv 32 := 0x00cb0b33.
Lemma F_84474 : fetch_word Ubsan.M.loaded_segments (0x84474 : word) = Some W_84474.
Proof. vm_refl. Qed.
Lemma D_84474 : decode_any W_84474 = Some (Op ALU_ADD 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84478 : bv 32 := 0x00da8ab3.
Lemma F_84478 : fetch_word Ubsan.M.loaded_segments (0x84478 : word) = Some W_84478.
Proof. vm_refl. Qed.
Lemma D_84478 : decode_any W_84478 = Some (Op ALU_ADD 21 21 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8447c : bv 32 := 0x00078913.
Lemma F_8447c : fetch_word Ubsan.M.loaded_segments (0x8447c : word) = Some W_8447c.
Proof. vm_refl. Qed.
Lemma D_8447c : decode_any W_8447c = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84480 : bv 32 := 0x08013783.
Lemma F_84480 : fetch_word Ubsan.M.loaded_segments (0x84480 : word) = Some W_84480.
Proof. vm_refl. Qed.
Lemma D_84480 : decode_any W_84480 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_84484 : bv 32 := 0xf0f59ae3.
Lemma F_84484 : fetch_word Ubsan.M.loaded_segments (0x84484 : word) = Some W_84484.
Proof. vm_refl. Qed.
Lemma D_84484 : decode_any W_84484 = Some (Branch BC_NE 11 15 7956, 4%Z).
Proof. vm_refl. Qed.

Definition W_84488 : bv 32 := 0x00048463.
Lemma F_84488 : fetch_word Ubsan.M.loaded_segments (0x84488 : word) = Some W_84488.
Proof. vm_refl. Qed.
Lemma D_84488 : decode_any W_84488 = Some (Branch BC_EQ 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8448c : bv 32 := 0x12c0306f.
Lemma F_8448c : fetch_word Ubsan.M.loaded_segments (0x8448c : word) = Some W_8448c.
Proof. vm_refl. Qed.
Lemma D_8448c : decode_any W_8448c = Some (Jal 0 12588, 4%Z).
Proof. vm_refl. Qed.

Definition W_84490 : bv 32 := 0x00357593.
Lemma F_84490 : fetch_word Ubsan.M.loaded_segments (0x84490 : word) = Some W_84490.
Proof. vm_refl. Qed.
Lemma D_84490 : decode_any W_84490 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84494 : bv 32 := 0x00058463.
Lemma F_84494 : fetch_word Ubsan.M.loaded_segments (0x84494 : word) = Some W_84494.
Proof. vm_refl. Qed.
Lemma D_84494 : decode_any W_84494 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84498 : bv 32 := 0x85cfe06f.
Lemma F_84498 : fetch_word Ubsan.M.loaded_segments (0x84498 : word) = Some W_84498.
Proof. vm_refl. Qed.
Lemma D_84498 : decode_any W_84498 = Some (Jal 0 2089052, 4%Z).
Proof. vm_refl. Qed.

Definition W_8449c : bv 32 := 0xfffec613.
Lemma F_8449c : fetch_word Ubsan.M.loaded_segments (0x8449c : word) = Some W_8449c.
Proof. vm_refl. Qed.
Lemma D_8449c : decode_any W_8449c = Some (OpImm ALU_XOR 12 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_844a0 : bv 32 := 0x00271693.
Lemma F_844a0 : fetch_word Ubsan.M.loaded_segments (0x844a0 : word) = Some W_844a0.
Proof. vm_refl. Qed.
Lemma D_844a0 : decode_any W_844a0 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_844a4 : bv 32 := 0x05813e03.
Lemma F_844a4 : fetch_word Ubsan.M.loaded_segments (0x844a4 : word) = Some W_844a4.
Proof. vm_refl. Qed.
Lemma D_844a4 : decode_any W_844a4 = Some (Load SZ8 true 28 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_844a8 : bv 32 := 0x002e1793.
Lemma F_844a8 : fetch_word Ubsan.M.loaded_segments (0x844a8 : word) = Some W_844a8.
Proof. vm_refl. Qed.
Lemma D_844a8 : decode_any W_844a8 = Some (ShiftImm ALU_SLL 15 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_844ac : bv 32 := 0x03813883.
Lemma F_844ac : fetch_word Ubsan.M.loaded_segments (0x844ac : word) = Some W_844ac.
Proof. vm_refl. Qed.
Lemma D_844ac : decode_any W_844ac = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_844b0 : bv 32 := 0x03013803.
Lemma F_844b0 : fetch_word Ubsan.M.loaded_segments (0x844b0 : word) = Some W_844b0.
Proof. vm_refl. Qed.
Lemma D_844b0 : decode_any W_844b0 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_844b4 : bv 32 := 0x011808b3.
Lemma F_844b4 : fetch_word Ubsan.M.loaded_segments (0x844b4 : word) = Some W_844b4.
Proof. vm_refl. Qed.
Lemma D_844b4 : decode_any W_844b4 = Some (Op ALU_ADD 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_844b8 : bv 32 := 0x04813283.
Lemma F_844b8 : fetch_word Ubsan.M.loaded_segments (0x844b8 : word) = Some W_844b8.
Proof. vm_refl. Qed.
Lemma D_844b8 : decode_any W_844b8 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_844bc : bv 32 := 0x43f2d813.
Lemma F_844bc : fetch_word Ubsan.M.loaded_segments (0x844bc : word) = Some W_844bc.
Proof. vm_refl. Qed.
Lemma D_844bc : decode_any W_844bc = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_844c0 : bv 32 := 0x005872b3.
Lemma F_844c0 : fetch_word Ubsan.M.loaded_segments (0x844c0 : word) = Some W_844c0.
Proof. vm_refl. Qed.
Lemma D_844c0 : decode_any W_844c0 = Some (Op ALU_AND 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_844c4 : bv 32 := 0x003f7813.
Lemma F_844c4 : fetch_word Ubsan.M.loaded_segments (0x844c4 : word) = Some W_844c4.
Proof. vm_refl. Qed.
Lemma D_844c4 : decode_any W_844c4 = Some (OpImm ALU_AND 16 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_844c8 : bv 32 := 0x05013383.
Lemma F_844c8 : fetch_word Ubsan.M.loaded_segments (0x844c8 : word) = Some W_844c8.
Proof. vm_refl. Qed.
Lemma D_844c8 : decode_any W_844c8 = Some (Load SZ8 true 7 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_844cc : bv 32 := 0x02813303.
Lemma F_844cc : fetch_word Ubsan.M.loaded_segments (0x844cc : word) = Some W_844cc.
Proof. vm_refl. Qed.
Lemma D_844cc : decode_any W_844cc = Some (Load SZ8 true 6 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_844d0 : bv 32 := 0x4073033b.
Lemma F_844d0 : fetch_word Ubsan.M.loaded_segments (0x844d0 : word) = Some W_844d0.
Proof. vm_refl. Qed.
Lemma D_844d0 : decode_any W_844d0 = Some (Op32 ALU_SUB 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_844d4 : bv 32 := 0x00072713.
Lemma F_844d4 : fetch_word Ubsan.M.loaded_segments (0x844d4 : word) = Some W_844d4.
Proof. vm_refl. Qed.
Lemma D_844d4 : decode_any W_844d4 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_844d8 : bv 32 := 0x005882b3.
Lemma F_844d8 : fetch_word Ubsan.M.loaded_segments (0x844d8 : word) = Some W_844d8.
Proof. vm_refl. Qed.
Lemma D_844d8 : decode_any W_844d8 = Some (Op ALU_ADD 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_844dc : bv 32 := 0x00ff08b3.
Lemma F_844dc : fetch_word Ubsan.M.loaded_segments (0x844dc : word) = Some W_844dc.
Proof. vm_refl. Qed.
Lemma D_844dc : decode_any W_844dc = Some (Op ALU_ADD 17 30 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_844e0 : bv 32 := 0x407282bb.
Lemma F_844e0 : fetch_word Ubsan.M.loaded_segments (0x844e0 : word) = Some W_844e0.
Proof. vm_refl. Qed.
Lemma D_844e0 : decode_any W_844e0 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_844e4 : bv 32 := 0x04013383.
Lemma F_844e4 : fetch_word Ubsan.M.loaded_segments (0x844e4 : word) = Some W_844e4.
Proof. vm_refl. Qed.
Lemma D_844e4 : decode_any W_844e4 = Some (Load SZ8 true 7 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_844e8 : bv 32 := 0x407282bb.
Lemma F_844e8 : fetch_word Ubsan.M.loaded_segments (0x844e8 : word) = Some W_844e8.
Proof. vm_refl. Qed.
Lemma D_844e8 : decode_any W_844e8 = Some (Op32 ALU_SUB 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_844ec : bv 32 := 0x43f2d393.
Lemma F_844ec : fetch_word Ubsan.M.loaded_segments (0x844ec : word) = Some W_844ec.
Proof. vm_refl. Qed.
Lemma D_844ec : decode_any W_844ec = Some (ShiftImm ALU_SRA 7 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_844f0 : bv 32 := 0x0053f2b3.
Lemma F_844f0 : fetch_word Ubsan.M.loaded_segments (0x844f0 : word) = Some W_844f0.
Proof. vm_refl. Qed.
Lemma D_844f0 : decode_any W_844f0 = Some (Op ALU_AND 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_844f4 : bv 32 := 0x405302bb.
Lemma F_844f4 : fetch_word Ubsan.M.loaded_segments (0x844f4 : word) = Some W_844f4.
Proof. vm_refl. Qed.
Lemma D_844f4 : decode_any W_844f4 = Some (Op32 ALU_SUB 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_844f8 : bv 32 := 0x000e2313.
Lemma F_844f8 : fetch_word Ubsan.M.loaded_segments (0x844f8 : word) = Some W_844f8.
Proof. vm_refl. Qed.
Lemma D_844f8 : decode_any W_844f8 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_844fc : bv 32 := 0x00050393.
Lemma F_844fc : fetch_word Ubsan.M.loaded_segments (0x844fc : word) = Some W_844fc.
Proof. vm_refl. Qed.
Lemma D_844fc : decode_any W_844fc = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84500 : bv 32 := 0x00051463.
Lemma F_84500 : fetch_word Ubsan.M.loaded_segments (0x84500 : word) = Some W_84500.
Proof. vm_refl. Qed.
Lemma D_84500 : decode_any W_84500 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84504 : bv 32 := 0xff1fd06f.
Lemma F_84504 : fetch_word Ubsan.M.loaded_segments (0x84504 : word) = Some W_84504.
Proof. vm_refl. Qed.
Lemma D_84504 : decode_any W_84504 = Some (Jal 0 2088944, 4%Z).
Proof. vm_refl. Qed.

Definition W_84508 : bv 32 := 0x00080463.
Lemma F_84508 : fetch_word Ubsan.M.loaded_segments (0x84508 : word) = Some W_84508.
Proof. vm_refl. Qed.
Lemma D_84508 : decode_any W_84508 = Some (Branch BC_EQ 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8450c : bv 32 := 0xfe9fd06f.
Lemma F_8450c : fetch_word Ubsan.M.loaded_segments (0x8450c : word) = Some W_8450c.
Proof. vm_refl. Qed.
Lemma D_8450c : decode_any W_8450c = Some (Jal 0 2088936, 4%Z).
Proof. vm_refl. Qed.

Definition W_84510 : bv 32 := 0x00bf0e33.
Lemma F_84510 : fetch_word Ubsan.M.loaded_segments (0x84510 : word) = Some W_84510.
Proof. vm_refl. Qed.
Lemma D_84510 : decode_any W_84510 = Some (Op ALU_ADD 28 30 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84514 : bv 32 := 0x000e1463.
Lemma F_84514 : fetch_word Ubsan.M.loaded_segments (0x84514 : word) = Some W_84514.
Proof. vm_refl. Qed.
Lemma D_84514 : decode_any W_84514 = Some (Branch BC_NE 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84518 : bv 32 := 0xfddfd06f.
Lemma F_84518 : fetch_word Ubsan.M.loaded_segments (0x84518 : word) = Some W_84518.
Proof. vm_refl. Qed.
Lemma D_84518 : decode_any W_84518 = Some (Jal 0 2088924, 4%Z).
Proof. vm_refl. Qed.

Definition W_8451c : bv 32 := 0x00052f83.
Lemma F_8451c : fetch_word Ubsan.M.loaded_segments (0x8451c : word) = Some W_8451c.
Proof. vm_refl. Qed.
Lemma D_8451c : decode_any W_8451c = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84520 : bv 32 := 0x000e2403.
Lemma F_84520 : fetch_word Ubsan.M.loaded_segments (0x84520 : word) = Some W_84520.
Proof. vm_refl. Qed.
Lemma D_84520 : decode_any W_84520 = Some (Load SZ4 true 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84524 : bv 32 := 0x00cff4b3.
Lemma F_84524 : fetch_word Ubsan.M.loaded_segments (0x84524 : word) = Some W_84524.
Proof. vm_refl. Qed.
Lemma D_84524 : decode_any W_84524 = Some (Op ALU_AND 9 31 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84528 : bv 32 := 0xfff44413.
Lemma F_84528 : fetch_word Ubsan.M.loaded_segments (0x84528 : word) = Some W_84528.
Proof. vm_refl. Qed.
Lemma D_84528 : decode_any W_84528 = Some (OpImm ALU_XOR 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8452c : bv 32 := 0x008fefb3.
Lemma F_8452c : fetch_word Ubsan.M.loaded_segments (0x8452c : word) = Some W_8452c.
Proof. vm_refl. Qed.
Lemma D_8452c : decode_any W_8452c = Some (Op ALU_OR 31 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84530 : bv 32 := 0x01dfffb3.
Lemma F_84530 : fetch_word Ubsan.M.loaded_segments (0x84530 : word) = Some W_84530.
Proof. vm_refl. Qed.
Lemma D_84530 : decode_any W_84530 = Some (Op ALU_AND 31 31 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84534 : bv 32 := 0x009fe433.
Lemma F_84534 : fetch_word Ubsan.M.loaded_segments (0x84534 : word) = Some W_84534.
Proof. vm_refl. Qed.
Lemma D_84534 : decode_any W_84534 = Some (Op ALU_OR 8 31 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_84538 : bv 32 := 0x00768fb3.
Lemma F_84538 : fetch_word Ubsan.M.loaded_segments (0x84538 : word) = Some W_84538.
Proof. vm_refl. Qed.
Lemma D_84538 : decode_any W_84538 = Some (Op ALU_ADD 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8453c : bv 32 := 0x00852023.
Lemma F_8453c : fetch_word Ubsan.M.loaded_segments (0x8453c : word) = Some W_8453c.
Proof. vm_refl. Qed.
Lemma D_8453c : decode_any W_8453c = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84540 : bv 32 := 0x000f9463.
Lemma F_84540 : fetch_word Ubsan.M.loaded_segments (0x84540 : word) = Some W_84540.
Proof. vm_refl. Qed.
Lemma D_84540 : decode_any W_84540 = Some (Branch BC_NE 31 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84544 : bv 32 := 0xfb1fd06f.
Lemma F_84544 : fetch_word Ubsan.M.loaded_segments (0x84544 : word) = Some W_84544.
Proof. vm_refl. Qed.
Lemma D_84544 : decode_any W_84544 = Some (Jal 0 2088880, 4%Z).
Proof. vm_refl. Qed.

Definition W_84548 : bv 32 := 0x007fb3b3.
Lemma F_84548 : fetch_word Ubsan.M.loaded_segments (0x84548 : word) = Some W_84548.
Proof. vm_refl. Qed.
Lemma D_84548 : decode_any W_84548 = Some (Op ALU_SLTU 7 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8454c : bv 32 := 0x00e3c3b3.
Lemma F_8454c : fetch_word Ubsan.M.loaded_segments (0x8454c : word) = Some W_8454c.
Proof. vm_refl. Qed.
Lemma D_8454c : decode_any W_8454c = Some (Op ALU_XOR 7 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_84550 : bv 32 := 0x0013c393.
Lemma F_84550 : fetch_word Ubsan.M.loaded_segments (0x84550 : word) = Some W_84550.
Proof. vm_refl. Qed.
Lemma D_84550 : decode_any W_84550 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84554 : bv 32 := 0x00039463.
Lemma F_84554 : fetch_word Ubsan.M.loaded_segments (0x84554 : word) = Some W_84554.
Proof. vm_refl. Qed.
Lemma D_84554 : decode_any W_84554 = Some (Branch BC_NE 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84558 : bv 32 := 0xf9dfd06f.
Lemma F_84558 : fetch_word Ubsan.M.loaded_segments (0x84558 : word) = Some W_84558.
Proof. vm_refl. Qed.
Lemma D_84558 : decode_any W_84558 = Some (Jal 0 2088860, 4%Z).
Proof. vm_refl. Qed.

Definition W_8455c : bv 32 := 0x00b883b3.
Lemma F_8455c : fetch_word Ubsan.M.loaded_segments (0x8455c : word) = Some W_8455c.
Proof. vm_refl. Qed.
Lemma D_8455c : decode_any W_8455c = Some (Op ALU_ADD 7 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84560 : bv 32 := 0x00039463.
Lemma F_84560 : fetch_word Ubsan.M.loaded_segments (0x84560 : word) = Some W_84560.
Proof. vm_refl. Qed.
Lemma D_84560 : decode_any W_84560 = Some (Branch BC_NE 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84564 : bv 32 := 0xf91fd06f.
Lemma F_84564 : fetch_word Ubsan.M.loaded_segments (0x84564 : word) = Some W_84564.
Proof. vm_refl. Qed.
Lemma D_84564 : decode_any W_84564 = Some (Jal 0 2088848, 4%Z).
Proof. vm_refl. Qed.

Definition W_84568 : bv 32 := 0x01c3b3b3.
Lemma F_84568 : fetch_word Ubsan.M.loaded_segments (0x84568 : word) = Some W_84568.
Proof. vm_refl. Qed.
Lemma D_84568 : decode_any W_84568 = Some (Op ALU_SLTU 7 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8456c : bv 32 := 0x0063c3b3.
Lemma F_8456c : fetch_word Ubsan.M.loaded_segments (0x8456c : word) = Some W_8456c.
Proof. vm_refl. Qed.
Lemma D_8456c : decode_any W_8456c = Some (Op ALU_XOR 7 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84570 : bv 32 := 0x0013c393.
Lemma F_84570 : fetch_word Ubsan.M.loaded_segments (0x84570 : word) = Some W_84570.
Proof. vm_refl. Qed.
Lemma D_84570 : decode_any W_84570 = Some (OpImm ALU_XOR 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84574 : bv 32 := 0x00039463.
Lemma F_84574 : fetch_word Ubsan.M.loaded_segments (0x84574 : word) = Some W_84574.
Proof. vm_refl. Qed.
Lemma D_84574 : decode_any W_84574 = Some (Branch BC_NE 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84578 : bv 32 := 0xf7dfd06f.
Lemma F_84578 : fetch_word Ubsan.M.loaded_segments (0x84578 : word) = Some W_84578.
Proof. vm_refl. Qed.
Lemma D_84578 : decode_any W_84578 = Some (Jal 0 2088828, 4%Z).
Proof. vm_refl. Qed.

Definition W_8457c : bv 32 := 0x0012829b.
Lemma F_8457c : fetch_word Ubsan.M.loaded_segments (0x8457c : word) = Some W_8457c.
Proof. vm_refl. Qed.
Lemma D_8457c : decode_any W_8457c = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84580 : bv 32 := 0x00f585b3.
Lemma F_84580 : fetch_word Ubsan.M.loaded_segments (0x84580 : word) = Some W_84580.
Proof. vm_refl. Qed.
Lemma D_84580 : decode_any W_84580 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84584 : bv 32 := 0x00d50533.
Lemma F_84584 : fetch_word Ubsan.M.loaded_segments (0x84584 : word) = Some W_84584.
Proof. vm_refl. Qed.
Lemma D_84584 : decode_any W_84584 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84588 : bv 32 := 0x000f8393.
Lemma F_84588 : fetch_word Ubsan.M.loaded_segments (0x84588 : word) = Some W_84588.
Proof. vm_refl. Qed.
Lemma D_84588 : decode_any W_84588 = Some (OpImm ALU_ADD 7 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8458c : bv 32 := 0xf6029ae3.
Lemma F_8458c : fetch_word Ubsan.M.loaded_segments (0x8458c : word) = Some W_8458c.
Proof. vm_refl. Qed.
Lemma D_8458c : decode_any W_8458c = Some (Branch BC_NE 5 0 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_84590 : bv 32 := 0x0280306f.
Lemma F_84590 : fetch_word Ubsan.M.loaded_segments (0x84590 : word) = Some W_84590.
Proof. vm_refl. Qed.
Lemma D_84590 : decode_any W_84590 = Some (Jal 0 12328, 4%Z).
Proof. vm_refl. Qed.

Definition W_84594 : bv 32 := 0x18008263.
Lemma F_84594 : fetch_word Ubsan.M.loaded_segments (0x84594 : word) = Some W_84594.
Proof. vm_refl. Qed.
Lemma D_84594 : decode_any W_84594 = Some (Branch BC_EQ 1 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_84598 : bv 32 := 0x00000593.
Lemma F_84598 : fetch_word Ubsan.M.loaded_segments (0x84598 : word) = Some W_84598.
Proof. vm_refl. Qed.
Lemma D_84598 : decode_any W_84598 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8459c : bv 32 := 0xffffc613.
Lemma F_8459c : fetch_word Ubsan.M.loaded_segments (0x8459c : word) = Some W_8459c.
Proof. vm_refl. Qed.
Lemma D_8459c : decode_any W_8459c = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_845a0 : bv 32 := 0x00c13023.
Lemma F_845a0 : fetch_word Ubsan.M.loaded_segments (0x845a0 : word) = Some W_845a0.
Proof. vm_refl. Qed.
Lemma D_845a0 : decode_any W_845a0 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_845a4 : bv 32 := 0xfffdc293.
Lemma F_845a4 : fetch_word Ubsan.M.loaded_segments (0x845a4 : word) = Some W_845a4.
Proof. vm_refl. Qed.
Lemma D_845a4 : decode_any W_845a4 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_845a8 : bv 32 := 0x00271393.
Lemma F_845a8 : fetch_word Ubsan.M.loaded_segments (0x845a8 : word) = Some W_845a8.
Proof. vm_refl. Qed.
Lemma D_845a8 : decode_any W_845a8 = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_845ac : bv 32 := 0x05813683.
Lemma F_845ac : fetch_word Ubsan.M.loaded_segments (0x845ac : word) = Some W_845ac.
Proof. vm_refl. Qed.
Lemma D_845ac : decode_any W_845ac = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_845b0 : bv 32 := 0x00269693.
Lemma F_845b0 : fetch_word Ubsan.M.loaded_segments (0x845b0 : word) = Some W_845b0.
Proof. vm_refl. Qed.
Lemma D_845b0 : decode_any W_845b0 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_845b4 : bv 32 := 0x003cfb93.
Lemma F_845b4 : fetch_word Ubsan.M.loaded_segments (0x845b4 : word) = Some W_845b4.
Proof. vm_refl. Qed.
Lemma D_845b4 : decode_any W_845b4 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_845b8 : bv 32 := 0x0037f613.
Lemma F_845b8 : fetch_word Ubsan.M.loaded_segments (0x845b8 : word) = Some W_845b8.
Proof. vm_refl. Qed.
Lemma D_845b8 : decode_any W_845b8 = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_845bc : bv 32 := 0x05013483.
Lemma F_845bc : fetch_word Ubsan.M.loaded_segments (0x845bc : word) = Some W_845bc.
Proof. vm_refl. Qed.
Lemma D_845bc : decode_any W_845bc = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_845c0 : bv 32 := 0x02813803.
Lemma F_845c0 : fetch_word Ubsan.M.loaded_segments (0x845c0 : word) = Some W_845c0.
Proof. vm_refl. Qed.
Lemma D_845c0 : decode_any W_845c0 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_845c4 : bv 32 := 0x4098083b.
Lemma F_845c4 : fetch_word Ubsan.M.loaded_segments (0x845c4 : word) = Some W_845c4.
Proof. vm_refl. Qed.
Lemma D_845c4 : decode_any W_845c4 = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_845c8 : bv 32 := 0x03813883.
Lemma F_845c8 : fetch_word Ubsan.M.loaded_segments (0x845c8 : word) = Some W_845c8.
Proof. vm_refl. Qed.
Lemma D_845c8 : decode_any W_845c8 = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_845cc : bv 32 := 0x03013e03.
Lemma F_845cc : fetch_word Ubsan.M.loaded_segments (0x845cc : word) = Some W_845cc.
Proof. vm_refl. Qed.
Lemma D_845cc : decode_any W_845cc = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_845d0 : bv 32 := 0x011e08b3.
Lemma F_845d0 : fetch_word Ubsan.M.loaded_segments (0x845d0 : word) = Some W_845d0.
Proof. vm_refl. Qed.
Lemma D_845d0 : decode_any W_845d0 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_845d4 : bv 32 := 0x04813a03.
Lemma F_845d4 : fetch_word Ubsan.M.loaded_segments (0x845d4 : word) = Some W_845d4.
Proof. vm_refl. Qed.
Lemma D_845d4 : decode_any W_845d4 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_845d8 : bv 32 := 0x43fa5e13.
Lemma F_845d8 : fetch_word Ubsan.M.loaded_segments (0x845d8 : word) = Some W_845d8.
Proof. vm_refl. Qed.
Lemma D_845d8 : decode_any W_845d8 = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_845dc : bv 32 := 0x01013983.
Lemma F_845dc : fetch_word Ubsan.M.loaded_segments (0x845dc : word) = Some W_845dc.
Proof. vm_refl. Qed.
Lemma D_845dc : decode_any W_845dc = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_845e0 : bv 32 := 0x0019f993.
Lemma F_845e0 : fetch_word Ubsan.M.loaded_segments (0x845e0 : word) = Some W_845e0.
Proof. vm_refl. Qed.
Lemma D_845e0 : decode_any W_845e0 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_845e4 : bv 32 := 0x001d7c13.
Lemma F_845e4 : fetch_word Ubsan.M.loaded_segments (0x845e4 : word) = Some W_845e4.
Proof. vm_refl. Qed.
Lemma D_845e4 : decode_any W_845e4 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_845e8 : bv 32 := 0x01f00093.
Lemma F_845e8 : fetch_word Ubsan.M.loaded_segments (0x845e8 : word) = Some W_845e8.
Proof. vm_refl. Qed.
Lemma D_845e8 : decode_any W_845e8 = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_845ec : bv 32 := 0x014e7e33.
Lemma F_845ec : fetch_word Ubsan.M.loaded_segments (0x845ec : word) = Some W_845ec.
Proof. vm_refl. Qed.
Lemma D_845ec : decode_any W_845ec = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_845f0 : bv 32 := 0x409888bb.
Lemma F_845f0 : fetch_word Ubsan.M.loaded_segments (0x845f0 : word) = Some W_845f0.
Proof. vm_refl. Qed.
Lemma D_845f0 : decode_any W_845f0 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_845f4 : bv 32 := 0x00d78a33.
Lemma F_845f4 : fetch_word Ubsan.M.loaded_segments (0x845f4 : word) = Some W_845f4.
Proof. vm_refl. Qed.
Lemma D_845f4 : decode_any W_845f4 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_845f8 : bv 32 := 0x00163b13.
Lemma F_845f8 : fetch_word Ubsan.M.loaded_segments (0x845f8 : word) = Some W_845f8.
Proof. vm_refl. Qed.
Lemma D_845f8 : decode_any W_845f8 = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_845fc : bv 32 := 0x04013603.
Lemma F_845fc : fetch_word Ubsan.M.loaded_segments (0x845fc : word) = Some W_845fc.
Proof. vm_refl. Qed.
Lemma D_845fc : decode_any W_845fc = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_84600 : bv 32 := 0x40c8863b.
Lemma F_84600 : fetch_word Ubsan.M.loaded_segments (0x84600 : word) = Some W_84600.
Proof. vm_refl. Qed.
Lemma D_84600 : decode_any W_84600 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84604 : bv 32 := 0x01c6063b.
Lemma F_84604 : fetch_word Ubsan.M.loaded_segments (0x84604 : word) = Some W_84604.
Proof. vm_refl. Qed.
Lemma D_84604 : decode_any W_84604 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84608 : bv 32 := 0x43f65893.
Lemma F_84608 : fetch_word Ubsan.M.loaded_segments (0x84608 : word) = Some W_84608.
Proof. vm_refl. Qed.
Lemma D_84608 : decode_any W_84608 = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_8460c : bv 32 := 0x00c8f633.
Lemma F_8460c : fetch_word Ubsan.M.loaded_segments (0x8460c : word) = Some W_8460c.
Proof. vm_refl. Qed.
Lemma D_8460c : decode_any W_8460c = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84610 : bv 32 := 0x40c80e3b.
Lemma F_84610 : fetch_word Ubsan.M.loaded_segments (0x84610 : word) = Some W_84610.
Proof. vm_refl. Qed.
Lemma D_84610 : decode_any W_84610 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84614 : bv 32 := 0x00072493.
Lemma F_84614 : fetch_word Ubsan.M.loaded_segments (0x84614 : word) = Some W_84614.
Proof. vm_refl. Qed.
Lemma D_84614 : decode_any W_84614 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84618 : bv 32 := 0x000c8813.
Lemma F_84618 : fetch_word Ubsan.M.loaded_segments (0x84618 : word) = Some W_84618.
Proof. vm_refl. Qed.
Lemma D_84618 : decode_any W_84618 = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8461c : bv 32 := 0x00b78d33.
Lemma F_8461c : fetch_word Ubsan.M.loaded_segments (0x8461c : word) = Some W_8461c.
Proof. vm_refl. Qed.
Lemma D_8461c : decode_any W_8461c = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84620 : bv 32 := 0x01a03633.
Lemma F_84620 : fetch_word Ubsan.M.loaded_segments (0x84620 : word) = Some W_84620.
Proof. vm_refl. Qed.
Lemma D_84620 : decode_any W_84620 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_84624 : bv 32 := 0x00cb7633.
Lemma F_84624 : fetch_word Ubsan.M.loaded_segments (0x84624 : word) = Some W_84624.
Proof. vm_refl. Qed.
Lemma D_84624 : decode_any W_84624 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84628 : bv 32 := 0x04098a63.
Lemma F_84628 : fetch_word Ubsan.M.loaded_segments (0x84628 : word) = Some W_84628.
Proof. vm_refl. Qed.
Lemma D_84628 : decode_any W_84628 = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_8462c : bv 32 := 0x00061463.
Lemma F_8462c : fetch_word Ubsan.M.loaded_segments (0x8462c : word) = Some W_8462c.
Proof. vm_refl. Qed.
Lemma D_8462c : decode_any W_8462c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84630 : bv 32 := 0xec5fd06f.
Lemma F_84630 : fetch_word Ubsan.M.loaded_segments (0x84630 : word) = Some W_84630.
Proof. vm_refl. Qed.
Lemma D_84630 : decode_any W_84630 = Some (Jal 0 2088644, 4%Z).
Proof. vm_refl. Qed.

Definition W_84634 : bv 32 := 0x02000613.
Lemma F_84634 : fetch_word Ubsan.M.loaded_segments (0x84634 : word) = Some W_84634.
Proof. vm_refl. Qed.
Lemma D_84634 : decode_any W_84634 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84638 : bv 32 := 0x00cf1463.
Lemma F_84638 : fetch_word Ubsan.M.loaded_segments (0x84638 : word) = Some W_84638.
Proof. vm_refl. Qed.
Lemma D_84638 : decode_any W_84638 = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8463c : bv 32 := 0xeb9fd06f.
Lemma F_8463c : fetch_word Ubsan.M.loaded_segments (0x8463c : word) = Some W_8463c.
Proof. vm_refl. Qed.
Lemma D_8463c : decode_any W_8463c = Some (Jal 0 2088632, 4%Z).
Proof. vm_refl. Qed.

Definition W_84640 : bv 32 := 0x000d2603.
Lemma F_84640 : fetch_word Ubsan.M.loaded_segments (0x84640 : word) = Some W_84640.
Proof. vm_refl. Qed.
Lemma D_84640 : decode_any W_84640 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84644 : bv 32 := 0x01d61abb.
Lemma F_84644 : fetch_word Ubsan.M.loaded_segments (0x84644 : word) = Some W_84644.
Proof. vm_refl. Qed.
Lemma D_84644 : decode_any W_84644 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84648 : bv 32 := 0x040c1663.
Lemma F_84648 : fetch_word Ubsan.M.loaded_segments (0x84648 : word) = Some W_84648.
Proof. vm_refl. Qed.
Lemma D_84648 : decode_any W_84648 = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_8464c : bv 32 := 0xffb00613.
Lemma F_8464c : fetch_word Ubsan.M.loaded_segments (0x8464c : word) = Some W_8464c.
Proof. vm_refl. Qed.
Lemma D_8464c : decode_any W_8464c = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_84650 : bv 32 := 0x01a67463.
Lemma F_84650 : fetch_word Ubsan.M.loaded_segments (0x84650 : word) = Some W_84650.
Proof. vm_refl. Qed.
Lemma D_84650 : decode_any W_84650 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84654 : bv 32 := 0xea1fd06f.
Lemma F_84654 : fetch_word Ubsan.M.loaded_segments (0x84654 : word) = Some W_84654.
Proof. vm_refl. Qed.
Lemma D_84654 : decode_any W_84654 = Some (Jal 0 2088608, 4%Z).
Proof. vm_refl. Qed.

Definition W_84658 : bv 32 := 0x0080f463.
Lemma F_84658 : fetch_word Ubsan.M.loaded_segments (0x84658 : word) = Some W_84658.
Proof. vm_refl. Qed.
Lemma D_84658 : decode_any W_84658 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8465c : bv 32 := 0xe99fd06f.
Lemma F_8465c : fetch_word Ubsan.M.loaded_segments (0x8465c : word) = Some W_8465c.
Proof. vm_refl. Qed.
Lemma D_8465c : decode_any W_8465c = Some (Jal 0 2088600, 4%Z).
Proof. vm_refl. Qed.

Definition W_84660 : bv 32 := 0x004d2603.
Lemma F_84660 : fetch_word Ubsan.M.loaded_segments (0x84660 : word) = Some W_84660.
Proof. vm_refl. Qed.
Lemma D_84660 : decode_any W_84660 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84664 : bv 32 := 0x00013883.
Lemma F_84664 : fetch_word Ubsan.M.loaded_segments (0x84664 : word) = Some W_84664.
Proof. vm_refl. Qed.
Lemma D_84664 : decode_any W_84664 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84668 : bv 32 := 0x011af8b3.
Lemma F_84668 : fetch_word Ubsan.M.loaded_segments (0x84668 : word) = Some W_84668.
Proof. vm_refl. Qed.
Lemma D_84668 : decode_any W_84668 = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8466c : bv 32 := 0x0086563b.
Lemma F_8466c : fetch_word Ubsan.M.loaded_segments (0x8466c : word) = Some W_8466c.
Proof. vm_refl. Qed.
Lemma D_8466c : decode_any W_8466c = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84670 : bv 32 := 0x01f67633.
Lemma F_84670 : fetch_word Ubsan.M.loaded_segments (0x84670 : word) = Some W_84670.
Proof. vm_refl. Qed.
Lemma D_84670 : decode_any W_84670 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84674 : bv 32 := 0x01166ab3.
Lemma F_84674 : fetch_word Ubsan.M.loaded_segments (0x84674 : word) = Some W_84674.
Proof. vm_refl. Qed.
Lemma D_84674 : decode_any W_84674 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84678 : bv 32 := 0x01c0006f.
Lemma F_84678 : fetch_word Ubsan.M.loaded_segments (0x84678 : word) = Some W_84678.
Proof. vm_refl. Qed.
Lemma D_84678 : decode_any W_84678 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8467c : bv 32 := 0x00061463.
Lemma F_8467c : fetch_word Ubsan.M.loaded_segments (0x8467c : word) = Some W_8467c.
Proof. vm_refl. Qed.
Lemma D_8467c : decode_any W_8467c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84680 : bv 32 := 0xe75fd06f.
Lemma F_84680 : fetch_word Ubsan.M.loaded_segments (0x84680 : word) = Some W_84680.
Proof. vm_refl. Qed.
Lemma D_84680 : decode_any W_84680 = Some (Jal 0 2088564, 4%Z).
Proof. vm_refl. Qed.

Definition W_84684 : bv 32 := 0x0080f463.
Lemma F_84684 : fetch_word Ubsan.M.loaded_segments (0x84684 : word) = Some W_84684.
Proof. vm_refl. Qed.
Lemma D_84684 : decode_any W_84684 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84688 : bv 32 := 0xe6dfd06f.
Lemma F_84688 : fetch_word Ubsan.M.loaded_segments (0x84688 : word) = Some W_84688.
Proof. vm_refl. Qed.
Lemma D_84688 : decode_any W_84688 = Some (Jal 0 2088556, 4%Z).
Proof. vm_refl. Qed.

Definition W_8468c : bv 32 := 0x000d2603.
Lemma F_8468c : fetch_word Ubsan.M.loaded_segments (0x8468c : word) = Some W_8468c.
Proof. vm_refl. Qed.
Lemma D_8468c : decode_any W_8468c = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84690 : bv 32 := 0x00865abb.
Lemma F_84690 : fetch_word Ubsan.M.loaded_segments (0x84690 : word) = Some W_84690.
Proof. vm_refl. Qed.
Lemma D_84690 : decode_any W_84690 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84694 : bv 32 := 0x000b8463.
Lemma F_84694 : fetch_word Ubsan.M.loaded_segments (0x84694 : word) = Some W_84694.
Proof. vm_refl. Qed.
Lemma D_84694 : decode_any W_84694 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84698 : bv 32 := 0xe5dfd06f.
Lemma F_84698 : fetch_word Ubsan.M.loaded_segments (0x84698 : word) = Some W_84698.
Proof. vm_refl. Qed.
Lemma D_84698 : decode_any W_84698 = Some (Jal 0 2088540, 4%Z).
Proof. vm_refl. Qed.

Definition W_8469c : bv 32 := 0x000c9463.
Lemma F_8469c : fetch_word Ubsan.M.loaded_segments (0x8469c : word) = Some W_8469c.
Proof. vm_refl. Qed.
Lemma D_8469c : decode_any W_8469c = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_846a0 : bv 32 := 0xe55fd06f.
Lemma F_846a0 : fetch_word Ubsan.M.loaded_segments (0x846a0 : word) = Some W_846a0.
Proof. vm_refl. Qed.
Lemma D_846a0 : decode_any W_846a0 = Some (Jal 0 2088532, 4%Z).
Proof. vm_refl. Qed.

Definition W_846a4 : bv 32 := 0x000ca603.
Lemma F_846a4 : fetch_word Ubsan.M.loaded_segments (0x846a4 : word) = Some W_846a4.
Proof. vm_refl. Qed.
Lemma D_846a4 : decode_any W_846a4 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_846a8 : bv 32 := 0x005678b3.
Lemma F_846a8 : fetch_word Ubsan.M.loaded_segments (0x846a8 : word) = Some W_846a8.
Proof. vm_refl. Qed.
Lemma D_846a8 : decode_any W_846a8 = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_846ac : bv 32 := 0xfff64613.
Lemma F_846ac : fetch_word Ubsan.M.loaded_segments (0x846ac : word) = Some W_846ac.
Proof. vm_refl. Qed.
Lemma D_846ac : decode_any W_846ac = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_846b0 : bv 32 := 0x00cae633.
Lemma F_846b0 : fetch_word Ubsan.M.loaded_segments (0x846b0 : word) = Some W_846b0.
Proof. vm_refl. Qed.
Lemma D_846b0 : decode_any W_846b0 = Some (Op ALU_OR 12 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_846b4 : bv 32 := 0x01b67633.
Lemma F_846b4 : fetch_word Ubsan.M.loaded_segments (0x846b4 : word) = Some W_846b4.
Proof. vm_refl. Qed.
Lemma D_846b4 : decode_any W_846b4 = Some (Op ALU_AND 12 12 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_846b8 : bv 32 := 0x01166633.
Lemma F_846b8 : fetch_word Ubsan.M.loaded_segments (0x846b8 : word) = Some W_846b8.
Proof. vm_refl. Qed.
Lemma D_846b8 : decode_any W_846b8 = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_846bc : bv 32 := 0x01038ab3.
Lemma F_846bc : fetch_word Ubsan.M.loaded_segments (0x846bc : word) = Some W_846bc.
Proof. vm_refl. Qed.
Lemma D_846bc : decode_any W_846bc = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_846c0 : bv 32 := 0x00cca023.
Lemma F_846c0 : fetch_word Ubsan.M.loaded_segments (0x846c0 : word) = Some W_846c0.
Proof. vm_refl. Qed.
Lemma D_846c0 : decode_any W_846c0 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_846c4 : bv 32 := 0x000a9463.
Lemma F_846c4 : fetch_word Ubsan.M.loaded_segments (0x846c4 : word) = Some W_846c4.
Proof. vm_refl. Qed.
Lemma D_846c4 : decode_any W_846c4 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_846c8 : bv 32 := 0xe2dfd06f.
Lemma F_846c8 : fetch_word Ubsan.M.loaded_segments (0x846c8 : word) = Some W_846c8.
Proof. vm_refl. Qed.
Lemma D_846c8 : decode_any W_846c8 = Some (Jal 0 2088492, 4%Z).
Proof. vm_refl. Qed.

Definition W_846cc : bv 32 := 0x010ab633.
Lemma F_846cc : fetch_word Ubsan.M.loaded_segments (0x846cc : word) = Some W_846cc.
Proof. vm_refl. Qed.
Lemma D_846cc : decode_any W_846cc = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_846d0 : bv 32 := 0x00964633.
Lemma F_846d0 : fetch_word Ubsan.M.loaded_segments (0x846d0 : word) = Some W_846d0.
Proof. vm_refl. Qed.
Lemma D_846d0 : decode_any W_846d0 = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_846d4 : bv 32 := 0x00164613.
Lemma F_846d4 : fetch_word Ubsan.M.loaded_segments (0x846d4 : word) = Some W_846d4.
Proof. vm_refl. Qed.
Lemma D_846d4 : decode_any W_846d4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_846d8 : bv 32 := 0x00061463.
Lemma F_846d8 : fetch_word Ubsan.M.loaded_segments (0x846d8 : word) = Some W_846d8.
Proof. vm_refl. Qed.
Lemma D_846d8 : decode_any W_846d8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_846dc : bv 32 := 0xe19fd06f.
Lemma F_846dc : fetch_word Ubsan.M.loaded_segments (0x846dc : word) = Some W_846dc.
Proof. vm_refl. Qed.
Lemma D_846dc : decode_any W_846dc = Some (Jal 0 2088472, 4%Z).
Proof. vm_refl. Qed.

Definition W_846e0 : bv 32 := 0x00ba0633.
Lemma F_846e0 : fetch_word Ubsan.M.loaded_segments (0x846e0 : word) = Some W_846e0.
Proof. vm_refl. Qed.
Lemma D_846e0 : decode_any W_846e0 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_846e4 : bv 32 := 0x00061463.
Lemma F_846e4 : fetch_word Ubsan.M.loaded_segments (0x846e4 : word) = Some W_846e4.
Proof. vm_refl. Qed.
Lemma D_846e4 : decode_any W_846e4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_846e8 : bv 32 := 0xe0dfd06f.
Lemma F_846e8 : fetch_word Ubsan.M.loaded_segments (0x846e8 : word) = Some W_846e8.
Proof. vm_refl. Qed.
Lemma D_846e8 : decode_any W_846e8 = Some (Jal 0 2088460, 4%Z).
Proof. vm_refl. Qed.

Definition W_846ec : bv 32 := 0x01a63633.
Lemma F_846ec : fetch_word Ubsan.M.loaded_segments (0x846ec : word) = Some W_846ec.
Proof. vm_refl. Qed.
Lemma D_846ec : decode_any W_846ec = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_846f0 : bv 32 := 0x07813803.
Lemma F_846f0 : fetch_word Ubsan.M.loaded_segments (0x846f0 : word) = Some W_846f0.
Proof. vm_refl. Qed.
Lemma D_846f0 : decode_any W_846f0 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_846f4 : bv 32 := 0x01064633.
Lemma F_846f4 : fetch_word Ubsan.M.loaded_segments (0x846f4 : word) = Some W_846f4.
Proof. vm_refl. Qed.
Lemma D_846f4 : decode_any W_846f4 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_846f8 : bv 32 := 0x00164613.
Lemma F_846f8 : fetch_word Ubsan.M.loaded_segments (0x846f8 : word) = Some W_846f8.
Proof. vm_refl. Qed.
Lemma D_846f8 : decode_any W_846f8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_846fc : bv 32 := 0x00061463.
Lemma F_846fc : fetch_word Ubsan.M.loaded_segments (0x846fc : word) = Some W_846fc.
Proof. vm_refl. Qed.
Lemma D_846fc : decode_any W_846fc = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84700 : bv 32 := 0xdf5fd06f.
Lemma F_84700 : fetch_word Ubsan.M.loaded_segments (0x84700 : word) = Some W_84700.
Proof. vm_refl. Qed.
Lemma D_84700 : decode_any W_84700 = Some (Jal 0 2088436, 4%Z).
Proof. vm_refl. Qed.

Definition W_84704 : bv 32 := 0x001e0e1b.
Lemma F_84704 : fetch_word Ubsan.M.loaded_segments (0x84704 : word) = Some W_84704.
Proof. vm_refl. Qed.
Lemma D_84704 : decode_any W_84704 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84708 : bv 32 := 0x00d585b3.
Lemma F_84708 : fetch_word Ubsan.M.loaded_segments (0x84708 : word) = Some W_84708.
Proof. vm_refl. Qed.
Lemma D_84708 : decode_any W_84708 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8470c : bv 32 := 0x007c8cb3.
Lemma F_8470c : fetch_word Ubsan.M.loaded_segments (0x8470c : word) = Some W_8470c.
Proof. vm_refl. Qed.
Lemma D_8470c : decode_any W_8470c = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84710 : bv 32 := 0x000a8813.
Lemma F_84710 : fetch_word Ubsan.M.loaded_segments (0x84710 : word) = Some W_84710.
Proof. vm_refl. Qed.
Lemma D_84710 : decode_any W_84710 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84714 : bv 32 := 0xf00e14e3.
Lemma F_84714 : fetch_word Ubsan.M.loaded_segments (0x84714 : word) = Some W_84714.
Proof. vm_refl. Qed.
Lemma D_84714 : decode_any W_84714 = Some (Branch BC_NE 28 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_84718 : bv 32 := 0x02013583.
Lemma F_84718 : fetch_word Ubsan.M.loaded_segments (0x84718 : word) = Some W_84718.
Proof. vm_refl. Qed.
Lemma D_84718 : decode_any W_84718 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8471c : bv 32 := 0x16059e63.
Lemma F_8471c : fetch_word Ubsan.M.loaded_segments (0x8471c : word) = Some W_8471c.
Proof. vm_refl. Qed.
Lemma D_8471c : decode_any W_8471c = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_84720 : bv 32 := 0xffffc693.
Lemma F_84720 : fetch_word Ubsan.M.loaded_segments (0x84720 : word) = Some W_84720.
Proof. vm_refl. Qed.
Lemma D_84720 : decode_any W_84720 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84724 : bv 32 := 0x00271293.
Lemma F_84724 : fetch_word Ubsan.M.loaded_segments (0x84724 : word) = Some W_84724.
Proof. vm_refl. Qed.
Lemma D_84724 : decode_any W_84724 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84728 : bv 32 := 0x05813383.
Lemma F_84728 : fetch_word Ubsan.M.loaded_segments (0x84728 : word) = Some W_84728.
Proof. vm_refl. Qed.
Lemma D_84728 : decode_any W_84728 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8472c : bv 32 := 0x00239393.
Lemma F_8472c : fetch_word Ubsan.M.loaded_segments (0x8472c : word) = Some W_8472c.
Proof. vm_refl. Qed.
Lemma D_8472c : decode_any W_8472c = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84730 : bv 32 := 0x00337613.
Lemma F_84730 : fetch_word Ubsan.M.loaded_segments (0x84730 : word) = Some W_84730.
Proof. vm_refl. Qed.
Lemma D_84730 : decode_any W_84730 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84734 : bv 32 := 0x00397793.
Lemma F_84734 : fetch_word Ubsan.M.loaded_segments (0x84734 : word) = Some W_84734.
Proof. vm_refl. Qed.
Lemma D_84734 : decode_any W_84734 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84738 : bv 32 := 0x07013a03.
Lemma F_84738 : fetch_word Ubsan.M.loaded_segments (0x84738 : word) = Some W_84738.
Proof. vm_refl. Qed.
Lemma D_84738 : decode_any W_84738 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8473c : bv 32 := 0x002a1a13.
Lemma F_8473c : fetch_word Ubsan.M.loaded_segments (0x8473c : word) = Some W_8473c.
Proof. vm_refl. Qed.
Lemma D_8473c : decode_any W_8473c = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84740 : bv 32 := 0x00072b93.
Lemma F_84740 : fetch_word Ubsan.M.loaded_segments (0x84740 : word) = Some W_84740.
Proof. vm_refl. Qed.
Lemma D_84740 : decode_any W_84740 = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84744 : bv 32 := 0x02000c93.
Lemma F_84744 : fetch_word Ubsan.M.loaded_segments (0x84744 : word) = Some W_84744.
Proof. vm_refl. Qed.
Lemma D_84744 : decode_any W_84744 = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84748 : bv 32 := 0xffb00d13.
Lemma F_84748 : fetch_word Ubsan.M.loaded_segments (0x84748 : word) = Some W_84748.
Proof. vm_refl. Qed.
Lemma D_84748 : decode_any W_84748 = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_8474c : bv 32 := 0x0017b793.
Lemma F_8474c : fetch_word Ubsan.M.loaded_segments (0x8474c : word) = Some W_8474c.
Proof. vm_refl. Qed.
Lemma D_8474c : decode_any W_8474c = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84750 : bv 32 := 0x02f13023.
Lemma F_84750 : fetch_word Ubsan.M.loaded_segments (0x84750 : word) = Some W_84750.
Proof. vm_refl. Qed.
Lemma D_84750 : decode_any W_84750 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84754 : bv 32 := 0x00163613.
Lemma F_84754 : fetch_word Ubsan.M.loaded_segments (0x84754 : word) = Some W_84754.
Proof. vm_refl. Qed.
Lemma D_84754 : decode_any W_84754 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84758 : bv 32 := 0x00c13823.
Lemma F_84758 : fetch_word Ubsan.M.loaded_segments (0x84758 : word) = Some W_84758.
Proof. vm_refl. Qed.
Lemma D_84758 : decode_any W_84758 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8475c : bv 32 := 0x01f00993.
Lemma F_8475c : fetch_word Ubsan.M.loaded_segments (0x8475c : word) = Some W_8475c.
Proof. vm_refl. Qed.
Lemma D_8475c : decode_any W_8475c = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84760 : bv 32 := 0x00030b13.
Lemma F_84760 : fetch_word Ubsan.M.loaded_segments (0x84760 : word) = Some W_84760.
Proof. vm_refl. Qed.
Lemma D_84760 : decode_any W_84760 = Some (OpImm ALU_ADD 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84764 : bv 32 := 0x00090c13.
Lemma F_84764 : fetch_word Ubsan.M.loaded_segments (0x84764 : word) = Some W_84764.
Proof. vm_refl. Qed.
Lemma D_84764 : decode_any W_84764 = Some (OpImm ALU_ADD 24 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84768 : bv 32 := 0x07013603.
Lemma F_84768 : fetch_word Ubsan.M.loaded_segments (0x84768 : word) = Some W_84768.
Proof. vm_refl. Qed.
Lemma D_84768 : decode_any W_84768 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8476c : bv 32 := 0x0a060e63.
Lemma F_8476c : fetch_word Ubsan.M.loaded_segments (0x8476c : word) = Some W_8476c.
Proof. vm_refl. Qed.
Lemma D_8476c : decode_any W_8476c = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_84770 : bv 32 := 0x00000d93.
Lemma F_84770 : fetch_word Ubsan.M.loaded_segments (0x84770 : word) = Some W_84770.
Proof. vm_refl. Qed.
Lemma D_84770 : decode_any W_84770 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84774 : bv 32 := 0x00603833.
Lemma F_84774 : fetch_word Ubsan.M.loaded_segments (0x84774 : word) = Some W_84774.
Proof. vm_refl. Qed.
Lemma D_84774 : decode_any W_84774 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84778 : bv 32 := 0x01203e33.
Lemma F_84778 : fetch_word Ubsan.M.loaded_segments (0x84778 : word) = Some W_84778.
Proof. vm_refl. Qed.
Lemma D_84778 : decode_any W_84778 = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8477c : bv 32 := 0x01013603.
Lemma F_8477c : fetch_word Ubsan.M.loaded_segments (0x8477c : word) = Some W_8477c.
Proof. vm_refl. Qed.
Lemma D_8477c : decode_any W_8477c = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84780 : bv 32 := 0x010674b3.
Lemma F_84780 : fetch_word Ubsan.M.loaded_segments (0x84780 : word) = Some W_84780.
Proof. vm_refl. Qed.
Lemma D_84780 : decode_any W_84780 = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84784 : bv 32 := 0x02013603.
Lemma F_84784 : fetch_word Ubsan.M.loaded_segments (0x84784 : word) = Some W_84784.
Proof. vm_refl. Qed.
Lemma D_84784 : decode_any W_84784 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84788 : bv 32 := 0x01c67ab3.
Lemma F_84788 : fetch_word Ubsan.M.loaded_segments (0x84788 : word) = Some W_84788.
Proof. vm_refl. Qed.
Lemma D_84788 : decode_any W_84788 = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8478c : bv 32 := 0x01bb0633.
Lemma F_8478c : fetch_word Ubsan.M.loaded_segments (0x8478c : word) = Some W_8478c.
Proof. vm_refl. Qed.
Lemma D_8478c : decode_any W_8478c = Some (Op ALU_ADD 12 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_84790 : bv 32 := 0x00667463.
Lemma F_84790 : fetch_word Ubsan.M.loaded_segments (0x84790 : word) = Some W_84790.
Proof. vm_refl. Qed.
Lemma D_84790 : decode_any W_84790 = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84794 : bv 32 := 0xd61fd06f.
Lemma F_84794 : fetch_word Ubsan.M.loaded_segments (0x84794 : word) = Some W_84794.
Proof. vm_refl. Qed.
Lemma D_84794 : decode_any W_84794 = Some (Jal 0 2088288, 4%Z).
Proof. vm_refl. Qed.

Definition W_84798 : bv 32 := 0x00163613.
Lemma F_84798 : fetch_word Ubsan.M.loaded_segments (0x84798 : word) = Some W_84798.
Proof. vm_refl. Qed.
Lemma D_84798 : decode_any W_84798 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8479c : bv 32 := 0x00c84633.
Lemma F_8479c : fetch_word Ubsan.M.loaded_segments (0x8479c : word) = Some W_8479c.
Proof. vm_refl. Qed.
Lemma D_8479c : decode_any W_8479c = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_847a0 : bv 32 := 0x00061463.
Lemma F_847a0 : fetch_word Ubsan.M.loaded_segments (0x847a0 : word) = Some W_847a0.
Proof. vm_refl. Qed.
Lemma D_847a0 : decode_any W_847a0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847a4 : bv 32 := 0xd51fd06f.
Lemma F_847a4 : fetch_word Ubsan.M.loaded_segments (0x847a4 : word) = Some W_847a4.
Proof. vm_refl. Qed.
Lemma D_847a4 : decode_any W_847a4 = Some (Jal 0 2088272, 4%Z).
Proof. vm_refl. Qed.

Definition W_847a8 : bv 32 := 0x00049463.
Lemma F_847a8 : fetch_word Ubsan.M.loaded_segments (0x847a8 : word) = Some W_847a8.
Proof. vm_refl. Qed.
Lemma D_847a8 : decode_any W_847a8 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847ac : bv 32 := 0xd49fd06f.
Lemma F_847ac : fetch_word Ubsan.M.loaded_segments (0x847ac : word) = Some W_847ac.
Proof. vm_refl. Qed.
Lemma D_847ac : decode_any W_847ac = Some (Jal 0 2088264, 4%Z).
Proof. vm_refl. Qed.

Definition W_847b0 : bv 32 := 0x019f1463.
Lemma F_847b0 : fetch_word Ubsan.M.loaded_segments (0x847b0 : word) = Some W_847b0.
Proof. vm_refl. Qed.
Lemma D_847b0 : decode_any W_847b0 = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847b4 : bv 32 := 0xd41fd06f.
Lemma F_847b4 : fetch_word Ubsan.M.loaded_segments (0x847b4 : word) = Some W_847b4.
Proof. vm_refl. Qed.
Lemma D_847b4 : decode_any W_847b4 = Some (Jal 0 2088256, 4%Z).
Proof. vm_refl. Qed.

Definition W_847b8 : bv 32 := 0x01b30633.
Lemma F_847b8 : fetch_word Ubsan.M.loaded_segments (0x847b8 : word) = Some W_847b8.
Proof. vm_refl. Qed.
Lemma D_847b8 : decode_any W_847b8 = Some (Op ALU_ADD 12 6 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_847bc : bv 32 := 0x00cd7463.
Lemma F_847bc : fetch_word Ubsan.M.loaded_segments (0x847bc : word) = Some W_847bc.
Proof. vm_refl. Qed.
Lemma D_847bc : decode_any W_847bc = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847c0 : bv 32 := 0xd35fd06f.
Lemma F_847c0 : fetch_word Ubsan.M.loaded_segments (0x847c0 : word) = Some W_847c0.
Proof. vm_refl. Qed.
Lemma D_847c0 : decode_any W_847c0 = Some (Jal 0 2088244, 4%Z).
Proof. vm_refl. Qed.

Definition W_847c4 : bv 32 := 0x0089f463.
Lemma F_847c4 : fetch_word Ubsan.M.loaded_segments (0x847c4 : word) = Some W_847c4.
Proof. vm_refl. Qed.
Lemma D_847c4 : decode_any W_847c4 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847c8 : bv 32 := 0xd2dfd06f.
Lemma F_847c8 : fetch_word Ubsan.M.loaded_segments (0x847c8 : word) = Some W_847c8.
Proof. vm_refl. Qed.
Lemma D_847c8 : decode_any W_847c8 = Some (Jal 0 2088236, 4%Z).
Proof. vm_refl. Qed.

Definition W_847cc : bv 32 := 0x01bc07b3.
Lemma F_847cc : fetch_word Ubsan.M.loaded_segments (0x847cc : word) = Some W_847cc.
Proof. vm_refl. Qed.
Lemma D_847cc : decode_any W_847cc = Some (Op ALU_ADD 15 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_847d0 : bv 32 := 0x0127f463.
Lemma F_847d0 : fetch_word Ubsan.M.loaded_segments (0x847d0 : word) = Some W_847d0.
Proof. vm_refl. Qed.
Lemma D_847d0 : decode_any W_847d0 = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847d4 : bv 32 := 0xd21fd06f.
Lemma F_847d4 : fetch_word Ubsan.M.loaded_segments (0x847d4 : word) = Some W_847d4.
Proof. vm_refl. Qed.
Lemma D_847d4 : decode_any W_847d4 = Some (Jal 0 2088224, 4%Z).
Proof. vm_refl. Qed.

Definition W_847d8 : bv 32 := 0x0017b793.
Lemma F_847d8 : fetch_word Ubsan.M.loaded_segments (0x847d8 : word) = Some W_847d8.
Proof. vm_refl. Qed.
Lemma D_847d8 : decode_any W_847d8 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_847dc : bv 32 := 0x00fe47b3.
Lemma F_847dc : fetch_word Ubsan.M.loaded_segments (0x847dc : word) = Some W_847dc.
Proof. vm_refl. Qed.
Lemma D_847dc : decode_any W_847dc = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_847e0 : bv 32 := 0x00079463.
Lemma F_847e0 : fetch_word Ubsan.M.loaded_segments (0x847e0 : word) = Some W_847e0.
Proof. vm_refl. Qed.
Lemma D_847e0 : decode_any W_847e0 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847e4 : bv 32 := 0xd11fd06f.
Lemma F_847e4 : fetch_word Ubsan.M.loaded_segments (0x847e4 : word) = Some W_847e4.
Proof. vm_refl. Qed.
Lemma D_847e4 : decode_any W_847e4 = Some (Jal 0 2088208, 4%Z).
Proof. vm_refl. Qed.

Definition W_847e8 : bv 32 := 0x000a9463.
Lemma F_847e8 : fetch_word Ubsan.M.loaded_segments (0x847e8 : word) = Some W_847e8.
Proof. vm_refl. Qed.
Lemma D_847e8 : decode_any W_847e8 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_847ec : bv 32 := 0xd09fd06f.
Lemma F_847ec : fetch_word Ubsan.M.loaded_segments (0x847ec : word) = Some W_847ec.
Proof. vm_refl. Qed.
Lemma D_847ec : decode_any W_847ec = Some (Jal 0 2088200, 4%Z).
Proof. vm_refl. Qed.

Definition W_847f0 : bv 32 := 0x00062783.
Lemma F_847f0 : fetch_word Ubsan.M.loaded_segments (0x847f0 : word) = Some W_847f0.
Proof. vm_refl. Qed.
Lemma D_847f0 : decode_any W_847f0 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_847f4 : bv 32 := 0x00462603.
Lemma F_847f4 : fetch_word Ubsan.M.loaded_segments (0x847f4 : word) = Some W_847f4.
Proof. vm_refl. Qed.
Lemma D_847f4 : decode_any W_847f4 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_847f8 : bv 32 := 0x01b908b3.
Lemma F_847f8 : fetch_word Ubsan.M.loaded_segments (0x847f8 : word) = Some W_847f8.
Proof. vm_refl. Qed.
Lemma D_847f8 : decode_any W_847f8 = Some (Op ALU_ADD 17 18 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_847fc : bv 32 := 0x0008a083.
Lemma F_847fc : fetch_word Ubsan.M.loaded_segments (0x847fc : word) = Some W_847fc.
Proof. vm_refl. Qed.
Lemma D_847fc : decode_any W_847fc = Some (Load SZ4 true 1 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84800 : bv 32 := 0x01d797bb.
Lemma F_84800 : fetch_word Ubsan.M.loaded_segments (0x84800 : word) = Some W_84800.
Proof. vm_refl. Qed.
Lemma D_84800 : decode_any W_84800 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84804 : bv 32 := 0x0086563b.
Lemma F_84804 : fetch_word Ubsan.M.loaded_segments (0x84804 : word) = Some W_84804.
Proof. vm_refl. Qed.
Lemma D_84804 : decode_any W_84804 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84808 : bv 32 := 0x00d7f7b3.
Lemma F_84808 : fetch_word Ubsan.M.loaded_segments (0x84808 : word) = Some W_84808.
Proof. vm_refl. Qed.
Lemma D_84808 : decode_any W_84808 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8480c : bv 32 := 0x01f67633.
Lemma F_8480c : fetch_word Ubsan.M.loaded_segments (0x8480c : word) = Some W_8480c.
Proof. vm_refl. Qed.
Lemma D_8480c : decode_any W_8480c = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84810 : bv 32 := 0x00f66633.
Lemma F_84810 : fetch_word Ubsan.M.loaded_segments (0x84810 : word) = Some W_84810.
Proof. vm_refl. Qed.
Lemma D_84810 : decode_any W_84810 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84814 : bv 32 := 0xfff0c793.
Lemma F_84814 : fetch_word Ubsan.M.loaded_segments (0x84814 : word) = Some W_84814.
Proof. vm_refl. Qed.
Lemma D_84814 : decode_any W_84814 = Some (OpImm ALU_XOR 15 1 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84818 : bv 32 := 0x00f66633.
Lemma F_84818 : fetch_word Ubsan.M.loaded_segments (0x84818 : word) = Some W_84818.
Proof. vm_refl. Qed.
Lemma D_84818 : decode_any W_84818 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8481c : bv 32 := 0x004d8d93.
Lemma F_8481c : fetch_word Ubsan.M.loaded_segments (0x8481c : word) = Some W_8481c.
Proof. vm_refl. Qed.
Lemma D_8481c : decode_any W_8481c = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84820 : bv 32 := 0x00c8a023.
Lemma F_84820 : fetch_word Ubsan.M.loaded_segments (0x84820 : word) = Some W_84820.
Proof. vm_refl. Qed.
Lemma D_84820 : decode_any W_84820 = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84824 : bv 32 := 0xf7ba14e3.
Lemma F_84824 : fetch_word Ubsan.M.loaded_segments (0x84824 : word) = Some W_84824.
Proof. vm_refl. Qed.
Lemma D_84824 : decode_any W_84824 = Some (Branch BC_NE 20 27 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_84828 : bv 32 := 0x00590633.
Lemma F_84828 : fetch_word Ubsan.M.loaded_segments (0x84828 : word) = Some W_84828.
Proof. vm_refl. Qed.
Lemma D_84828 : decode_any W_84828 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8482c : bv 32 := 0x012037b3.
Lemma F_8482c : fetch_word Ubsan.M.loaded_segments (0x8482c : word) = Some W_8482c.
Proof. vm_refl. Qed.
Lemma D_8482c : decode_any W_8482c = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84830 : bv 32 := 0x00163813.
Lemma F_84830 : fetch_word Ubsan.M.loaded_segments (0x84830 : word) = Some W_84830.
Proof. vm_refl. Qed.
Lemma D_84830 : decode_any W_84830 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84834 : bv 32 := 0x01079463.
Lemma F_84834 : fetch_word Ubsan.M.loaded_segments (0x84834 : word) = Some W_84834.
Proof. vm_refl. Qed.
Lemma D_84834 : decode_any W_84834 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84838 : bv 32 := 0xcbdfd06f.
Lemma F_84838 : fetch_word Ubsan.M.loaded_segments (0x84838 : word) = Some W_84838.
Proof. vm_refl. Qed.
Lemma D_84838 : decode_any W_84838 = Some (Jal 0 2088124, 4%Z).
Proof. vm_refl. Qed.

Definition W_8483c : bv 32 := 0x01263633.
Lemma F_8483c : fetch_word Ubsan.M.loaded_segments (0x8483c : word) = Some W_8483c.
Proof. vm_refl. Qed.
Lemma D_8483c : decode_any W_8483c = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84840 : bv 32 := 0x01764633.
Lemma F_84840 : fetch_word Ubsan.M.loaded_segments (0x84840 : word) = Some W_84840.
Proof. vm_refl. Qed.
Lemma D_84840 : decode_any W_84840 = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_84844 : bv 32 := 0x00164613.
Lemma F_84844 : fetch_word Ubsan.M.loaded_segments (0x84844 : word) = Some W_84844.
Proof. vm_refl. Qed.
Lemma D_84844 : decode_any W_84844 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84848 : bv 32 := 0x00061463.
Lemma F_84848 : fetch_word Ubsan.M.loaded_segments (0x84848 : word) = Some W_84848.
Proof. vm_refl. Qed.
Lemma D_84848 : decode_any W_84848 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8484c : bv 32 := 0xca9fd06f.
Lemma F_8484c : fetch_word Ubsan.M.loaded_segments (0x8484c : word) = Some W_8484c.
Proof. vm_refl. Qed.
Lemma D_8484c : decode_any W_8484c = Some (Jal 0 2088104, 4%Z).
Proof. vm_refl. Qed.

Definition W_84850 : bv 32 := 0x00638633.
Lemma F_84850 : fetch_word Ubsan.M.loaded_segments (0x84850 : word) = Some W_84850.
Proof. vm_refl. Qed.
Lemma D_84850 : decode_any W_84850 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84854 : bv 32 := 0x006037b3.
Lemma F_84854 : fetch_word Ubsan.M.loaded_segments (0x84854 : word) = Some W_84854.
Proof. vm_refl. Qed.
Lemma D_84854 : decode_any W_84854 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84858 : bv 32 := 0x00163813.
Lemma F_84858 : fetch_word Ubsan.M.loaded_segments (0x84858 : word) = Some W_84858.
Proof. vm_refl. Qed.
Lemma D_84858 : decode_any W_84858 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8485c : bv 32 := 0x01079463.
Lemma F_8485c : fetch_word Ubsan.M.loaded_segments (0x8485c : word) = Some W_8485c.
Proof. vm_refl. Qed.
Lemma D_8485c : decode_any W_8485c = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84860 : bv 32 := 0xc95fd06f.
Lemma F_84860 : fetch_word Ubsan.M.loaded_segments (0x84860 : word) = Some W_84860.
Proof. vm_refl. Qed.
Lemma D_84860 : decode_any W_84860 = Some (Jal 0 2088084, 4%Z).
Proof. vm_refl. Qed.

Definition W_84864 : bv 32 := 0x006637b3.
Lemma F_84864 : fetch_word Ubsan.M.loaded_segments (0x84864 : word) = Some W_84864.
Proof. vm_refl. Qed.
Lemma D_84864 : decode_any W_84864 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84868 : bv 32 := 0x07813803.
Lemma F_84868 : fetch_word Ubsan.M.loaded_segments (0x84868 : word) = Some W_84868.
Proof. vm_refl. Qed.
Lemma D_84868 : decode_any W_84868 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8486c : bv 32 := 0x0107c7b3.
Lemma F_8486c : fetch_word Ubsan.M.loaded_segments (0x8486c : word) = Some W_8486c.
Proof. vm_refl. Qed.
Lemma D_8486c : decode_any W_8486c = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84870 : bv 32 := 0x0017c793.
Lemma F_84870 : fetch_word Ubsan.M.loaded_segments (0x84870 : word) = Some W_84870.
Proof. vm_refl. Qed.
Lemma D_84870 : decode_any W_84870 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84874 : bv 32 := 0x00079463.
Lemma F_84874 : fetch_word Ubsan.M.loaded_segments (0x84874 : word) = Some W_84874.
Proof. vm_refl. Qed.
Lemma D_84874 : decode_any W_84874 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84878 : bv 32 := 0xc7dfd06f.
Lemma F_84878 : fetch_word Ubsan.M.loaded_segments (0x84878 : word) = Some W_84878.
Proof. vm_refl. Qed.
Lemma D_84878 : decode_any W_84878 = Some (Jal 0 2088060, 4%Z).
Proof. vm_refl. Qed.

Definition W_8487c : bv 32 := 0x00590933.
Lemma F_8487c : fetch_word Ubsan.M.loaded_segments (0x8487c : word) = Some W_8487c.
Proof. vm_refl. Qed.
Lemma D_8487c : decode_any W_8487c = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84880 : bv 32 := 0x0015859b.
Lemma F_84880 : fetch_word Ubsan.M.loaded_segments (0x84880 : word) = Some W_84880.
Proof. vm_refl. Qed.
Lemma D_84880 : decode_any W_84880 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84884 : bv 32 := 0x005c0c33.
Lemma F_84884 : fetch_word Ubsan.M.loaded_segments (0x84884 : word) = Some W_84884.
Proof. vm_refl. Qed.
Lemma D_84884 : decode_any W_84884 = Some (Op ALU_ADD 24 24 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84888 : bv 32 := 0x007b0b33.
Lemma F_84888 : fetch_word Ubsan.M.loaded_segments (0x84888 : word) = Some W_84888.
Proof. vm_refl. Qed.
Lemma D_84888 : decode_any W_84888 = Some (Op ALU_ADD 22 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8488c : bv 32 := 0x00060313.
Lemma F_8488c : fetch_word Ubsan.M.loaded_segments (0x8488c : word) = Some W_8488c.
Proof. vm_refl. Qed.
Lemma D_8488c : decode_any W_8488c = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84890 : bv 32 := 0x08013603.
Lemma F_84890 : fetch_word Ubsan.M.loaded_segments (0x84890 : word) = Some W_84890.
Proof. vm_refl. Qed.
Lemma D_84890 : decode_any W_84890 = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_84894 : bv 32 := 0xecc59ae3.
Lemma F_84894 : fetch_word Ubsan.M.loaded_segments (0x84894 : word) = Some W_84894.
Proof. vm_refl. Qed.
Lemma D_84894 : decode_any W_84894 = Some (Branch BC_NE 11 12 7892, 4%Z).
Proof. vm_refl. Qed.

Definition W_84898 : bv 32 := 0x01813583.
Lemma F_84898 : fetch_word Ubsan.M.loaded_segments (0x84898 : word) = Some W_84898.
Proof. vm_refl. Qed.
Lemma D_84898 : decode_any W_84898 = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8489c : bv 32 := 0x00058463.
Lemma F_8489c : fetch_word Ubsan.M.loaded_segments (0x8489c : word) = Some W_8489c.
Proof. vm_refl. Qed.
Lemma D_8489c : decode_any W_8489c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_848a0 : bv 32 := 0x5190206f.
Lemma F_848a0 : fetch_word Ubsan.M.loaded_segments (0x848a0 : word) = Some W_848a0.
Proof. vm_refl. Qed.
Lemma D_848a0 : decode_any W_848a0 = Some (Jal 0 11544, 4%Z).
Proof. vm_refl. Qed.

Definition W_848a4 : bv 32 := 0x06813583.
Lemma F_848a4 : fetch_word Ubsan.M.loaded_segments (0x848a4 : word) = Some W_848a4.
Proof. vm_refl. Qed.
Lemma D_848a4 : decode_any W_848a4 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_848a8 : bv 32 := 0x0035f593.
Lemma F_848a8 : fetch_word Ubsan.M.loaded_segments (0x848a8 : word) = Some W_848a8.
Proof. vm_refl. Qed.
Lemma D_848a8 : decode_any W_848a8 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_848ac : bv 32 := 0x00058463.
Lemma F_848ac : fetch_word Ubsan.M.loaded_segments (0x848ac : word) = Some W_848ac.
Proof. vm_refl. Qed.
Lemma D_848ac : decode_any W_848ac = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_848b0 : bv 32 := 0xc45fd06f.
Lemma F_848b0 : fetch_word Ubsan.M.loaded_segments (0x848b0 : word) = Some W_848b0.
Proof. vm_refl. Qed.
Lemma D_848b0 : decode_any W_848b0 = Some (Jal 0 2088004, 4%Z).
Proof. vm_refl. Qed.

Definition W_848b4 : bv 32 := 0xffffc613.
Lemma F_848b4 : fetch_word Ubsan.M.loaded_segments (0x848b4 : word) = Some W_848b4.
Proof. vm_refl. Qed.
Lemma D_848b4 : decode_any W_848b4 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_848b8 : bv 32 := 0x06013683.
Lemma F_848b8 : fetch_word Ubsan.M.loaded_segments (0x848b8 : word) = Some W_848b8.
Proof. vm_refl. Qed.
Lemma D_848b8 : decode_any W_848b8 = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_848bc : bv 32 := 0xfff6c693.
Lemma F_848bc : fetch_word Ubsan.M.loaded_segments (0x848bc : word) = Some W_848bc.
Proof. vm_refl. Qed.
Lemma D_848bc : decode_any W_848bc = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_848c0 : bv 32 := 0x00271793.
Lemma F_848c0 : fetch_word Ubsan.M.loaded_segments (0x848c0 : word) = Some W_848c0.
Proof. vm_refl. Qed.
Lemma D_848c0 : decode_any W_848c0 = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_848c4 : bv 32 := 0x05813303.
Lemma F_848c4 : fetch_word Ubsan.M.loaded_segments (0x848c4 : word) = Some W_848c4.
Proof. vm_refl. Qed.
Lemma D_848c4 : decode_any W_848c4 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_848c8 : bv 32 := 0x00231313.
Lemma F_848c8 : fetch_word Ubsan.M.loaded_segments (0x848c8 : word) = Some W_848c8.
Proof. vm_refl. Qed.
Lemma D_848c8 : decode_any W_848c8 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_848cc : bv 32 := 0x00357893.
Lemma F_848cc : fetch_word Ubsan.M.loaded_segments (0x848cc : word) = Some W_848cc.
Proof. vm_refl. Qed.
Lemma D_848cc : decode_any W_848cc = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_848d0 : bv 32 := 0x05013903.
Lemma F_848d0 : fetch_word Ubsan.M.loaded_segments (0x848d0 : word) = Some W_848d0.
Proof. vm_refl. Qed.
Lemma D_848d0 : decode_any W_848d0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_848d4 : bv 32 := 0x02813803.
Lemma F_848d4 : fetch_word Ubsan.M.loaded_segments (0x848d4 : word) = Some W_848d4.
Proof. vm_refl. Qed.
Lemma D_848d4 : decode_any W_848d4 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_848d8 : bv 32 := 0x412804bb.
Lemma F_848d8 : fetch_word Ubsan.M.loaded_segments (0x848d8 : word) = Some W_848d8.
Proof. vm_refl. Qed.
Lemma D_848d8 : decode_any W_848d8 = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_848dc : bv 32 := 0x03813383.
Lemma F_848dc : fetch_word Ubsan.M.loaded_segments (0x848dc : word) = Some W_848dc.
Proof. vm_refl. Qed.
Lemma D_848dc : decode_any W_848dc = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_848e0 : bv 32 := 0x03013803.
Lemma F_848e0 : fetch_word Ubsan.M.loaded_segments (0x848e0 : word) = Some W_848e0.
Proof. vm_refl. Qed.
Lemma D_848e0 : decode_any W_848e0 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_848e4 : bv 32 := 0x007803b3.
Lemma F_848e4 : fetch_word Ubsan.M.loaded_segments (0x848e4 : word) = Some W_848e4.
Proof. vm_refl. Qed.
Lemma D_848e4 : decode_any W_848e4 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_848e8 : bv 32 := 0x04813283.
Lemma F_848e8 : fetch_word Ubsan.M.loaded_segments (0x848e8 : word) = Some W_848e8.
Proof. vm_refl. Qed.
Lemma D_848e8 : decode_any W_848e8 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_848ec : bv 32 := 0x43f2d813.
Lemma F_848ec : fetch_word Ubsan.M.loaded_segments (0x848ec : word) = Some W_848ec.
Proof. vm_refl. Qed.
Lemma D_848ec : decode_any W_848ec = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_848f0 : bv 32 := 0x00587e33.
Lemma F_848f0 : fetch_word Ubsan.M.loaded_segments (0x848f0 : word) = Some W_848f0.
Proof. vm_refl. Qed.
Lemma D_848f0 : decode_any W_848f0 = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_848f4 : bv 32 := 0x02000813.
Lemma F_848f4 : fetch_word Ubsan.M.loaded_segments (0x848f4 : word) = Some W_848f4.
Proof. vm_refl. Qed.
Lemma D_848f4 : decode_any W_848f4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_848f8 : bv 32 := 0x00813283.
Lemma F_848f8 : fetch_word Ubsan.M.loaded_segments (0x848f8 : word) = Some W_848f8.
Proof. vm_refl. Qed.
Lemma D_848f8 : decode_any W_848f8 = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_848fc : bv 32 := 0x0012f293.
Lemma F_848fc : fetch_word Ubsan.M.loaded_segments (0x848fc : word) = Some W_848fc.
Proof. vm_refl. Qed.
Lemma D_848fc : decode_any W_848fc = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84900 : bv 32 := 0x00072713.
Lemma F_84900 : fetch_word Ubsan.M.loaded_segments (0x84900 : word) = Some W_84900.
Proof. vm_refl. Qed.
Lemma D_84900 : decode_any W_84900 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84904 : bv 32 := 0x01c38e33.
Lemma F_84904 : fetch_word Ubsan.M.loaded_segments (0x84904 : word) = Some W_84904.
Proof. vm_refl. Qed.
Lemma D_84904 : decode_any W_84904 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84908 : bv 32 := 0xffb00393.
Lemma F_84908 : fetch_word Ubsan.M.loaded_segments (0x84908 : word) = Some W_84908.
Proof. vm_refl. Qed.
Lemma D_84908 : decode_any W_84908 = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_8490c : bv 32 := 0x412e093b.
Lemma F_8490c : fetch_word Ubsan.M.loaded_segments (0x8490c : word) = Some W_8490c.
Proof. vm_refl. Qed.
Lemma D_8490c : decode_any W_8490c = Some (Op32 ALU_SUB 18 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84910 : bv 32 := 0x06813e03.
Lemma F_84910 : fetch_word Ubsan.M.loaded_segments (0x84910 : word) = Some W_84910.
Proof. vm_refl. Qed.
Lemma D_84910 : decode_any W_84910 = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_84914 : bv 32 := 0x006e0e33.
Lemma F_84914 : fetch_word Ubsan.M.loaded_segments (0x84914 : word) = Some W_84914.
Proof. vm_refl. Qed.
Lemma D_84914 : decode_any W_84914 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84918 : bv 32 := 0x04013983.
Lemma F_84918 : fetch_word Ubsan.M.loaded_segments (0x84918 : word) = Some W_84918.
Proof. vm_refl. Qed.
Lemma D_84918 : decode_any W_84918 = Some (Load SZ8 true 19 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8491c : bv 32 := 0x4139093b.
Lemma F_8491c : fetch_word Ubsan.M.loaded_segments (0x8491c : word) = Some W_8491c.
Proof. vm_refl. Qed.
Lemma D_8491c : decode_any W_8491c = Some (Op32 ALU_SUB 18 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_84920 : bv 32 := 0x43f95993.
Lemma F_84920 : fetch_word Ubsan.M.loaded_segments (0x84920 : word) = Some W_84920.
Proof. vm_refl. Qed.
Lemma D_84920 : decode_any W_84920 = Some (ShiftImm ALU_SRA 19 18 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84924 : bv 32 := 0x0129f933.
Lemma F_84924 : fetch_word Ubsan.M.loaded_segments (0x84924 : word) = Some W_84924.
Proof. vm_refl. Qed.
Lemma D_84924 : decode_any W_84924 = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84928 : bv 32 := 0x412484bb.
Lemma F_84928 : fetch_word Ubsan.M.loaded_segments (0x84928 : word) = Some W_84928.
Proof. vm_refl. Qed.
Lemma D_84928 : decode_any W_84928 = Some (Op32 ALU_SUB 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8492c : bv 32 := 0x01f00993.
Lemma F_8492c : fetch_word Ubsan.M.loaded_segments (0x8492c : word) = Some W_8492c.
Proof. vm_refl. Qed.
Lemma D_8492c : decode_any W_8492c = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84930 : bv 32 := 0x00050a13.
Lemma F_84930 : fetch_word Ubsan.M.loaded_segments (0x84930 : word) = Some W_84930.
Proof. vm_refl. Qed.
Lemma D_84930 : decode_any W_84930 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84934 : bv 32 := 0x06813a83.
Lemma F_84934 : fetch_word Ubsan.M.loaded_segments (0x84934 : word) = Some W_84934.
Proof. vm_refl. Qed.
Lemma D_84934 : decode_any W_84934 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_84938 : bv 32 := 0x00ba8ab3.
Lemma F_84938 : fetch_word Ubsan.M.loaded_segments (0x84938 : word) = Some W_84938.
Proof. vm_refl. Qed.
Lemma D_84938 : decode_any W_84938 = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8493c : bv 32 := 0x000a9463.
Lemma F_8493c : fetch_word Ubsan.M.loaded_segments (0x8493c : word) = Some W_8493c.
Proof. vm_refl. Qed.
Lemma D_8493c : decode_any W_8493c = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84940 : bv 32 := 0xbb5fd06f.
Lemma F_84940 : fetch_word Ubsan.M.loaded_segments (0x84940 : word) = Some W_84940.
Proof. vm_refl. Qed.
Lemma D_84940 : decode_any W_84940 = Some (Jal 0 2087860, 4%Z).
Proof. vm_refl. Qed.

Definition W_84944 : bv 32 := 0x010f1463.
Lemma F_84944 : fetch_word Ubsan.M.loaded_segments (0x84944 : word) = Some W_84944.
Proof. vm_refl. Qed.
Lemma D_84944 : decode_any W_84944 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84948 : bv 32 := 0xbadfd06f.
Lemma F_84948 : fetch_word Ubsan.M.loaded_segments (0x84948 : word) = Some W_84948.
Proof. vm_refl. Qed.
Lemma D_84948 : decode_any W_84948 = Some (Jal 0 2087852, 4%Z).
Proof. vm_refl. Qed.

Definition W_8494c : bv 32 := 0x000aa903.
Lemma F_8494c : fetch_word Ubsan.M.loaded_segments (0x8494c : word) = Some W_8494c.
Proof. vm_refl. Qed.
Lemma D_8494c : decode_any W_8494c = Some (Load SZ4 true 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84950 : bv 32 := 0x01d91b3b.
Lemma F_84950 : fetch_word Ubsan.M.loaded_segments (0x84950 : word) = Some W_84950.
Proof. vm_refl. Qed.
Lemma D_84950 : decode_any W_84950 = Some (Op32 ALU_SLL 22 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84954 : bv 32 := 0x02029463.
Lemma F_84954 : fetch_word Ubsan.M.loaded_segments (0x84954 : word) = Some W_84954.
Proof. vm_refl. Qed.
Lemma D_84954 : decode_any W_84954 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84958 : bv 32 := 0x0153f463.
Lemma F_84958 : fetch_word Ubsan.M.loaded_segments (0x84958 : word) = Some W_84958.
Proof. vm_refl. Qed.
Lemma D_84958 : decode_any W_84958 = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8495c : bv 32 := 0xb99fd06f.
Lemma F_8495c : fetch_word Ubsan.M.loaded_segments (0x8495c : word) = Some W_8495c.
Proof. vm_refl. Qed.
Lemma D_8495c : decode_any W_8495c = Some (Jal 0 2087832, 4%Z).
Proof. vm_refl. Qed.

Definition W_84960 : bv 32 := 0x0089f463.
Lemma F_84960 : fetch_word Ubsan.M.loaded_segments (0x84960 : word) = Some W_84960.
Proof. vm_refl. Qed.
Lemma D_84960 : decode_any W_84960 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84964 : bv 32 := 0xb91fd06f.
Lemma F_84964 : fetch_word Ubsan.M.loaded_segments (0x84964 : word) = Some W_84964.
Proof. vm_refl. Qed.
Lemma D_84964 : decode_any W_84964 = Some (Jal 0 2087824, 4%Z).
Proof. vm_refl. Qed.

Definition W_84968 : bv 32 := 0x004aa903.
Lemma F_84968 : fetch_word Ubsan.M.loaded_segments (0x84968 : word) = Some W_84968.
Proof. vm_refl. Qed.
Lemma D_84968 : decode_any W_84968 = Some (Load SZ4 true 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8496c : bv 32 := 0x00cb7b33.
Lemma F_8496c : fetch_word Ubsan.M.loaded_segments (0x8496c : word) = Some W_8496c.
Proof. vm_refl. Qed.
Lemma D_8496c : decode_any W_8496c = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84970 : bv 32 := 0x0089593b.
Lemma F_84970 : fetch_word Ubsan.M.loaded_segments (0x84970 : word) = Some W_84970.
Proof. vm_refl. Qed.
Lemma D_84970 : decode_any W_84970 = Some (Op32 ALU_SRL 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84974 : bv 32 := 0x01f97933.
Lemma F_84974 : fetch_word Ubsan.M.loaded_segments (0x84974 : word) = Some W_84974.
Proof. vm_refl. Qed.
Lemma D_84974 : decode_any W_84974 = Some (Op ALU_AND 18 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84978 : bv 32 := 0x01696b33.
Lemma F_84978 : fetch_word Ubsan.M.loaded_segments (0x84978 : word) = Some W_84978.
Proof. vm_refl. Qed.
Lemma D_84978 : decode_any W_84978 = Some (Op ALU_OR 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8497c : bv 32 := 0x00088463.
Lemma F_8497c : fetch_word Ubsan.M.loaded_segments (0x8497c : word) = Some W_8497c.
Proof. vm_refl. Qed.
Lemma D_8497c : decode_any W_8497c = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84980 : bv 32 := 0xb75fd06f.
Lemma F_84980 : fetch_word Ubsan.M.loaded_segments (0x84980 : word) = Some W_84980.
Proof. vm_refl. Qed.
Lemma D_84980 : decode_any W_84980 = Some (Jal 0 2087796, 4%Z).
Proof. vm_refl. Qed.

Definition W_84984 : bv 32 := 0x00051463.
Lemma F_84984 : fetch_word Ubsan.M.loaded_segments (0x84984 : word) = Some W_84984.
Proof. vm_refl. Qed.
Lemma D_84984 : decode_any W_84984 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84988 : bv 32 := 0xb6dfd06f.
Lemma F_84988 : fetch_word Ubsan.M.loaded_segments (0x84988 : word) = Some W_84988.
Proof. vm_refl. Qed.
Lemma D_84988 : decode_any W_84988 = Some (Jal 0 2087788, 4%Z).
Proof. vm_refl. Qed.

Definition W_8498c : bv 32 := 0x00052903.
Lemma F_8498c : fetch_word Ubsan.M.loaded_segments (0x8498c : word) = Some W_8498c.
Proof. vm_refl. Qed.
Lemma D_8498c : decode_any W_8498c = Some (Load SZ4 true 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84990 : bv 32 := 0x00d97bb3.
Lemma F_84990 : fetch_word Ubsan.M.loaded_segments (0x84990 : word) = Some W_84990.
Proof. vm_refl. Qed.
Lemma D_84990 : decode_any W_84990 = Some (Op ALU_AND 23 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84994 : bv 32 := 0xfff94913.
Lemma F_84994 : fetch_word Ubsan.M.loaded_segments (0x84994 : word) = Some W_84994.
Proof. vm_refl. Qed.
Lemma D_84994 : decode_any W_84994 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84998 : bv 32 := 0x012b6933.
Lemma F_84998 : fetch_word Ubsan.M.loaded_segments (0x84998 : word) = Some W_84998.
Proof. vm_refl. Qed.
Lemma D_84998 : decode_any W_84998 = Some (Op ALU_OR 18 22 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8499c : bv 32 := 0x06013b03.
Lemma F_8499c : fetch_word Ubsan.M.loaded_segments (0x8499c : word) = Some W_8499c.
Proof. vm_refl. Qed.
Lemma D_8499c : decode_any W_8499c = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_849a0 : bv 32 := 0x01697933.
Lemma F_849a0 : fetch_word Ubsan.M.loaded_segments (0x849a0 : word) = Some W_849a0.
Proof. vm_refl. Qed.
Lemma D_849a0 : decode_any W_849a0 = Some (Op ALU_AND 18 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_849a4 : bv 32 := 0x01796933.
Lemma F_849a4 : fetch_word Ubsan.M.loaded_segments (0x849a4 : word) = Some W_849a4.
Proof. vm_refl. Qed.
Lemma D_849a4 : decode_any W_849a4 = Some (Op ALU_OR 18 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_849a8 : bv 32 := 0x01478b33.
Lemma F_849a8 : fetch_word Ubsan.M.loaded_segments (0x849a8 : word) = Some W_849a8.
Proof. vm_refl. Qed.
Lemma D_849a8 : decode_any W_849a8 = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_849ac : bv 32 := 0x01252023.
Lemma F_849ac : fetch_word Ubsan.M.loaded_segments (0x849ac : word) = Some W_849ac.
Proof. vm_refl. Qed.
Lemma D_849ac : decode_any W_849ac = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_849b0 : bv 32 := 0x000b1463.
Lemma F_849b0 : fetch_word Ubsan.M.loaded_segments (0x849b0 : word) = Some W_849b0.
Proof. vm_refl. Qed.
Lemma D_849b0 : decode_any W_849b0 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_849b4 : bv 32 := 0xb41fd06f.
Lemma F_849b4 : fetch_word Ubsan.M.loaded_segments (0x849b4 : word) = Some W_849b4.
Proof. vm_refl. Qed.
Lemma D_849b4 : decode_any W_849b4 = Some (Jal 0 2087744, 4%Z).
Proof. vm_refl. Qed.

Definition W_849b8 : bv 32 := 0x014b3933.
Lemma F_849b8 : fetch_word Ubsan.M.loaded_segments (0x849b8 : word) = Some W_849b8.
Proof. vm_refl. Qed.
Lemma D_849b8 : decode_any W_849b8 = Some (Op ALU_SLTU 18 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_849bc : bv 32 := 0x00e94933.
Lemma F_849bc : fetch_word Ubsan.M.loaded_segments (0x849bc : word) = Some W_849bc.
Proof. vm_refl. Qed.
Lemma D_849bc : decode_any W_849bc = Some (Op ALU_XOR 18 18 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_849c0 : bv 32 := 0x00194913.
Lemma F_849c0 : fetch_word Ubsan.M.loaded_segments (0x849c0 : word) = Some W_849c0.
Proof. vm_refl. Qed.
Lemma D_849c0 : decode_any W_849c0 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_849c4 : bv 32 := 0x00091463.
Lemma F_849c4 : fetch_word Ubsan.M.loaded_segments (0x849c4 : word) = Some W_849c4.
Proof. vm_refl. Qed.
Lemma D_849c4 : decode_any W_849c4 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_849c8 : bv 32 := 0xb2dfd06f.
Lemma F_849c8 : fetch_word Ubsan.M.loaded_segments (0x849c8 : word) = Some W_849c8.
Proof. vm_refl. Qed.
Lemma D_849c8 : decode_any W_849c8 = Some (Jal 0 2087724, 4%Z).
Proof. vm_refl. Qed.

Definition W_849cc : bv 32 := 0x00be0a33.
Lemma F_849cc : fetch_word Ubsan.M.loaded_segments (0x849cc : word) = Some W_849cc.
Proof. vm_refl. Qed.
Lemma D_849cc : decode_any W_849cc = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_849d0 : bv 32 := 0x000a1463.
Lemma F_849d0 : fetch_word Ubsan.M.loaded_segments (0x849d0 : word) = Some W_849d0.
Proof. vm_refl. Qed.
Lemma D_849d0 : decode_any W_849d0 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_849d4 : bv 32 := 0xb21fd06f.
Lemma F_849d4 : fetch_word Ubsan.M.loaded_segments (0x849d4 : word) = Some W_849d4.
Proof. vm_refl. Qed.
Lemma D_849d4 : decode_any W_849d4 = Some (Jal 0 2087712, 4%Z).
Proof. vm_refl. Qed.

Definition W_849d8 : bv 32 := 0x015a3933.
Lemma F_849d8 : fetch_word Ubsan.M.loaded_segments (0x849d8 : word) = Some W_849d8.
Proof. vm_refl. Qed.
Lemma D_849d8 : decode_any W_849d8 = Some (Op ALU_SLTU 18 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_849dc : bv 32 := 0x07813a03.
Lemma F_849dc : fetch_word Ubsan.M.loaded_segments (0x849dc : word) = Some W_849dc.
Proof. vm_refl. Qed.
Lemma D_849dc : decode_any W_849dc = Some (Load SZ8 true 20 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_849e0 : bv 32 := 0x01494933.
Lemma F_849e0 : fetch_word Ubsan.M.loaded_segments (0x849e0 : word) = Some W_849e0.
Proof. vm_refl. Qed.
Lemma D_849e0 : decode_any W_849e0 = Some (Op ALU_XOR 18 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_849e4 : bv 32 := 0x00194913.
Lemma F_849e4 : fetch_word Ubsan.M.loaded_segments (0x849e4 : word) = Some W_849e4.
Proof. vm_refl. Qed.
Lemma D_849e4 : decode_any W_849e4 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_849e8 : bv 32 := 0x00091463.
Lemma F_849e8 : fetch_word Ubsan.M.loaded_segments (0x849e8 : word) = Some W_849e8.
Proof. vm_refl. Qed.
Lemma D_849e8 : decode_any W_849e8 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_849ec : bv 32 := 0xb09fd06f.
Lemma F_849ec : fetch_word Ubsan.M.loaded_segments (0x849ec : word) = Some W_849ec.
Proof. vm_refl. Qed.
Lemma D_849ec : decode_any W_849ec = Some (Jal 0 2087688, 4%Z).
Proof. vm_refl. Qed.

Definition W_849f0 : bv 32 := 0x0014849b.
Lemma F_849f0 : fetch_word Ubsan.M.loaded_segments (0x849f0 : word) = Some W_849f0.
Proof. vm_refl. Qed.
Lemma D_849f0 : decode_any W_849f0 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_849f4 : bv 32 := 0x006585b3.
Lemma F_849f4 : fetch_word Ubsan.M.loaded_segments (0x849f4 : word) = Some W_849f4.
Proof. vm_refl. Qed.
Lemma D_849f4 : decode_any W_849f4 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_849f8 : bv 32 := 0x00f50533.
Lemma F_849f8 : fetch_word Ubsan.M.loaded_segments (0x849f8 : word) = Some W_849f8.
Proof. vm_refl. Qed.
Lemma D_849f8 : decode_any W_849f8 = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_849fc : bv 32 := 0x000b0a13.
Lemma F_849fc : fetch_word Ubsan.M.loaded_segments (0x849fc : word) = Some W_849fc.
Proof. vm_refl. Qed.
Lemma D_849fc : decode_any W_849fc = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a00 : bv 32 := 0xf2049ae3.
Lemma F_84a00 : fetch_word Ubsan.M.loaded_segments (0x84a00 : word) = Some W_84a00.
Proof. vm_refl. Qed.
Lemma D_84a00 : decode_any W_84a00 = Some (Branch BC_NE 9 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a04 : bv 32 := 0x3b50206f.
Lemma F_84a04 : fetch_word Ubsan.M.loaded_segments (0x84a04 : word) = Some W_84a04.
Proof. vm_refl. Qed.
Lemma D_84a04 : decode_any W_84a04 = Some (Jal 0 11188, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a08 : bv 32 := 0x16008e63.
Lemma F_84a08 : fetch_word Ubsan.M.loaded_segments (0x84a08 : word) = Some W_84a08.
Proof. vm_refl. Qed.
Lemma D_84a08 : decode_any W_84a08 = Some (Branch BC_EQ 1 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a0c : bv 32 := 0x00000593.
Lemma F_84a0c : fetch_word Ubsan.M.loaded_segments (0x84a0c : word) = Some W_84a0c.
Proof. vm_refl. Qed.
Lemma D_84a0c : decode_any W_84a0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a10 : bv 32 := 0xffffca93.
Lemma F_84a10 : fetch_word Ubsan.M.loaded_segments (0x84a10 : word) = Some W_84a10.
Proof. vm_refl. Qed.
Lemma D_84a10 : decode_any W_84a10 = Some (OpImm ALU_XOR 21 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a14 : bv 32 := 0xfffdc293.
Lemma F_84a14 : fetch_word Ubsan.M.loaded_segments (0x84a14 : word) = Some W_84a14.
Proof. vm_refl. Qed.
Lemma D_84a14 : decode_any W_84a14 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a18 : bv 32 := 0x00271393.
Lemma F_84a18 : fetch_word Ubsan.M.loaded_segments (0x84a18 : word) = Some W_84a18.
Proof. vm_refl. Qed.
Lemma D_84a18 : decode_any W_84a18 = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a1c : bv 32 := 0x05813683.
Lemma F_84a1c : fetch_word Ubsan.M.loaded_segments (0x84a1c : word) = Some W_84a1c.
Proof. vm_refl. Qed.
Lemma D_84a1c : decode_any W_84a1c = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a20 : bv 32 := 0x00269693.
Lemma F_84a20 : fetch_word Ubsan.M.loaded_segments (0x84a20 : word) = Some W_84a20.
Proof. vm_refl. Qed.
Lemma D_84a20 : decode_any W_84a20 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a24 : bv 32 := 0x003cfb93.
Lemma F_84a24 : fetch_word Ubsan.M.loaded_segments (0x84a24 : word) = Some W_84a24.
Proof. vm_refl. Qed.
Lemma D_84a24 : decode_any W_84a24 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a28 : bv 32 := 0x0037f613.
Lemma F_84a28 : fetch_word Ubsan.M.loaded_segments (0x84a28 : word) = Some W_84a28.
Proof. vm_refl. Qed.
Lemma D_84a28 : decode_any W_84a28 = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a2c : bv 32 := 0x05013883.
Lemma F_84a2c : fetch_word Ubsan.M.loaded_segments (0x84a2c : word) = Some W_84a2c.
Proof. vm_refl. Qed.
Lemma D_84a2c : decode_any W_84a2c = Some (Load SZ8 true 17 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a30 : bv 32 := 0x02813803.
Lemma F_84a30 : fetch_word Ubsan.M.loaded_segments (0x84a30 : word) = Some W_84a30.
Proof. vm_refl. Qed.
Lemma D_84a30 : decode_any W_84a30 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a34 : bv 32 := 0x4118083b.
Lemma F_84a34 : fetch_word Ubsan.M.loaded_segments (0x84a34 : word) = Some W_84a34.
Proof. vm_refl. Qed.
Lemma D_84a34 : decode_any W_84a34 = Some (Op32 ALU_SUB 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a38 : bv 32 := 0x03813e03.
Lemma F_84a38 : fetch_word Ubsan.M.loaded_segments (0x84a38 : word) = Some W_84a38.
Proof. vm_refl. Qed.
Lemma D_84a38 : decode_any W_84a38 = Some (Load SZ8 true 28 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a3c : bv 32 := 0x03013483.
Lemma F_84a3c : fetch_word Ubsan.M.loaded_segments (0x84a3c : word) = Some W_84a3c.
Proof. vm_refl. Qed.
Lemma D_84a3c : decode_any W_84a3c = Some (Load SZ8 true 9 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a40 : bv 32 := 0x01c48e33.
Lemma F_84a40 : fetch_word Ubsan.M.loaded_segments (0x84a40 : word) = Some W_84a40.
Proof. vm_refl. Qed.
Lemma D_84a40 : decode_any W_84a40 = Some (Op ALU_ADD 28 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a44 : bv 32 := 0x04813a03.
Lemma F_84a44 : fetch_word Ubsan.M.loaded_segments (0x84a44 : word) = Some W_84a44.
Proof. vm_refl. Qed.
Lemma D_84a44 : decode_any W_84a44 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a48 : bv 32 := 0x43fa5493.
Lemma F_84a48 : fetch_word Ubsan.M.loaded_segments (0x84a48 : word) = Some W_84a48.
Proof. vm_refl. Qed.
Lemma D_84a48 : decode_any W_84a48 = Some (ShiftImm ALU_SRA 9 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a4c : bv 32 := 0x01013983.
Lemma F_84a4c : fetch_word Ubsan.M.loaded_segments (0x84a4c : word) = Some W_84a4c.
Proof. vm_refl. Qed.
Lemma D_84a4c : decode_any W_84a4c = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a50 : bv 32 := 0x0019f993.
Lemma F_84a50 : fetch_word Ubsan.M.loaded_segments (0x84a50 : word) = Some W_84a50.
Proof. vm_refl. Qed.
Lemma D_84a50 : decode_any W_84a50 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a54 : bv 32 := 0x001d7c13.
Lemma F_84a54 : fetch_word Ubsan.M.loaded_segments (0x84a54 : word) = Some W_84a54.
Proof. vm_refl. Qed.
Lemma D_84a54 : decode_any W_84a54 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a58 : bv 32 := 0x01f00093.
Lemma F_84a58 : fetch_word Ubsan.M.loaded_segments (0x84a58 : word) = Some W_84a58.
Proof. vm_refl. Qed.
Lemma D_84a58 : decode_any W_84a58 = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a5c : bv 32 := 0x0144f4b3.
Lemma F_84a5c : fetch_word Ubsan.M.loaded_segments (0x84a5c : word) = Some W_84a5c.
Proof. vm_refl. Qed.
Lemma D_84a5c : decode_any W_84a5c = Some (Op ALU_AND 9 9 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a60 : bv 32 := 0x411e0e3b.
Lemma F_84a60 : fetch_word Ubsan.M.loaded_segments (0x84a60 : word) = Some W_84a60.
Proof. vm_refl. Qed.
Lemma D_84a60 : decode_any W_84a60 = Some (Op32 ALU_SUB 28 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a64 : bv 32 := 0x000a8893.
Lemma F_84a64 : fetch_word Ubsan.M.loaded_segments (0x84a64 : word) = Some W_84a64.
Proof. vm_refl. Qed.
Lemma D_84a64 : decode_any W_84a64 = Some (OpImm ALU_ADD 17 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a68 : bv 32 := 0x00d78a33.
Lemma F_84a68 : fetch_word Ubsan.M.loaded_segments (0x84a68 : word) = Some W_84a68.
Proof. vm_refl. Qed.
Lemma D_84a68 : decode_any W_84a68 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a6c : bv 32 := 0x00163b13.
Lemma F_84a6c : fetch_word Ubsan.M.loaded_segments (0x84a6c : word) = Some W_84a6c.
Proof. vm_refl. Qed.
Lemma D_84a6c : decode_any W_84a6c = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a70 : bv 32 := 0x04013603.
Lemma F_84a70 : fetch_word Ubsan.M.loaded_segments (0x84a70 : word) = Some W_84a70.
Proof. vm_refl. Qed.
Lemma D_84a70 : decode_any W_84a70 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a74 : bv 32 := 0x40ce063b.
Lemma F_84a74 : fetch_word Ubsan.M.loaded_segments (0x84a74 : word) = Some W_84a74.
Proof. vm_refl. Qed.
Lemma D_84a74 : decode_any W_84a74 = Some (Op32 ALU_SUB 12 28 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a78 : bv 32 := 0x0096063b.
Lemma F_84a78 : fetch_word Ubsan.M.loaded_segments (0x84a78 : word) = Some W_84a78.
Proof. vm_refl. Qed.
Lemma D_84a78 : decode_any W_84a78 = Some (Op32 ALU_ADD 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a7c : bv 32 := 0x43f65e13.
Lemma F_84a7c : fetch_word Ubsan.M.loaded_segments (0x84a7c : word) = Some W_84a7c.
Proof. vm_refl. Qed.
Lemma D_84a7c : decode_any W_84a7c = Some (ShiftImm ALU_SRA 28 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a80 : bv 32 := 0x00ce7633.
Lemma F_84a80 : fetch_word Ubsan.M.loaded_segments (0x84a80 : word) = Some W_84a80.
Proof. vm_refl. Qed.
Lemma D_84a80 : decode_any W_84a80 = Some (Op ALU_AND 12 28 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a84 : bv 32 := 0x40c80e3b.
Lemma F_84a84 : fetch_word Ubsan.M.loaded_segments (0x84a84 : word) = Some W_84a84.
Proof. vm_refl. Qed.
Lemma D_84a84 : decode_any W_84a84 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a88 : bv 32 := 0x00072493.
Lemma F_84a88 : fetch_word Ubsan.M.loaded_segments (0x84a88 : word) = Some W_84a88.
Proof. vm_refl. Qed.
Lemma D_84a88 : decode_any W_84a88 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a8c : bv 32 := 0x000c8813.
Lemma F_84a8c : fetch_word Ubsan.M.loaded_segments (0x84a8c : word) = Some W_84a8c.
Proof. vm_refl. Qed.
Lemma D_84a8c : decode_any W_84a8c = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a90 : bv 32 := 0x00b78d33.
Lemma F_84a90 : fetch_word Ubsan.M.loaded_segments (0x84a90 : word) = Some W_84a90.
Proof. vm_refl. Qed.
Lemma D_84a90 : decode_any W_84a90 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a94 : bv 32 := 0x01a03633.
Lemma F_84a94 : fetch_word Ubsan.M.loaded_segments (0x84a94 : word) = Some W_84a94.
Proof. vm_refl. Qed.
Lemma D_84a94 : decode_any W_84a94 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a98 : bv 32 := 0x00cb7633.
Lemma F_84a98 : fetch_word Ubsan.M.loaded_segments (0x84a98 : word) = Some W_84a98.
Proof. vm_refl. Qed.
Lemma D_84a98 : decode_any W_84a98 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a9c : bv 32 := 0x04098863.
Lemma F_84a9c : fetch_word Ubsan.M.loaded_segments (0x84a9c : word) = Some W_84a9c.
Proof. vm_refl. Qed.
Lemma D_84a9c : decode_any W_84a9c = Some (Branch BC_EQ 19 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_84aa0 : bv 32 := 0x00061463.
Lemma F_84aa0 : fetch_word Ubsan.M.loaded_segments (0x84aa0 : word) = Some W_84aa0.
Proof. vm_refl. Qed.
Lemma D_84aa0 : decode_any W_84aa0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84aa4 : bv 32 := 0xa51fd06f.
Lemma F_84aa4 : fetch_word Ubsan.M.loaded_segments (0x84aa4 : word) = Some W_84aa4.
Proof. vm_refl. Qed.
Lemma D_84aa4 : decode_any W_84aa4 = Some (Jal 0 2087504, 4%Z).
Proof. vm_refl. Qed.

Definition W_84aa8 : bv 32 := 0x02000613.
Lemma F_84aa8 : fetch_word Ubsan.M.loaded_segments (0x84aa8 : word) = Some W_84aa8.
Proof. vm_refl. Qed.
Lemma D_84aa8 : decode_any W_84aa8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84aac : bv 32 := 0x00cf1463.
Lemma F_84aac : fetch_word Ubsan.M.loaded_segments (0x84aac : word) = Some W_84aac.
Proof. vm_refl. Qed.
Lemma D_84aac : decode_any W_84aac = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ab0 : bv 32 := 0xa45fd06f.
Lemma F_84ab0 : fetch_word Ubsan.M.loaded_segments (0x84ab0 : word) = Some W_84ab0.
Proof. vm_refl. Qed.
Lemma D_84ab0 : decode_any W_84ab0 = Some (Jal 0 2087492, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ab4 : bv 32 := 0x000d2603.
Lemma F_84ab4 : fetch_word Ubsan.M.loaded_segments (0x84ab4 : word) = Some W_84ab4.
Proof. vm_refl. Qed.
Lemma D_84ab4 : decode_any W_84ab4 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ab8 : bv 32 := 0x01d61abb.
Lemma F_84ab8 : fetch_word Ubsan.M.loaded_segments (0x84ab8 : word) = Some W_84ab8.
Proof. vm_refl. Qed.
Lemma D_84ab8 : decode_any W_84ab8 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84abc : bv 32 := 0x040c1463.
Lemma F_84abc : fetch_word Ubsan.M.loaded_segments (0x84abc : word) = Some W_84abc.
Proof. vm_refl. Qed.
Lemma D_84abc : decode_any W_84abc = Some (Branch BC_NE 24 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ac0 : bv 32 := 0xffb00613.
Lemma F_84ac0 : fetch_word Ubsan.M.loaded_segments (0x84ac0 : word) = Some W_84ac0.
Proof. vm_refl. Qed.
Lemma D_84ac0 : decode_any W_84ac0 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ac4 : bv 32 := 0x01a67463.
Lemma F_84ac4 : fetch_word Ubsan.M.loaded_segments (0x84ac4 : word) = Some W_84ac4.
Proof. vm_refl. Qed.
Lemma D_84ac4 : decode_any W_84ac4 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ac8 : bv 32 := 0xa2dfd06f.
Lemma F_84ac8 : fetch_word Ubsan.M.loaded_segments (0x84ac8 : word) = Some W_84ac8.
Proof. vm_refl. Qed.
Lemma D_84ac8 : decode_any W_84ac8 = Some (Jal 0 2087468, 4%Z).
Proof. vm_refl. Qed.

Definition W_84acc : bv 32 := 0x0080f463.
Lemma F_84acc : fetch_word Ubsan.M.loaded_segments (0x84acc : word) = Some W_84acc.
Proof. vm_refl. Qed.
Lemma D_84acc : decode_any W_84acc = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ad0 : bv 32 := 0xa25fd06f.
Lemma F_84ad0 : fetch_word Ubsan.M.loaded_segments (0x84ad0 : word) = Some W_84ad0.
Proof. vm_refl. Qed.
Lemma D_84ad0 : decode_any W_84ad0 = Some (Jal 0 2087460, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ad4 : bv 32 := 0x004d2603.
Lemma F_84ad4 : fetch_word Ubsan.M.loaded_segments (0x84ad4 : word) = Some W_84ad4.
Proof. vm_refl. Qed.
Lemma D_84ad4 : decode_any W_84ad4 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ad8 : bv 32 := 0x011afab3.
Lemma F_84ad8 : fetch_word Ubsan.M.loaded_segments (0x84ad8 : word) = Some W_84ad8.
Proof. vm_refl. Qed.
Lemma D_84ad8 : decode_any W_84ad8 = Some (Op ALU_AND 21 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84adc : bv 32 := 0x0086563b.
Lemma F_84adc : fetch_word Ubsan.M.loaded_segments (0x84adc : word) = Some W_84adc.
Proof. vm_refl. Qed.
Lemma D_84adc : decode_any W_84adc = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ae0 : bv 32 := 0x01f67633.
Lemma F_84ae0 : fetch_word Ubsan.M.loaded_segments (0x84ae0 : word) = Some W_84ae0.
Proof. vm_refl. Qed.
Lemma D_84ae0 : decode_any W_84ae0 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ae4 : bv 32 := 0x01566ab3.
Lemma F_84ae4 : fetch_word Ubsan.M.loaded_segments (0x84ae4 : word) = Some W_84ae4.
Proof. vm_refl. Qed.
Lemma D_84ae4 : decode_any W_84ae4 = Some (Op ALU_OR 21 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ae8 : bv 32 := 0x01c0006f.
Lemma F_84ae8 : fetch_word Ubsan.M.loaded_segments (0x84ae8 : word) = Some W_84ae8.
Proof. vm_refl. Qed.
Lemma D_84ae8 : decode_any W_84ae8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84aec : bv 32 := 0x00061463.
Lemma F_84aec : fetch_word Ubsan.M.loaded_segments (0x84aec : word) = Some W_84aec.
Proof. vm_refl. Qed.
Lemma D_84aec : decode_any W_84aec = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84af0 : bv 32 := 0xa05fd06f.
Lemma F_84af0 : fetch_word Ubsan.M.loaded_segments (0x84af0 : word) = Some W_84af0.
Proof. vm_refl. Qed.
Lemma D_84af0 : decode_any W_84af0 = Some (Jal 0 2087428, 4%Z).
Proof. vm_refl. Qed.

Definition W_84af4 : bv 32 := 0x0080f463.
Lemma F_84af4 : fetch_word Ubsan.M.loaded_segments (0x84af4 : word) = Some W_84af4.
Proof. vm_refl. Qed.
Lemma D_84af4 : decode_any W_84af4 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84af8 : bv 32 := 0x9fdfd06f.
Lemma F_84af8 : fetch_word Ubsan.M.loaded_segments (0x84af8 : word) = Some W_84af8.
Proof. vm_refl. Qed.
Lemma D_84af8 : decode_any W_84af8 = Some (Jal 0 2087420, 4%Z).
Proof. vm_refl. Qed.

Definition W_84afc : bv 32 := 0x000d2603.
Lemma F_84afc : fetch_word Ubsan.M.loaded_segments (0x84afc : word) = Some W_84afc.
Proof. vm_refl. Qed.
Lemma D_84afc : decode_any W_84afc = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b00 : bv 32 := 0x00865abb.
Lemma F_84b00 : fetch_word Ubsan.M.loaded_segments (0x84b00 : word) = Some W_84b00.
Proof. vm_refl. Qed.
Lemma D_84b00 : decode_any W_84b00 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b04 : bv 32 := 0x000b8463.
Lemma F_84b04 : fetch_word Ubsan.M.loaded_segments (0x84b04 : word) = Some W_84b04.
Proof. vm_refl. Qed.
Lemma D_84b04 : decode_any W_84b04 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b08 : bv 32 := 0x9edfd06f.
Lemma F_84b08 : fetch_word Ubsan.M.loaded_segments (0x84b08 : word) = Some W_84b08.
Proof. vm_refl. Qed.
Lemma D_84b08 : decode_any W_84b08 = Some (Jal 0 2087404, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b0c : bv 32 := 0x000c9463.
Lemma F_84b0c : fetch_word Ubsan.M.loaded_segments (0x84b0c : word) = Some W_84b0c.
Proof. vm_refl. Qed.
Lemma D_84b0c : decode_any W_84b0c = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b10 : bv 32 := 0x9e5fd06f.
Lemma F_84b10 : fetch_word Ubsan.M.loaded_segments (0x84b10 : word) = Some W_84b10.
Proof. vm_refl. Qed.
Lemma D_84b10 : decode_any W_84b10 = Some (Jal 0 2087396, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b14 : bv 32 := 0x000ca603.
Lemma F_84b14 : fetch_word Ubsan.M.loaded_segments (0x84b14 : word) = Some W_84b14.
Proof. vm_refl. Qed.
Lemma D_84b14 : decode_any W_84b14 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b18 : bv 32 := 0xfffaca93.
Lemma F_84b18 : fetch_word Ubsan.M.loaded_segments (0x84b18 : word) = Some W_84b18.
Proof. vm_refl. Qed.
Lemma D_84b18 : decode_any W_84b18 = Some (OpImm ALU_XOR 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b1c : bv 32 := 0x015dfab3.
Lemma F_84b1c : fetch_word Ubsan.M.loaded_segments (0x84b1c : word) = Some W_84b1c.
Proof. vm_refl. Qed.
Lemma D_84b1c : decode_any W_84b1c = Some (Op ALU_AND 21 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b20 : bv 32 := 0x00567633.
Lemma F_84b20 : fetch_word Ubsan.M.loaded_segments (0x84b20 : word) = Some W_84b20.
Proof. vm_refl. Qed.
Lemma D_84b20 : decode_any W_84b20 = Some (Op ALU_AND 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b24 : bv 32 := 0x01566633.
Lemma F_84b24 : fetch_word Ubsan.M.loaded_segments (0x84b24 : word) = Some W_84b24.
Proof. vm_refl. Qed.
Lemma D_84b24 : decode_any W_84b24 = Some (Op ALU_OR 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b28 : bv 32 := 0x01038ab3.
Lemma F_84b28 : fetch_word Ubsan.M.loaded_segments (0x84b28 : word) = Some W_84b28.
Proof. vm_refl. Qed.
Lemma D_84b28 : decode_any W_84b28 = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b2c : bv 32 := 0x00cca023.
Lemma F_84b2c : fetch_word Ubsan.M.loaded_segments (0x84b2c : word) = Some W_84b2c.
Proof. vm_refl. Qed.
Lemma D_84b2c : decode_any W_84b2c = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b30 : bv 32 := 0x000a9463.
Lemma F_84b30 : fetch_word Ubsan.M.loaded_segments (0x84b30 : word) = Some W_84b30.
Proof. vm_refl. Qed.
Lemma D_84b30 : decode_any W_84b30 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b34 : bv 32 := 0x9c1fd06f.
Lemma F_84b34 : fetch_word Ubsan.M.loaded_segments (0x84b34 : word) = Some W_84b34.
Proof. vm_refl. Qed.
Lemma D_84b34 : decode_any W_84b34 = Some (Jal 0 2087360, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b38 : bv 32 := 0x010ab633.
Lemma F_84b38 : fetch_word Ubsan.M.loaded_segments (0x84b38 : word) = Some W_84b38.
Proof. vm_refl. Qed.
Lemma D_84b38 : decode_any W_84b38 = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b3c : bv 32 := 0x00964633.
Lemma F_84b3c : fetch_word Ubsan.M.loaded_segments (0x84b3c : word) = Some W_84b3c.
Proof. vm_refl. Qed.
Lemma D_84b3c : decode_any W_84b3c = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b40 : bv 32 := 0x00164613.
Lemma F_84b40 : fetch_word Ubsan.M.loaded_segments (0x84b40 : word) = Some W_84b40.
Proof. vm_refl. Qed.
Lemma D_84b40 : decode_any W_84b40 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b44 : bv 32 := 0x00061463.
Lemma F_84b44 : fetch_word Ubsan.M.loaded_segments (0x84b44 : word) = Some W_84b44.
Proof. vm_refl. Qed.
Lemma D_84b44 : decode_any W_84b44 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b48 : bv 32 := 0x9adfd06f.
Lemma F_84b48 : fetch_word Ubsan.M.loaded_segments (0x84b48 : word) = Some W_84b48.
Proof. vm_refl. Qed.
Lemma D_84b48 : decode_any W_84b48 = Some (Jal 0 2087340, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b4c : bv 32 := 0x00ba0633.
Lemma F_84b4c : fetch_word Ubsan.M.loaded_segments (0x84b4c : word) = Some W_84b4c.
Proof. vm_refl. Qed.
Lemma D_84b4c : decode_any W_84b4c = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b50 : bv 32 := 0x00061463.
Lemma F_84b50 : fetch_word Ubsan.M.loaded_segments (0x84b50 : word) = Some W_84b50.
Proof. vm_refl. Qed.
Lemma D_84b50 : decode_any W_84b50 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b54 : bv 32 := 0x9a1fd06f.
Lemma F_84b54 : fetch_word Ubsan.M.loaded_segments (0x84b54 : word) = Some W_84b54.
Proof. vm_refl. Qed.
Lemma D_84b54 : decode_any W_84b54 = Some (Jal 0 2087328, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b58 : bv 32 := 0x01a63633.
Lemma F_84b58 : fetch_word Ubsan.M.loaded_segments (0x84b58 : word) = Some W_84b58.
Proof. vm_refl. Qed.
Lemma D_84b58 : decode_any W_84b58 = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b5c : bv 32 := 0x07813803.
Lemma F_84b5c : fetch_word Ubsan.M.loaded_segments (0x84b5c : word) = Some W_84b5c.
Proof. vm_refl. Qed.
Lemma D_84b5c : decode_any W_84b5c = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b60 : bv 32 := 0x01064633.
Lemma F_84b60 : fetch_word Ubsan.M.loaded_segments (0x84b60 : word) = Some W_84b60.
Proof. vm_refl. Qed.
Lemma D_84b60 : decode_any W_84b60 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b64 : bv 32 := 0x00164613.
Lemma F_84b64 : fetch_word Ubsan.M.loaded_segments (0x84b64 : word) = Some W_84b64.
Proof. vm_refl. Qed.
Lemma D_84b64 : decode_any W_84b64 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b68 : bv 32 := 0x00061463.
Lemma F_84b68 : fetch_word Ubsan.M.loaded_segments (0x84b68 : word) = Some W_84b68.
Proof. vm_refl. Qed.
Lemma D_84b68 : decode_any W_84b68 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b6c : bv 32 := 0x989fd06f.
Lemma F_84b6c : fetch_word Ubsan.M.loaded_segments (0x84b6c : word) = Some W_84b6c.
Proof. vm_refl. Qed.
Lemma D_84b6c : decode_any W_84b6c = Some (Jal 0 2087304, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b70 : bv 32 := 0x001e0e1b.
Lemma F_84b70 : fetch_word Ubsan.M.loaded_segments (0x84b70 : word) = Some W_84b70.
Proof. vm_refl. Qed.
Lemma D_84b70 : decode_any W_84b70 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b74 : bv 32 := 0x00d585b3.
Lemma F_84b74 : fetch_word Ubsan.M.loaded_segments (0x84b74 : word) = Some W_84b74.
Proof. vm_refl. Qed.
Lemma D_84b74 : decode_any W_84b74 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b78 : bv 32 := 0x007c8cb3.
Lemma F_84b78 : fetch_word Ubsan.M.loaded_segments (0x84b78 : word) = Some W_84b78.
Proof. vm_refl. Qed.
Lemma D_84b78 : decode_any W_84b78 = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b7c : bv 32 := 0x000a8813.
Lemma F_84b7c : fetch_word Ubsan.M.loaded_segments (0x84b7c : word) = Some W_84b7c.
Proof. vm_refl. Qed.
Lemma D_84b7c : decode_any W_84b7c = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b80 : bv 32 := 0xf00e18e3.
Lemma F_84b80 : fetch_word Ubsan.M.loaded_segments (0x84b80 : word) = Some W_84b80.
Proof. vm_refl. Qed.
Lemma D_84b80 : decode_any W_84b80 = Some (Branch BC_NE 28 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b84 : bv 32 := 0x02013583.
Lemma F_84b84 : fetch_word Ubsan.M.loaded_segments (0x84b84 : word) = Some W_84b84.
Proof. vm_refl. Qed.
Lemma D_84b84 : decode_any W_84b84 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b88 : bv 32 := 0x16059263.
Lemma F_84b88 : fetch_word Ubsan.M.loaded_segments (0x84b88 : word) = Some W_84b88.
Proof. vm_refl. Qed.
Lemma D_84b88 : decode_any W_84b88 = Some (Branch BC_NE 11 0 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b8c : bv 32 := 0xffffc693.
Lemma F_84b8c : fetch_word Ubsan.M.loaded_segments (0x84b8c : word) = Some W_84b8c.
Proof. vm_refl. Qed.
Lemma D_84b8c : decode_any W_84b8c = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b90 : bv 32 := 0x00271293.
Lemma F_84b90 : fetch_word Ubsan.M.loaded_segments (0x84b90 : word) = Some W_84b90.
Proof. vm_refl. Qed.
Lemma D_84b90 : decode_any W_84b90 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b94 : bv 32 := 0x05813383.
Lemma F_84b94 : fetch_word Ubsan.M.loaded_segments (0x84b94 : word) = Some W_84b94.
Proof. vm_refl. Qed.
Lemma D_84b94 : decode_any W_84b94 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b98 : bv 32 := 0x00239393.
Lemma F_84b98 : fetch_word Ubsan.M.loaded_segments (0x84b98 : word) = Some W_84b98.
Proof. vm_refl. Qed.
Lemma D_84b98 : decode_any W_84b98 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84b9c : bv 32 := 0x00337613.
Lemma F_84b9c : fetch_word Ubsan.M.loaded_segments (0x84b9c : word) = Some W_84b9c.
Proof. vm_refl. Qed.
Lemma D_84b9c : decode_any W_84b9c = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ba0 : bv 32 := 0x00397793.
Lemma F_84ba0 : fetch_word Ubsan.M.loaded_segments (0x84ba0 : word) = Some W_84ba0.
Proof. vm_refl. Qed.
Lemma D_84ba0 : decode_any W_84ba0 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ba4 : bv 32 := 0x07013a03.
Lemma F_84ba4 : fetch_word Ubsan.M.loaded_segments (0x84ba4 : word) = Some W_84ba4.
Proof. vm_refl. Qed.
Lemma D_84ba4 : decode_any W_84ba4 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ba8 : bv 32 := 0x002a1a13.
Lemma F_84ba8 : fetch_word Ubsan.M.loaded_segments (0x84ba8 : word) = Some W_84ba8.
Proof. vm_refl. Qed.
Lemma D_84ba8 : decode_any W_84ba8 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bac : bv 32 := 0x00072b93.
Lemma F_84bac : fetch_word Ubsan.M.loaded_segments (0x84bac : word) = Some W_84bac.
Proof. vm_refl. Qed.
Lemma D_84bac : decode_any W_84bac = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bb0 : bv 32 := 0x02000993.
Lemma F_84bb0 : fetch_word Ubsan.M.loaded_segments (0x84bb0 : word) = Some W_84bb0.
Proof. vm_refl. Qed.
Lemma D_84bb0 : decode_any W_84bb0 = Some (OpImm ALU_ADD 19 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bb4 : bv 32 := 0xffb00c93.
Lemma F_84bb4 : fetch_word Ubsan.M.loaded_segments (0x84bb4 : word) = Some W_84bb4.
Proof. vm_refl. Qed.
Lemma D_84bb4 : decode_any W_84bb4 = Some (OpImm ALU_ADD 25 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bb8 : bv 32 := 0x0017b893.
Lemma F_84bb8 : fetch_word Ubsan.M.loaded_segments (0x84bb8 : word) = Some W_84bb8.
Proof. vm_refl. Qed.
Lemma D_84bb8 : decode_any W_84bb8 = Some (OpImm ALU_SLTU 17 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bbc : bv 32 := 0x00163b13.
Lemma F_84bbc : fetch_word Ubsan.M.loaded_segments (0x84bbc : word) = Some W_84bbc.
Proof. vm_refl. Qed.
Lemma D_84bbc : decode_any W_84bbc = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bc0 : bv 32 := 0x01f00d13.
Lemma F_84bc0 : fetch_word Ubsan.M.loaded_segments (0x84bc0 : word) = Some W_84bc0.
Proof. vm_refl. Qed.
Lemma D_84bc0 : decode_any W_84bc0 = Some (OpImm ALU_ADD 26 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bc4 : bv 32 := 0x00030d93.
Lemma F_84bc4 : fetch_word Ubsan.M.loaded_segments (0x84bc4 : word) = Some W_84bc4.
Proof. vm_refl. Qed.
Lemma D_84bc4 : decode_any W_84bc4 = Some (OpImm ALU_ADD 27 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bc8 : bv 32 := 0x00090093.
Lemma F_84bc8 : fetch_word Ubsan.M.loaded_segments (0x84bc8 : word) = Some W_84bc8.
Proof. vm_refl. Qed.
Lemma D_84bc8 : decode_any W_84bc8 = Some (OpImm ALU_ADD 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bcc : bv 32 := 0x07013603.
Lemma F_84bcc : fetch_word Ubsan.M.loaded_segments (0x84bcc : word) = Some W_84bcc.
Proof. vm_refl. Qed.
Lemma D_84bcc : decode_any W_84bcc = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bd0 : bv 32 := 0x0a060663.
Lemma F_84bd0 : fetch_word Ubsan.M.loaded_segments (0x84bd0 : word) = Some W_84bd0.
Proof. vm_refl. Qed.
Lemma D_84bd0 : decode_any W_84bd0 = Some (Branch BC_EQ 12 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bd4 : bv 32 := 0x00000c13.
Lemma F_84bd4 : fetch_word Ubsan.M.loaded_segments (0x84bd4 : word) = Some W_84bd4.
Proof. vm_refl. Qed.
Lemma D_84bd4 : decode_any W_84bd4 = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bd8 : bv 32 := 0x00603833.
Lemma F_84bd8 : fetch_word Ubsan.M.loaded_segments (0x84bd8 : word) = Some W_84bd8.
Proof. vm_refl. Qed.
Lemma D_84bd8 : decode_any W_84bd8 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bdc : bv 32 := 0x01203e33.
Lemma F_84bdc : fetch_word Ubsan.M.loaded_segments (0x84bdc : word) = Some W_84bdc.
Proof. vm_refl. Qed.
Lemma D_84bdc : decode_any W_84bdc = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84be0 : bv 32 := 0x010b74b3.
Lemma F_84be0 : fetch_word Ubsan.M.loaded_segments (0x84be0 : word) = Some W_84be0.
Proof. vm_refl. Qed.
Lemma D_84be0 : decode_any W_84be0 = Some (Op ALU_AND 9 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84be4 : bv 32 := 0x01c8fab3.
Lemma F_84be4 : fetch_word Ubsan.M.loaded_segments (0x84be4 : word) = Some W_84be4.
Proof. vm_refl. Qed.
Lemma D_84be4 : decode_any W_84be4 = Some (Op ALU_AND 21 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84be8 : bv 32 := 0x018d8633.
Lemma F_84be8 : fetch_word Ubsan.M.loaded_segments (0x84be8 : word) = Some W_84be8.
Proof. vm_refl. Qed.
Lemma D_84be8 : decode_any W_84be8 = Some (Op ALU_ADD 12 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bec : bv 32 := 0x00667463.
Lemma F_84bec : fetch_word Ubsan.M.loaded_segments (0x84bec : word) = Some W_84bec.
Proof. vm_refl. Qed.
Lemma D_84bec : decode_any W_84bec = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bf0 : bv 32 := 0x905fd06f.
Lemma F_84bf0 : fetch_word Ubsan.M.loaded_segments (0x84bf0 : word) = Some W_84bf0.
Proof. vm_refl. Qed.
Lemma D_84bf0 : decode_any W_84bf0 = Some (Jal 0 2087172, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bf4 : bv 32 := 0x00163613.
Lemma F_84bf4 : fetch_word Ubsan.M.loaded_segments (0x84bf4 : word) = Some W_84bf4.
Proof. vm_refl. Qed.
Lemma D_84bf4 : decode_any W_84bf4 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bf8 : bv 32 := 0x00c84633.
Lemma F_84bf8 : fetch_word Ubsan.M.loaded_segments (0x84bf8 : word) = Some W_84bf8.
Proof. vm_refl. Qed.
Lemma D_84bf8 : decode_any W_84bf8 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84bfc : bv 32 := 0x00061463.
Lemma F_84bfc : fetch_word Ubsan.M.loaded_segments (0x84bfc : word) = Some W_84bfc.
Proof. vm_refl. Qed.
Lemma D_84bfc : decode_any W_84bfc = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c00 : bv 32 := 0x8f5fd06f.
Lemma F_84c00 : fetch_word Ubsan.M.loaded_segments (0x84c00 : word) = Some W_84c00.
Proof. vm_refl. Qed.
Lemma D_84c00 : decode_any W_84c00 = Some (Jal 0 2087156, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c04 : bv 32 := 0x00049463.
Lemma F_84c04 : fetch_word Ubsan.M.loaded_segments (0x84c04 : word) = Some W_84c04.
Proof. vm_refl. Qed.
Lemma D_84c04 : decode_any W_84c04 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c08 : bv 32 := 0x8edfd06f.
Lemma F_84c08 : fetch_word Ubsan.M.loaded_segments (0x84c08 : word) = Some W_84c08.
Proof. vm_refl. Qed.
Lemma D_84c08 : decode_any W_84c08 = Some (Jal 0 2087148, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c0c : bv 32 := 0x013f1463.
Lemma F_84c0c : fetch_word Ubsan.M.loaded_segments (0x84c0c : word) = Some W_84c0c.
Proof. vm_refl. Qed.
Lemma D_84c0c : decode_any W_84c0c = Some (Branch BC_NE 30 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c10 : bv 32 := 0x8e5fd06f.
Lemma F_84c10 : fetch_word Ubsan.M.loaded_segments (0x84c10 : word) = Some W_84c10.
Proof. vm_refl. Qed.
Lemma D_84c10 : decode_any W_84c10 = Some (Jal 0 2087140, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c14 : bv 32 := 0x01830633.
Lemma F_84c14 : fetch_word Ubsan.M.loaded_segments (0x84c14 : word) = Some W_84c14.
Proof. vm_refl. Qed.
Lemma D_84c14 : decode_any W_84c14 = Some (Op ALU_ADD 12 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c18 : bv 32 := 0x00ccf463.
Lemma F_84c18 : fetch_word Ubsan.M.loaded_segments (0x84c18 : word) = Some W_84c18.
Proof. vm_refl. Qed.
Lemma D_84c18 : decode_any W_84c18 = Some (Branch BC_GEU 25 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c1c : bv 32 := 0x8d9fd06f.
Lemma F_84c1c : fetch_word Ubsan.M.loaded_segments (0x84c1c : word) = Some W_84c1c.
Proof. vm_refl. Qed.
Lemma D_84c1c : decode_any W_84c1c = Some (Jal 0 2087128, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c20 : bv 32 := 0x008d7463.
Lemma F_84c20 : fetch_word Ubsan.M.loaded_segments (0x84c20 : word) = Some W_84c20.
Proof. vm_refl. Qed.
Lemma D_84c20 : decode_any W_84c20 = Some (Branch BC_GEU 26 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c24 : bv 32 := 0x8d1fd06f.
Lemma F_84c24 : fetch_word Ubsan.M.loaded_segments (0x84c24 : word) = Some W_84c24.
Proof. vm_refl. Qed.
Lemma D_84c24 : decode_any W_84c24 = Some (Jal 0 2087120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c28 : bv 32 := 0x018087b3.
Lemma F_84c28 : fetch_word Ubsan.M.loaded_segments (0x84c28 : word) = Some W_84c28.
Proof. vm_refl. Qed.
Lemma D_84c28 : decode_any W_84c28 = Some (Op ALU_ADD 15 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c2c : bv 32 := 0x0127f463.
Lemma F_84c2c : fetch_word Ubsan.M.loaded_segments (0x84c2c : word) = Some W_84c2c.
Proof. vm_refl. Qed.
Lemma D_84c2c : decode_any W_84c2c = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c30 : bv 32 := 0x8c5fd06f.
Lemma F_84c30 : fetch_word Ubsan.M.loaded_segments (0x84c30 : word) = Some W_84c30.
Proof. vm_refl. Qed.
Lemma D_84c30 : decode_any W_84c30 = Some (Jal 0 2087108, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c34 : bv 32 := 0x0017b793.
Lemma F_84c34 : fetch_word Ubsan.M.loaded_segments (0x84c34 : word) = Some W_84c34.
Proof. vm_refl. Qed.
Lemma D_84c34 : decode_any W_84c34 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c38 : bv 32 := 0x00fe47b3.
Lemma F_84c38 : fetch_word Ubsan.M.loaded_segments (0x84c38 : word) = Some W_84c38.
Proof. vm_refl. Qed.
Lemma D_84c38 : decode_any W_84c38 = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c3c : bv 32 := 0x00079463.
Lemma F_84c3c : fetch_word Ubsan.M.loaded_segments (0x84c3c : word) = Some W_84c3c.
Proof. vm_refl. Qed.
Lemma D_84c3c : decode_any W_84c3c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c40 : bv 32 := 0x8b5fd06f.
Lemma F_84c40 : fetch_word Ubsan.M.loaded_segments (0x84c40 : word) = Some W_84c40.
Proof. vm_refl. Qed.
Lemma D_84c40 : decode_any W_84c40 = Some (Jal 0 2087092, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c44 : bv 32 := 0x000a9463.
Lemma F_84c44 : fetch_word Ubsan.M.loaded_segments (0x84c44 : word) = Some W_84c44.
Proof. vm_refl. Qed.
Lemma D_84c44 : decode_any W_84c44 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c48 : bv 32 := 0x8adfd06f.
Lemma F_84c48 : fetch_word Ubsan.M.loaded_segments (0x84c48 : word) = Some W_84c48.
Proof. vm_refl. Qed.
Lemma D_84c48 : decode_any W_84c48 = Some (Jal 0 2087084, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c4c : bv 32 := 0x00062783.
Lemma F_84c4c : fetch_word Ubsan.M.loaded_segments (0x84c4c : word) = Some W_84c4c.
Proof. vm_refl. Qed.
Lemma D_84c4c : decode_any W_84c4c = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c50 : bv 32 := 0x00462603.
Lemma F_84c50 : fetch_word Ubsan.M.loaded_segments (0x84c50 : word) = Some W_84c50.
Proof. vm_refl. Qed.
Lemma D_84c50 : decode_any W_84c50 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c54 : bv 32 := 0x01d797bb.
Lemma F_84c54 : fetch_word Ubsan.M.loaded_segments (0x84c54 : word) = Some W_84c54.
Proof. vm_refl. Qed.
Lemma D_84c54 : decode_any W_84c54 = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c58 : bv 32 := 0x0086563b.
Lemma F_84c58 : fetch_word Ubsan.M.loaded_segments (0x84c58 : word) = Some W_84c58.
Proof. vm_refl. Qed.
Lemma D_84c58 : decode_any W_84c58 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c5c : bv 32 := 0x00d7f7b3.
Lemma F_84c5c : fetch_word Ubsan.M.loaded_segments (0x84c5c : word) = Some W_84c5c.
Proof. vm_refl. Qed.
Lemma D_84c5c : decode_any W_84c5c = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c60 : bv 32 := 0x01f67633.
Lemma F_84c60 : fetch_word Ubsan.M.loaded_segments (0x84c60 : word) = Some W_84c60.
Proof. vm_refl. Qed.
Lemma D_84c60 : decode_any W_84c60 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c64 : bv 32 := 0x00f66633.
Lemma F_84c64 : fetch_word Ubsan.M.loaded_segments (0x84c64 : word) = Some W_84c64.
Proof. vm_refl. Qed.
Lemma D_84c64 : decode_any W_84c64 = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c68 : bv 32 := 0x018907b3.
Lemma F_84c68 : fetch_word Ubsan.M.loaded_segments (0x84c68 : word) = Some W_84c68.
Proof. vm_refl. Qed.
Lemma D_84c68 : decode_any W_84c68 = Some (Op ALU_ADD 15 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c6c : bv 32 := 0xfff64613.
Lemma F_84c6c : fetch_word Ubsan.M.loaded_segments (0x84c6c : word) = Some W_84c6c.
Proof. vm_refl. Qed.
Lemma D_84c6c : decode_any W_84c6c = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c70 : bv 32 := 0x004c0c13.
Lemma F_84c70 : fetch_word Ubsan.M.loaded_segments (0x84c70 : word) = Some W_84c70.
Proof. vm_refl. Qed.
Lemma D_84c70 : decode_any W_84c70 = Some (OpImm ALU_ADD 24 24 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c74 : bv 32 := 0x00c7a023.
Lemma F_84c74 : fetch_word Ubsan.M.loaded_segments (0x84c74 : word) = Some W_84c74.
Proof. vm_refl. Qed.
Lemma D_84c74 : decode_any W_84c74 = Some (Store SZ4 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c78 : bv 32 := 0xf78a18e3.
Lemma F_84c78 : fetch_word Ubsan.M.loaded_segments (0x84c78 : word) = Some W_84c78.
Proof. vm_refl. Qed.
Lemma D_84c78 : decode_any W_84c78 = Some (Branch BC_NE 20 24 8048, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c7c : bv 32 := 0x00590633.
Lemma F_84c7c : fetch_word Ubsan.M.loaded_segments (0x84c7c : word) = Some W_84c7c.
Proof. vm_refl. Qed.
Lemma D_84c7c : decode_any W_84c7c = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c80 : bv 32 := 0x012037b3.
Lemma F_84c80 : fetch_word Ubsan.M.loaded_segments (0x84c80 : word) = Some W_84c80.
Proof. vm_refl. Qed.
Lemma D_84c80 : decode_any W_84c80 = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c84 : bv 32 := 0x00163813.
Lemma F_84c84 : fetch_word Ubsan.M.loaded_segments (0x84c84 : word) = Some W_84c84.
Proof. vm_refl. Qed.
Lemma D_84c84 : decode_any W_84c84 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c88 : bv 32 := 0x01079463.
Lemma F_84c88 : fetch_word Ubsan.M.loaded_segments (0x84c88 : word) = Some W_84c88.
Proof. vm_refl. Qed.
Lemma D_84c88 : decode_any W_84c88 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c8c : bv 32 := 0x869fd06f.
Lemma F_84c8c : fetch_word Ubsan.M.loaded_segments (0x84c8c : word) = Some W_84c8c.
Proof. vm_refl. Qed.
Lemma D_84c8c : decode_any W_84c8c = Some (Jal 0 2087016, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c90 : bv 32 := 0x01263633.
Lemma F_84c90 : fetch_word Ubsan.M.loaded_segments (0x84c90 : word) = Some W_84c90.
Proof. vm_refl. Qed.
Lemma D_84c90 : decode_any W_84c90 = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c94 : bv 32 := 0x01764633.
Lemma F_84c94 : fetch_word Ubsan.M.loaded_segments (0x84c94 : word) = Some W_84c94.
Proof. vm_refl. Qed.
Lemma D_84c94 : decode_any W_84c94 = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c98 : bv 32 := 0x00164613.
Lemma F_84c98 : fetch_word Ubsan.M.loaded_segments (0x84c98 : word) = Some W_84c98.
Proof. vm_refl. Qed.
Lemma D_84c98 : decode_any W_84c98 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c9c : bv 32 := 0x00061463.
Lemma F_84c9c : fetch_word Ubsan.M.loaded_segments (0x84c9c : word) = Some W_84c9c.
Proof. vm_refl. Qed.
Lemma D_84c9c : decode_any W_84c9c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ca0 : bv 32 := 0x855fd06f.
Lemma F_84ca0 : fetch_word Ubsan.M.loaded_segments (0x84ca0 : word) = Some W_84ca0.
Proof. vm_refl. Qed.
Lemma D_84ca0 : decode_any W_84ca0 = Some (Jal 0 2086996, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ca4 : bv 32 := 0x00638633.
Lemma F_84ca4 : fetch_word Ubsan.M.loaded_segments (0x84ca4 : word) = Some W_84ca4.
Proof. vm_refl. Qed.
Lemma D_84ca4 : decode_any W_84ca4 = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ca8 : bv 32 := 0x006037b3.
Lemma F_84ca8 : fetch_word Ubsan.M.loaded_segments (0x84ca8 : word) = Some W_84ca8.
Proof. vm_refl. Qed.
Lemma D_84ca8 : decode_any W_84ca8 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cac : bv 32 := 0x00163813.
Lemma F_84cac : fetch_word Ubsan.M.loaded_segments (0x84cac : word) = Some W_84cac.
Proof. vm_refl. Qed.
Lemma D_84cac : decode_any W_84cac = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cb0 : bv 32 := 0x01079463.
Lemma F_84cb0 : fetch_word Ubsan.M.loaded_segments (0x84cb0 : word) = Some W_84cb0.
Proof. vm_refl. Qed.
Lemma D_84cb0 : decode_any W_84cb0 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cb4 : bv 32 := 0x841fd06f.
Lemma F_84cb4 : fetch_word Ubsan.M.loaded_segments (0x84cb4 : word) = Some W_84cb4.
Proof. vm_refl. Qed.
Lemma D_84cb4 : decode_any W_84cb4 = Some (Jal 0 2086976, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cb8 : bv 32 := 0x006637b3.
Lemma F_84cb8 : fetch_word Ubsan.M.loaded_segments (0x84cb8 : word) = Some W_84cb8.
Proof. vm_refl. Qed.
Lemma D_84cb8 : decode_any W_84cb8 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cbc : bv 32 := 0x07813803.
Lemma F_84cbc : fetch_word Ubsan.M.loaded_segments (0x84cbc : word) = Some W_84cbc.
Proof. vm_refl. Qed.
Lemma D_84cbc : decode_any W_84cbc = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cc0 : bv 32 := 0x0107c7b3.
Lemma F_84cc0 : fetch_word Ubsan.M.loaded_segments (0x84cc0 : word) = Some W_84cc0.
Proof. vm_refl. Qed.
Lemma D_84cc0 : decode_any W_84cc0 = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cc4 : bv 32 := 0x0017c793.
Lemma F_84cc4 : fetch_word Ubsan.M.loaded_segments (0x84cc4 : word) = Some W_84cc4.
Proof. vm_refl. Qed.
Lemma D_84cc4 : decode_any W_84cc4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cc8 : bv 32 := 0x00079463.
Lemma F_84cc8 : fetch_word Ubsan.M.loaded_segments (0x84cc8 : word) = Some W_84cc8.
Proof. vm_refl. Qed.
Lemma D_84cc8 : decode_any W_84cc8 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ccc : bv 32 := 0x829fd06f.
Lemma F_84ccc : fetch_word Ubsan.M.loaded_segments (0x84ccc : word) = Some W_84ccc.
Proof. vm_refl. Qed.
Lemma D_84ccc : decode_any W_84ccc = Some (Jal 0 2086952, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cd0 : bv 32 := 0x00590933.
Lemma F_84cd0 : fetch_word Ubsan.M.loaded_segments (0x84cd0 : word) = Some W_84cd0.
Proof. vm_refl. Qed.
Lemma D_84cd0 : decode_any W_84cd0 = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cd4 : bv 32 := 0x0015859b.
Lemma F_84cd4 : fetch_word Ubsan.M.loaded_segments (0x84cd4 : word) = Some W_84cd4.
Proof. vm_refl. Qed.
Lemma D_84cd4 : decode_any W_84cd4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cd8 : bv 32 := 0x005080b3.
Lemma F_84cd8 : fetch_word Ubsan.M.loaded_segments (0x84cd8 : word) = Some W_84cd8.
Proof. vm_refl. Qed.
Lemma D_84cd8 : decode_any W_84cd8 = Some (Op ALU_ADD 1 1 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cdc : bv 32 := 0x007d8db3.
Lemma F_84cdc : fetch_word Ubsan.M.loaded_segments (0x84cdc : word) = Some W_84cdc.
Proof. vm_refl. Qed.
Lemma D_84cdc : decode_any W_84cdc = Some (Op ALU_ADD 27 27 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ce0 : bv 32 := 0x00060313.
Lemma F_84ce0 : fetch_word Ubsan.M.loaded_segments (0x84ce0 : word) = Some W_84ce0.
Proof. vm_refl. Qed.
Lemma D_84ce0 : decode_any W_84ce0 = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ce4 : bv 32 := 0x08013603.
Lemma F_84ce4 : fetch_word Ubsan.M.loaded_segments (0x84ce4 : word) = Some W_84ce4.
Proof. vm_refl. Qed.
Lemma D_84ce4 : decode_any W_84ce4 = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ce8 : bv 32 := 0xeec592e3.
Lemma F_84ce8 : fetch_word Ubsan.M.loaded_segments (0x84ce8 : word) = Some W_84ce8.
Proof. vm_refl. Qed.
Lemma D_84ce8 : decode_any W_84ce8 = Some (Branch BC_NE 11 12 7908, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cec : bv 32 := 0x01813583.
Lemma F_84cec : fetch_word Ubsan.M.loaded_segments (0x84cec : word) = Some W_84cec.
Proof. vm_refl. Qed.
Lemma D_84cec : decode_any W_84cec = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cf0 : bv 32 := 0x00058463.
Lemma F_84cf0 : fetch_word Ubsan.M.loaded_segments (0x84cf0 : word) = Some W_84cf0.
Proof. vm_refl. Qed.
Lemma D_84cf0 : decode_any W_84cf0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cf4 : bv 32 := 0x0c50206f.
Lemma F_84cf4 : fetch_word Ubsan.M.loaded_segments (0x84cf4 : word) = Some W_84cf4.
Proof. vm_refl. Qed.
Lemma D_84cf4 : decode_any W_84cf4 = Some (Jal 0 10436, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cf8 : bv 32 := 0x06813583.
Lemma F_84cf8 : fetch_word Ubsan.M.loaded_segments (0x84cf8 : word) = Some W_84cf8.
Proof. vm_refl. Qed.
Lemma D_84cf8 : decode_any W_84cf8 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cfc : bv 32 := 0x0035f593.
Lemma F_84cfc : fetch_word Ubsan.M.loaded_segments (0x84cfc : word) = Some W_84cfc.
Proof. vm_refl. Qed.
Lemma D_84cfc : decode_any W_84cfc = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d00 : bv 32 := 0x00058463.
Lemma F_84d00 : fetch_word Ubsan.M.loaded_segments (0x84d00 : word) = Some W_84d00.
Proof. vm_refl. Qed.
Lemma D_84d00 : decode_any W_84d00 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d04 : bv 32 := 0xff0fd06f.
Lemma F_84d04 : fetch_word Ubsan.M.loaded_segments (0x84d04 : word) = Some W_84d04.
Proof. vm_refl. Qed.
Lemma D_84d04 : decode_any W_84d04 = Some (Jal 0 2086896, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d08 : bv 32 := 0xffffc613.
Lemma F_84d08 : fetch_word Ubsan.M.loaded_segments (0x84d08 : word) = Some W_84d08.
Proof. vm_refl. Qed.
Lemma D_84d08 : decode_any W_84d08 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d0c : bv 32 := 0x06013683.
Lemma F_84d0c : fetch_word Ubsan.M.loaded_segments (0x84d0c : word) = Some W_84d0c.
Proof. vm_refl. Qed.
Lemma D_84d0c : decode_any W_84d0c = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d10 : bv 32 := 0xfff6c693.
Lemma F_84d10 : fetch_word Ubsan.M.loaded_segments (0x84d10 : word) = Some W_84d10.
Proof. vm_refl. Qed.
Lemma D_84d10 : decode_any W_84d10 = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d14 : bv 32 := 0x00271793.
Lemma F_84d14 : fetch_word Ubsan.M.loaded_segments (0x84d14 : word) = Some W_84d14.
Proof. vm_refl. Qed.
Lemma D_84d14 : decode_any W_84d14 = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d18 : bv 32 := 0x05813303.
Lemma F_84d18 : fetch_word Ubsan.M.loaded_segments (0x84d18 : word) = Some W_84d18.
Proof. vm_refl. Qed.
Lemma D_84d18 : decode_any W_84d18 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d1c : bv 32 := 0x00231313.
Lemma F_84d1c : fetch_word Ubsan.M.loaded_segments (0x84d1c : word) = Some W_84d1c.
Proof. vm_refl. Qed.
Lemma D_84d1c : decode_any W_84d1c = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d20 : bv 32 := 0x00357893.
Lemma F_84d20 : fetch_word Ubsan.M.loaded_segments (0x84d20 : word) = Some W_84d20.
Proof. vm_refl. Qed.
Lemma D_84d20 : decode_any W_84d20 = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d24 : bv 32 := 0x05013903.
Lemma F_84d24 : fetch_word Ubsan.M.loaded_segments (0x84d24 : word) = Some W_84d24.
Proof. vm_refl. Qed.
Lemma D_84d24 : decode_any W_84d24 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d28 : bv 32 := 0x02813803.
Lemma F_84d28 : fetch_word Ubsan.M.loaded_segments (0x84d28 : word) = Some W_84d28.
Proof. vm_refl. Qed.
Lemma D_84d28 : decode_any W_84d28 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d2c : bv 32 := 0x412804bb.
Lemma F_84d2c : fetch_word Ubsan.M.loaded_segments (0x84d2c : word) = Some W_84d2c.
Proof. vm_refl. Qed.
Lemma D_84d2c : decode_any W_84d2c = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d30 : bv 32 := 0x03813383.
Lemma F_84d30 : fetch_word Ubsan.M.loaded_segments (0x84d30 : word) = Some W_84d30.
Proof. vm_refl. Qed.
Lemma D_84d30 : decode_any W_84d30 = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d34 : bv 32 := 0x03013803.
Lemma F_84d34 : fetch_word Ubsan.M.loaded_segments (0x84d34 : word) = Some W_84d34.
Proof. vm_refl. Qed.
Lemma D_84d34 : decode_any W_84d34 = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d38 : bv 32 := 0x007803b3.
Lemma F_84d38 : fetch_word Ubsan.M.loaded_segments (0x84d38 : word) = Some W_84d38.
Proof. vm_refl. Qed.
Lemma D_84d38 : decode_any W_84d38 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d3c : bv 32 := 0x04813283.
Lemma F_84d3c : fetch_word Ubsan.M.loaded_segments (0x84d3c : word) = Some W_84d3c.
Proof. vm_refl. Qed.
Lemma D_84d3c : decode_any W_84d3c = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d40 : bv 32 := 0x43f2d813.
Lemma F_84d40 : fetch_word Ubsan.M.loaded_segments (0x84d40 : word) = Some W_84d40.
Proof. vm_refl. Qed.
Lemma D_84d40 : decode_any W_84d40 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d44 : bv 32 := 0x00587e33.
Lemma F_84d44 : fetch_word Ubsan.M.loaded_segments (0x84d44 : word) = Some W_84d44.
Proof. vm_refl. Qed.
Lemma D_84d44 : decode_any W_84d44 = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d48 : bv 32 := 0x02000813.
Lemma F_84d48 : fetch_word Ubsan.M.loaded_segments (0x84d48 : word) = Some W_84d48.
Proof. vm_refl. Qed.
Lemma D_84d48 : decode_any W_84d48 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d4c : bv 32 := 0x00813283.
Lemma F_84d4c : fetch_word Ubsan.M.loaded_segments (0x84d4c : word) = Some W_84d4c.
Proof. vm_refl. Qed.
Lemma D_84d4c : decode_any W_84d4c = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d50 : bv 32 := 0x0012f293.
Lemma F_84d50 : fetch_word Ubsan.M.loaded_segments (0x84d50 : word) = Some W_84d50.
Proof. vm_refl. Qed.
Lemma D_84d50 : decode_any W_84d50 = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d54 : bv 32 := 0x00072713.
Lemma F_84d54 : fetch_word Ubsan.M.loaded_segments (0x84d54 : word) = Some W_84d54.
Proof. vm_refl. Qed.
Lemma D_84d54 : decode_any W_84d54 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d58 : bv 32 := 0x01c38e33.
Lemma F_84d58 : fetch_word Ubsan.M.loaded_segments (0x84d58 : word) = Some W_84d58.
Proof. vm_refl. Qed.
Lemma D_84d58 : decode_any W_84d58 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d5c : bv 32 := 0xffb00393.
Lemma F_84d5c : fetch_word Ubsan.M.loaded_segments (0x84d5c : word) = Some W_84d5c.
Proof. vm_refl. Qed.
Lemma D_84d5c : decode_any W_84d5c = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d60 : bv 32 := 0x412e09bb.
Lemma F_84d60 : fetch_word Ubsan.M.loaded_segments (0x84d60 : word) = Some W_84d60.
Proof. vm_refl. Qed.
Lemma D_84d60 : decode_any W_84d60 = Some (Op32 ALU_SUB 19 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d64 : bv 32 := 0x06813e03.
Lemma F_84d64 : fetch_word Ubsan.M.loaded_segments (0x84d64 : word) = Some W_84d64.
Proof. vm_refl. Qed.
Lemma D_84d64 : decode_any W_84d64 = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d68 : bv 32 := 0x006e0e33.
Lemma F_84d68 : fetch_word Ubsan.M.loaded_segments (0x84d68 : word) = Some W_84d68.
Proof. vm_refl. Qed.
Lemma D_84d68 : decode_any W_84d68 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d6c : bv 32 := 0x04013903.
Lemma F_84d6c : fetch_word Ubsan.M.loaded_segments (0x84d6c : word) = Some W_84d6c.
Proof. vm_refl. Qed.
Lemma D_84d6c : decode_any W_84d6c = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d70 : bv 32 := 0x412989bb.
Lemma F_84d70 : fetch_word Ubsan.M.loaded_segments (0x84d70 : word) = Some W_84d70.
Proof. vm_refl. Qed.
Lemma D_84d70 : decode_any W_84d70 = Some (Op32 ALU_SUB 19 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d74 : bv 32 := 0x43f9da13.
Lemma F_84d74 : fetch_word Ubsan.M.loaded_segments (0x84d74 : word) = Some W_84d74.
Proof. vm_refl. Qed.
Lemma D_84d74 : decode_any W_84d74 = Some (ShiftImm ALU_SRA 20 19 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d78 : bv 32 := 0x013a79b3.
Lemma F_84d78 : fetch_word Ubsan.M.loaded_segments (0x84d78 : word) = Some W_84d78.
Proof. vm_refl. Qed.
Lemma D_84d78 : decode_any W_84d78 = Some (Op ALU_AND 19 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d7c : bv 32 := 0x413484bb.
Lemma F_84d7c : fetch_word Ubsan.M.loaded_segments (0x84d7c : word) = Some W_84d7c.
Proof. vm_refl. Qed.
Lemma D_84d7c : decode_any W_84d7c = Some (Op32 ALU_SUB 9 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d80 : bv 32 := 0x01f00993.
Lemma F_84d80 : fetch_word Ubsan.M.loaded_segments (0x84d80 : word) = Some W_84d80.
Proof. vm_refl. Qed.
Lemma D_84d80 : decode_any W_84d80 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d84 : bv 32 := 0x00050a13.
Lemma F_84d84 : fetch_word Ubsan.M.loaded_segments (0x84d84 : word) = Some W_84d84.
Proof. vm_refl. Qed.
Lemma D_84d84 : decode_any W_84d84 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d88 : bv 32 := 0x06813a83.
Lemma F_84d88 : fetch_word Ubsan.M.loaded_segments (0x84d88 : word) = Some W_84d88.
Proof. vm_refl. Qed.
Lemma D_84d88 : decode_any W_84d88 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d8c : bv 32 := 0x00ba8ab3.
Lemma F_84d8c : fetch_word Ubsan.M.loaded_segments (0x84d8c : word) = Some W_84d8c.
Proof. vm_refl. Qed.
Lemma D_84d8c : decode_any W_84d8c = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d90 : bv 32 := 0x000a9463.
Lemma F_84d90 : fetch_word Ubsan.M.loaded_segments (0x84d90 : word) = Some W_84d90.
Proof. vm_refl. Qed.
Lemma D_84d90 : decode_any W_84d90 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d94 : bv 32 := 0xf60fd06f.
Lemma F_84d94 : fetch_word Ubsan.M.loaded_segments (0x84d94 : word) = Some W_84d94.
Proof. vm_refl. Qed.
Lemma D_84d94 : decode_any W_84d94 = Some (Jal 0 2086752, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d98 : bv 32 := 0x010f1463.
Lemma F_84d98 : fetch_word Ubsan.M.loaded_segments (0x84d98 : word) = Some W_84d98.
Proof. vm_refl. Qed.
Lemma D_84d98 : decode_any W_84d98 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84d9c : bv 32 := 0xf58fd06f.
Lemma F_84d9c : fetch_word Ubsan.M.loaded_segments (0x84d9c : word) = Some W_84d9c.
Proof. vm_refl. Qed.
Lemma D_84d9c : decode_any W_84d9c = Some (Jal 0 2086744, 4%Z).
Proof. vm_refl. Qed.

Definition W_84da0 : bv 32 := 0x000aab03.
Lemma F_84da0 : fetch_word Ubsan.M.loaded_segments (0x84da0 : word) = Some W_84da0.
Proof. vm_refl. Qed.
Lemma D_84da0 : decode_any W_84da0 = Some (Load SZ4 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84da4 : bv 32 := 0x01db1b3b.
Lemma F_84da4 : fetch_word Ubsan.M.loaded_segments (0x84da4 : word) = Some W_84da4.
Proof. vm_refl. Qed.
Lemma D_84da4 : decode_any W_84da4 = Some (Op32 ALU_SLL 22 22 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84da8 : bv 32 := 0x02029463.
Lemma F_84da8 : fetch_word Ubsan.M.loaded_segments (0x84da8 : word) = Some W_84da8.
Proof. vm_refl. Qed.
Lemma D_84da8 : decode_any W_84da8 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dac : bv 32 := 0x0153f463.
Lemma F_84dac : fetch_word Ubsan.M.loaded_segments (0x84dac : word) = Some W_84dac.
Proof. vm_refl. Qed.
Lemma D_84dac : decode_any W_84dac = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84db0 : bv 32 := 0xf44fd06f.
Lemma F_84db0 : fetch_word Ubsan.M.loaded_segments (0x84db0 : word) = Some W_84db0.
Proof. vm_refl. Qed.
Lemma D_84db0 : decode_any W_84db0 = Some (Jal 0 2086724, 4%Z).
Proof. vm_refl. Qed.

Definition W_84db4 : bv 32 := 0x0089f463.
Lemma F_84db4 : fetch_word Ubsan.M.loaded_segments (0x84db4 : word) = Some W_84db4.
Proof. vm_refl. Qed.
Lemma D_84db4 : decode_any W_84db4 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84db8 : bv 32 := 0xf3cfd06f.
Lemma F_84db8 : fetch_word Ubsan.M.loaded_segments (0x84db8 : word) = Some W_84db8.
Proof. vm_refl. Qed.
Lemma D_84db8 : decode_any W_84db8 = Some (Jal 0 2086716, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dbc : bv 32 := 0x004aab83.
Lemma F_84dbc : fetch_word Ubsan.M.loaded_segments (0x84dbc : word) = Some W_84dbc.
Proof. vm_refl. Qed.
Lemma D_84dbc : decode_any W_84dbc = Some (Load SZ4 true 23 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dc0 : bv 32 := 0x00cb7b33.
Lemma F_84dc0 : fetch_word Ubsan.M.loaded_segments (0x84dc0 : word) = Some W_84dc0.
Proof. vm_refl. Qed.
Lemma D_84dc0 : decode_any W_84dc0 = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dc4 : bv 32 := 0x008bdbbb.
Lemma F_84dc4 : fetch_word Ubsan.M.loaded_segments (0x84dc4 : word) = Some W_84dc4.
Proof. vm_refl. Qed.
Lemma D_84dc4 : decode_any W_84dc4 = Some (Op32 ALU_SRL 23 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dc8 : bv 32 := 0x01fbfbb3.
Lemma F_84dc8 : fetch_word Ubsan.M.loaded_segments (0x84dc8 : word) = Some W_84dc8.
Proof. vm_refl. Qed.
Lemma D_84dc8 : decode_any W_84dc8 = Some (Op ALU_AND 23 23 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dcc : bv 32 := 0x016beb33.
Lemma F_84dcc : fetch_word Ubsan.M.loaded_segments (0x84dcc : word) = Some W_84dcc.
Proof. vm_refl. Qed.
Lemma D_84dcc : decode_any W_84dcc = Some (Op ALU_OR 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dd0 : bv 32 := 0x00088463.
Lemma F_84dd0 : fetch_word Ubsan.M.loaded_segments (0x84dd0 : word) = Some W_84dd0.
Proof. vm_refl. Qed.
Lemma D_84dd0 : decode_any W_84dd0 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dd4 : bv 32 := 0xf20fd06f.
Lemma F_84dd4 : fetch_word Ubsan.M.loaded_segments (0x84dd4 : word) = Some W_84dd4.
Proof. vm_refl. Qed.
Lemma D_84dd4 : decode_any W_84dd4 = Some (Jal 0 2086688, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dd8 : bv 32 := 0x00051463.
Lemma F_84dd8 : fetch_word Ubsan.M.loaded_segments (0x84dd8 : word) = Some W_84dd8.
Proof. vm_refl. Qed.
Lemma D_84dd8 : decode_any W_84dd8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ddc : bv 32 := 0xf18fd06f.
Lemma F_84ddc : fetch_word Ubsan.M.loaded_segments (0x84ddc : word) = Some W_84ddc.
Proof. vm_refl. Qed.
Lemma D_84ddc : decode_any W_84ddc = Some (Jal 0 2086680, 4%Z).
Proof. vm_refl. Qed.

Definition W_84de0 : bv 32 := 0x00052b83.
Lemma F_84de0 : fetch_word Ubsan.M.loaded_segments (0x84de0 : word) = Some W_84de0.
Proof. vm_refl. Qed.
Lemma D_84de0 : decode_any W_84de0 = Some (Load SZ4 true 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84de4 : bv 32 := 0xfffb4b13.
Lemma F_84de4 : fetch_word Ubsan.M.loaded_segments (0x84de4 : word) = Some W_84de4.
Proof. vm_refl. Qed.
Lemma D_84de4 : decode_any W_84de4 = Some (OpImm ALU_XOR 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84de8 : bv 32 := 0x06013903.
Lemma F_84de8 : fetch_word Ubsan.M.loaded_segments (0x84de8 : word) = Some W_84de8.
Proof. vm_refl. Qed.
Lemma D_84de8 : decode_any W_84de8 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dec : bv 32 := 0x01697b33.
Lemma F_84dec : fetch_word Ubsan.M.loaded_segments (0x84dec : word) = Some W_84dec.
Proof. vm_refl. Qed.
Lemma D_84dec : decode_any W_84dec = Some (Op ALU_AND 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_84df0 : bv 32 := 0x00dbfbb3.
Lemma F_84df0 : fetch_word Ubsan.M.loaded_segments (0x84df0 : word) = Some W_84df0.
Proof. vm_refl. Qed.
Lemma D_84df0 : decode_any W_84df0 = Some (Op ALU_AND 23 23 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84df4 : bv 32 := 0x016bebb3.
Lemma F_84df4 : fetch_word Ubsan.M.loaded_segments (0x84df4 : word) = Some W_84df4.
Proof. vm_refl. Qed.
Lemma D_84df4 : decode_any W_84df4 = Some (Op ALU_OR 23 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_84df8 : bv 32 := 0x01478b33.
Lemma F_84df8 : fetch_word Ubsan.M.loaded_segments (0x84df8 : word) = Some W_84df8.
Proof. vm_refl. Qed.
Lemma D_84df8 : decode_any W_84df8 = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_84dfc : bv 32 := 0x01752023.
Lemma F_84dfc : fetch_word Ubsan.M.loaded_segments (0x84dfc : word) = Some W_84dfc.
Proof. vm_refl. Qed.
Lemma D_84dfc : decode_any W_84dfc = Some (Store SZ4 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e00 : bv 32 := 0x000b1463.
Lemma F_84e00 : fetch_word Ubsan.M.loaded_segments (0x84e00 : word) = Some W_84e00.
Proof. vm_refl. Qed.
Lemma D_84e00 : decode_any W_84e00 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e04 : bv 32 := 0xef0fd06f.
Lemma F_84e04 : fetch_word Ubsan.M.loaded_segments (0x84e04 : word) = Some W_84e04.
Proof. vm_refl. Qed.
Lemma D_84e04 : decode_any W_84e04 = Some (Jal 0 2086640, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e08 : bv 32 := 0x014b3a33.
Lemma F_84e08 : fetch_word Ubsan.M.loaded_segments (0x84e08 : word) = Some W_84e08.
Proof. vm_refl. Qed.
Lemma D_84e08 : decode_any W_84e08 = Some (Op ALU_SLTU 20 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e0c : bv 32 := 0x00ea4a33.
Lemma F_84e0c : fetch_word Ubsan.M.loaded_segments (0x84e0c : word) = Some W_84e0c.
Proof. vm_refl. Qed.
Lemma D_84e0c : decode_any W_84e0c = Some (Op ALU_XOR 20 20 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e10 : bv 32 := 0x001a4a13.
Lemma F_84e10 : fetch_word Ubsan.M.loaded_segments (0x84e10 : word) = Some W_84e10.
Proof. vm_refl. Qed.
Lemma D_84e10 : decode_any W_84e10 = Some (OpImm ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e14 : bv 32 := 0x000a1463.
Lemma F_84e14 : fetch_word Ubsan.M.loaded_segments (0x84e14 : word) = Some W_84e14.
Proof. vm_refl. Qed.
Lemma D_84e14 : decode_any W_84e14 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e18 : bv 32 := 0xedcfd06f.
Lemma F_84e18 : fetch_word Ubsan.M.loaded_segments (0x84e18 : word) = Some W_84e18.
Proof. vm_refl. Qed.
Lemma D_84e18 : decode_any W_84e18 = Some (Jal 0 2086620, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e1c : bv 32 := 0x00be0a33.
Lemma F_84e1c : fetch_word Ubsan.M.loaded_segments (0x84e1c : word) = Some W_84e1c.
Proof. vm_refl. Qed.
Lemma D_84e1c : decode_any W_84e1c = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e20 : bv 32 := 0x000a1463.
Lemma F_84e20 : fetch_word Ubsan.M.loaded_segments (0x84e20 : word) = Some W_84e20.
Proof. vm_refl. Qed.
Lemma D_84e20 : decode_any W_84e20 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e24 : bv 32 := 0xed0fd06f.
Lemma F_84e24 : fetch_word Ubsan.M.loaded_segments (0x84e24 : word) = Some W_84e24.
Proof. vm_refl. Qed.
Lemma D_84e24 : decode_any W_84e24 = Some (Jal 0 2086608, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e28 : bv 32 := 0x015a3a33.
Lemma F_84e28 : fetch_word Ubsan.M.loaded_segments (0x84e28 : word) = Some W_84e28.
Proof. vm_refl. Qed.
Lemma D_84e28 : decode_any W_84e28 = Some (Op ALU_SLTU 20 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e2c : bv 32 := 0x07813903.
Lemma F_84e2c : fetch_word Ubsan.M.loaded_segments (0x84e2c : word) = Some W_84e2c.
Proof. vm_refl. Qed.
Lemma D_84e2c : decode_any W_84e2c = Some (Load SZ8 true 18 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e30 : bv 32 := 0x012a4a33.
Lemma F_84e30 : fetch_word Ubsan.M.loaded_segments (0x84e30 : word) = Some W_84e30.
Proof. vm_refl. Qed.
Lemma D_84e30 : decode_any W_84e30 = Some (Op ALU_XOR 20 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e34 : bv 32 := 0x001a4a13.
Lemma F_84e34 : fetch_word Ubsan.M.loaded_segments (0x84e34 : word) = Some W_84e34.
Proof. vm_refl. Qed.
Lemma D_84e34 : decode_any W_84e34 = Some (OpImm ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e38 : bv 32 := 0x000a1463.
Lemma F_84e38 : fetch_word Ubsan.M.loaded_segments (0x84e38 : word) = Some W_84e38.
Proof. vm_refl. Qed.
Lemma D_84e38 : decode_any W_84e38 = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e3c : bv 32 := 0xeb8fd06f.
Lemma F_84e3c : fetch_word Ubsan.M.loaded_segments (0x84e3c : word) = Some W_84e3c.
Proof. vm_refl. Qed.
Lemma D_84e3c : decode_any W_84e3c = Some (Jal 0 2086584, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e40 : bv 32 := 0x0014849b.
Lemma F_84e40 : fetch_word Ubsan.M.loaded_segments (0x84e40 : word) = Some W_84e40.
Proof. vm_refl. Qed.
Lemma D_84e40 : decode_any W_84e40 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e44 : bv 32 := 0x006585b3.
Lemma F_84e44 : fetch_word Ubsan.M.loaded_segments (0x84e44 : word) = Some W_84e44.
Proof. vm_refl. Qed.
Lemma D_84e44 : decode_any W_84e44 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e48 : bv 32 := 0x00f50533.
Lemma F_84e48 : fetch_word Ubsan.M.loaded_segments (0x84e48 : word) = Some W_84e48.
Proof. vm_refl. Qed.
Lemma D_84e48 : decode_any W_84e48 = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e4c : bv 32 := 0x000b0a13.
Lemma F_84e4c : fetch_word Ubsan.M.loaded_segments (0x84e4c : word) = Some W_84e4c.
Proof. vm_refl. Qed.
Lemma D_84e4c : decode_any W_84e4c = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e50 : bv 32 := 0xf2049ce3.
Lemma F_84e50 : fetch_word Ubsan.M.loaded_segments (0x84e50 : word) = Some W_84e50.
Proof. vm_refl. Qed.
Lemma D_84e50 : decode_any W_84e50 = Some (Branch BC_NE 9 0 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e54 : bv 32 := 0x7640206f.
Lemma F_84e54 : fetch_word Ubsan.M.loaded_segments (0x84e54 : word) = Some W_84e54.
Proof. vm_refl. Qed.
Lemma D_84e54 : decode_any W_84e54 = Some (Jal 0 10084, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e58 : bv 32 := 0x18008263.
Lemma F_84e58 : fetch_word Ubsan.M.loaded_segments (0x84e58 : word) = Some W_84e58.
Proof. vm_refl. Qed.
Lemma D_84e58 : decode_any W_84e58 = Some (Branch BC_EQ 1 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e5c : bv 32 := 0x00000593.
Lemma F_84e5c : fetch_word Ubsan.M.loaded_segments (0x84e5c : word) = Some W_84e5c.
Proof. vm_refl. Qed.
Lemma D_84e5c : decode_any W_84e5c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e60 : bv 32 := 0xffffc613.
Lemma F_84e60 : fetch_word Ubsan.M.loaded_segments (0x84e60 : word) = Some W_84e60.
Proof. vm_refl. Qed.
Lemma D_84e60 : decode_any W_84e60 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e64 : bv 32 := 0x00c13023.
Lemma F_84e64 : fetch_word Ubsan.M.loaded_segments (0x84e64 : word) = Some W_84e64.
Proof. vm_refl. Qed.
Lemma D_84e64 : decode_any W_84e64 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e68 : bv 32 := 0xfffdc293.
Lemma F_84e68 : fetch_word Ubsan.M.loaded_segments (0x84e68 : word) = Some W_84e68.
Proof. vm_refl. Qed.
Lemma D_84e68 : decode_any W_84e68 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e6c : bv 32 := 0x00271393.
Lemma F_84e6c : fetch_word Ubsan.M.loaded_segments (0x84e6c : word) = Some W_84e6c.
Proof. vm_refl. Qed.
Lemma D_84e6c : decode_any W_84e6c = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e70 : bv 32 := 0x05813683.
Lemma F_84e70 : fetch_word Ubsan.M.loaded_segments (0x84e70 : word) = Some W_84e70.
Proof. vm_refl. Qed.
Lemma D_84e70 : decode_any W_84e70 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e74 : bv 32 := 0x00269693.
Lemma F_84e74 : fetch_word Ubsan.M.loaded_segments (0x84e74 : word) = Some W_84e74.
Proof. vm_refl. Qed.
Lemma D_84e74 : decode_any W_84e74 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e78 : bv 32 := 0x003cfb93.
Lemma F_84e78 : fetch_word Ubsan.M.loaded_segments (0x84e78 : word) = Some W_84e78.
Proof. vm_refl. Qed.
Lemma D_84e78 : decode_any W_84e78 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e7c : bv 32 := 0x0037f613.
Lemma F_84e7c : fetch_word Ubsan.M.loaded_segments (0x84e7c : word) = Some W_84e7c.
Proof. vm_refl. Qed.
Lemma D_84e7c : decode_any W_84e7c = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e80 : bv 32 := 0x05013483.
Lemma F_84e80 : fetch_word Ubsan.M.loaded_segments (0x84e80 : word) = Some W_84e80.
Proof. vm_refl. Qed.
Lemma D_84e80 : decode_any W_84e80 = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e84 : bv 32 := 0x02813803.
Lemma F_84e84 : fetch_word Ubsan.M.loaded_segments (0x84e84 : word) = Some W_84e84.
Proof. vm_refl. Qed.
Lemma D_84e84 : decode_any W_84e84 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e88 : bv 32 := 0x4098083b.
Lemma F_84e88 : fetch_word Ubsan.M.loaded_segments (0x84e88 : word) = Some W_84e88.
Proof. vm_refl. Qed.
Lemma D_84e88 : decode_any W_84e88 = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e8c : bv 32 := 0x03813883.
Lemma F_84e8c : fetch_word Ubsan.M.loaded_segments (0x84e8c : word) = Some W_84e8c.
Proof. vm_refl. Qed.
Lemma D_84e8c : decode_any W_84e8c = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e90 : bv 32 := 0x03013e03.
Lemma F_84e90 : fetch_word Ubsan.M.loaded_segments (0x84e90 : word) = Some W_84e90.
Proof. vm_refl. Qed.
Lemma D_84e90 : decode_any W_84e90 = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e94 : bv 32 := 0x011e08b3.
Lemma F_84e94 : fetch_word Ubsan.M.loaded_segments (0x84e94 : word) = Some W_84e94.
Proof. vm_refl. Qed.
Lemma D_84e94 : decode_any W_84e94 = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e98 : bv 32 := 0x04813a03.
Lemma F_84e98 : fetch_word Ubsan.M.loaded_segments (0x84e98 : word) = Some W_84e98.
Proof. vm_refl. Qed.
Lemma D_84e98 : decode_any W_84e98 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_84e9c : bv 32 := 0x43fa5e13.
Lemma F_84e9c : fetch_word Ubsan.M.loaded_segments (0x84e9c : word) = Some W_84e9c.
Proof. vm_refl. Qed.
Lemma D_84e9c : decode_any W_84e9c = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ea0 : bv 32 := 0x01013983.
Lemma F_84ea0 : fetch_word Ubsan.M.loaded_segments (0x84ea0 : word) = Some W_84ea0.
Proof. vm_refl. Qed.
Lemma D_84ea0 : decode_any W_84ea0 = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ea4 : bv 32 := 0x0019f993.
Lemma F_84ea4 : fetch_word Ubsan.M.loaded_segments (0x84ea4 : word) = Some W_84ea4.
Proof. vm_refl. Qed.
Lemma D_84ea4 : decode_any W_84ea4 = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ea8 : bv 32 := 0x001d7c13.
Lemma F_84ea8 : fetch_word Ubsan.M.loaded_segments (0x84ea8 : word) = Some W_84ea8.
Proof. vm_refl. Qed.
Lemma D_84ea8 : decode_any W_84ea8 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84eac : bv 32 := 0x01f00093.
Lemma F_84eac : fetch_word Ubsan.M.loaded_segments (0x84eac : word) = Some W_84eac.
Proof. vm_refl. Qed.
Lemma D_84eac : decode_any W_84eac = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84eb0 : bv 32 := 0x014e7e33.
Lemma F_84eb0 : fetch_word Ubsan.M.loaded_segments (0x84eb0 : word) = Some W_84eb0.
Proof. vm_refl. Qed.
Lemma D_84eb0 : decode_any W_84eb0 = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_84eb4 : bv 32 := 0x409888bb.
Lemma F_84eb4 : fetch_word Ubsan.M.loaded_segments (0x84eb4 : word) = Some W_84eb4.
Proof. vm_refl. Qed.
Lemma D_84eb4 : decode_any W_84eb4 = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_84eb8 : bv 32 := 0x00d78a33.
Lemma F_84eb8 : fetch_word Ubsan.M.loaded_segments (0x84eb8 : word) = Some W_84eb8.
Proof. vm_refl. Qed.
Lemma D_84eb8 : decode_any W_84eb8 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ebc : bv 32 := 0x00163b13.
Lemma F_84ebc : fetch_word Ubsan.M.loaded_segments (0x84ebc : word) = Some W_84ebc.
Proof. vm_refl. Qed.
Lemma D_84ebc : decode_any W_84ebc = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ec0 : bv 32 := 0x04013603.
Lemma F_84ec0 : fetch_word Ubsan.M.loaded_segments (0x84ec0 : word) = Some W_84ec0.
Proof. vm_refl. Qed.
Lemma D_84ec0 : decode_any W_84ec0 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ec4 : bv 32 := 0x40c8863b.
Lemma F_84ec4 : fetch_word Ubsan.M.loaded_segments (0x84ec4 : word) = Some W_84ec4.
Proof. vm_refl. Qed.
Lemma D_84ec4 : decode_any W_84ec4 = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ec8 : bv 32 := 0x01c6063b.
Lemma F_84ec8 : fetch_word Ubsan.M.loaded_segments (0x84ec8 : word) = Some W_84ec8.
Proof. vm_refl. Qed.
Lemma D_84ec8 : decode_any W_84ec8 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ecc : bv 32 := 0x43f65893.
Lemma F_84ecc : fetch_word Ubsan.M.loaded_segments (0x84ecc : word) = Some W_84ecc.
Proof. vm_refl. Qed.
Lemma D_84ecc : decode_any W_84ecc = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ed0 : bv 32 := 0x00c8f633.
Lemma F_84ed0 : fetch_word Ubsan.M.loaded_segments (0x84ed0 : word) = Some W_84ed0.
Proof. vm_refl. Qed.
Lemma D_84ed0 : decode_any W_84ed0 = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ed4 : bv 32 := 0x40c80e3b.
Lemma F_84ed4 : fetch_word Ubsan.M.loaded_segments (0x84ed4 : word) = Some W_84ed4.
Proof. vm_refl. Qed.
Lemma D_84ed4 : decode_any W_84ed4 = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ed8 : bv 32 := 0x00072493.
Lemma F_84ed8 : fetch_word Ubsan.M.loaded_segments (0x84ed8 : word) = Some W_84ed8.
Proof. vm_refl. Qed.
Lemma D_84ed8 : decode_any W_84ed8 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84edc : bv 32 := 0x000c8813.
Lemma F_84edc : fetch_word Ubsan.M.loaded_segments (0x84edc : word) = Some W_84edc.
Proof. vm_refl. Qed.
Lemma D_84edc : decode_any W_84edc = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ee0 : bv 32 := 0x00b78d33.
Lemma F_84ee0 : fetch_word Ubsan.M.loaded_segments (0x84ee0 : word) = Some W_84ee0.
Proof. vm_refl. Qed.
Lemma D_84ee0 : decode_any W_84ee0 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ee4 : bv 32 := 0x01a03633.
Lemma F_84ee4 : fetch_word Ubsan.M.loaded_segments (0x84ee4 : word) = Some W_84ee4.
Proof. vm_refl. Qed.
Lemma D_84ee4 : decode_any W_84ee4 = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ee8 : bv 32 := 0x00cb7633.
Lemma F_84ee8 : fetch_word Ubsan.M.loaded_segments (0x84ee8 : word) = Some W_84ee8.
Proof. vm_refl. Qed.
Lemma D_84ee8 : decode_any W_84ee8 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84eec : bv 32 := 0x04098a63.
Lemma F_84eec : fetch_word Ubsan.M.loaded_segments (0x84eec : word) = Some W_84eec.
Proof. vm_refl. Qed.
Lemma D_84eec : decode_any W_84eec = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ef0 : bv 32 := 0x00061463.
Lemma F_84ef0 : fetch_word Ubsan.M.loaded_segments (0x84ef0 : word) = Some W_84ef0.
Proof. vm_refl. Qed.
Lemma D_84ef0 : decode_any W_84ef0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ef4 : bv 32 := 0xe00fd06f.
Lemma F_84ef4 : fetch_word Ubsan.M.loaded_segments (0x84ef4 : word) = Some W_84ef4.
Proof. vm_refl. Qed.
Lemma D_84ef4 : decode_any W_84ef4 = Some (Jal 0 2086400, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ef8 : bv 32 := 0x02000613.
Lemma F_84ef8 : fetch_word Ubsan.M.loaded_segments (0x84ef8 : word) = Some W_84ef8.
Proof. vm_refl. Qed.
Lemma D_84ef8 : decode_any W_84ef8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84efc : bv 32 := 0x00cf1463.
Lemma F_84efc : fetch_word Ubsan.M.loaded_segments (0x84efc : word) = Some W_84efc.
Proof. vm_refl. Qed.
Lemma D_84efc : decode_any W_84efc = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f00 : bv 32 := 0xdf4fd06f.
Lemma F_84f00 : fetch_word Ubsan.M.loaded_segments (0x84f00 : word) = Some W_84f00.
Proof. vm_refl. Qed.
Lemma D_84f00 : decode_any W_84f00 = Some (Jal 0 2086388, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f04 : bv 32 := 0x000d2603.
Lemma F_84f04 : fetch_word Ubsan.M.loaded_segments (0x84f04 : word) = Some W_84f04.
Proof. vm_refl. Qed.
Lemma D_84f04 : decode_any W_84f04 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f08 : bv 32 := 0x01d61abb.
Lemma F_84f08 : fetch_word Ubsan.M.loaded_segments (0x84f08 : word) = Some W_84f08.
Proof. vm_refl. Qed.
Lemma D_84f08 : decode_any W_84f08 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f0c : bv 32 := 0x040c1663.
Lemma F_84f0c : fetch_word Ubsan.M.loaded_segments (0x84f0c : word) = Some W_84f0c.
Proof. vm_refl. Qed.
Lemma D_84f0c : decode_any W_84f0c = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f10 : bv 32 := 0xffb00613.
Lemma F_84f10 : fetch_word Ubsan.M.loaded_segments (0x84f10 : word) = Some W_84f10.
Proof. vm_refl. Qed.
Lemma D_84f10 : decode_any W_84f10 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f14 : bv 32 := 0x01a67463.
Lemma F_84f14 : fetch_word Ubsan.M.loaded_segments (0x84f14 : word) = Some W_84f14.
Proof. vm_refl. Qed.
Lemma D_84f14 : decode_any W_84f14 = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f18 : bv 32 := 0xddcfd06f.
Lemma F_84f18 : fetch_word Ubsan.M.loaded_segments (0x84f18 : word) = Some W_84f18.
Proof. vm_refl. Qed.
Lemma D_84f18 : decode_any W_84f18 = Some (Jal 0 2086364, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f1c : bv 32 := 0x0080f463.
Lemma F_84f1c : fetch_word Ubsan.M.loaded_segments (0x84f1c : word) = Some W_84f1c.
Proof. vm_refl. Qed.
Lemma D_84f1c : decode_any W_84f1c = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f20 : bv 32 := 0xdd4fd06f.
Lemma F_84f20 : fetch_word Ubsan.M.loaded_segments (0x84f20 : word) = Some W_84f20.
Proof. vm_refl. Qed.
Lemma D_84f20 : decode_any W_84f20 = Some (Jal 0 2086356, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f24 : bv 32 := 0x004d2603.
Lemma F_84f24 : fetch_word Ubsan.M.loaded_segments (0x84f24 : word) = Some W_84f24.
Proof. vm_refl. Qed.
Lemma D_84f24 : decode_any W_84f24 = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f28 : bv 32 := 0x00013883.
Lemma F_84f28 : fetch_word Ubsan.M.loaded_segments (0x84f28 : word) = Some W_84f28.
Proof. vm_refl. Qed.
Lemma D_84f28 : decode_any W_84f28 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f2c : bv 32 := 0x011af8b3.
Lemma F_84f2c : fetch_word Ubsan.M.loaded_segments (0x84f2c : word) = Some W_84f2c.
Proof. vm_refl. Qed.
Lemma D_84f2c : decode_any W_84f2c = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f30 : bv 32 := 0x0086563b.
Lemma F_84f30 : fetch_word Ubsan.M.loaded_segments (0x84f30 : word) = Some W_84f30.
Proof. vm_refl. Qed.
Lemma D_84f30 : decode_any W_84f30 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f34 : bv 32 := 0x01f67633.
Lemma F_84f34 : fetch_word Ubsan.M.loaded_segments (0x84f34 : word) = Some W_84f34.
Proof. vm_refl. Qed.
Lemma D_84f34 : decode_any W_84f34 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f38 : bv 32 := 0x01166ab3.
Lemma F_84f38 : fetch_word Ubsan.M.loaded_segments (0x84f38 : word) = Some W_84f38.
Proof. vm_refl. Qed.
Lemma D_84f38 : decode_any W_84f38 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f3c : bv 32 := 0x01c0006f.
Lemma F_84f3c : fetch_word Ubsan.M.loaded_segments (0x84f3c : word) = Some W_84f3c.
Proof. vm_refl. Qed.
Lemma D_84f3c : decode_any W_84f3c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f40 : bv 32 := 0x00061463.
Lemma F_84f40 : fetch_word Ubsan.M.loaded_segments (0x84f40 : word) = Some W_84f40.
Proof. vm_refl. Qed.
Lemma D_84f40 : decode_any W_84f40 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f44 : bv 32 := 0xdb0fd06f.
Lemma F_84f44 : fetch_word Ubsan.M.loaded_segments (0x84f44 : word) = Some W_84f44.
Proof. vm_refl. Qed.
Lemma D_84f44 : decode_any W_84f44 = Some (Jal 0 2086320, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f48 : bv 32 := 0x0080f463.
Lemma F_84f48 : fetch_word Ubsan.M.loaded_segments (0x84f48 : word) = Some W_84f48.
Proof. vm_refl. Qed.
Lemma D_84f48 : decode_any W_84f48 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f4c : bv 32 := 0xda8fd06f.
Lemma F_84f4c : fetch_word Ubsan.M.loaded_segments (0x84f4c : word) = Some W_84f4c.
Proof. vm_refl. Qed.
Lemma D_84f4c : decode_any W_84f4c = Some (Jal 0 2086312, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f50 : bv 32 := 0x000d2603.
Lemma F_84f50 : fetch_word Ubsan.M.loaded_segments (0x84f50 : word) = Some W_84f50.
Proof. vm_refl. Qed.
Lemma D_84f50 : decode_any W_84f50 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f54 : bv 32 := 0x00865abb.
Lemma F_84f54 : fetch_word Ubsan.M.loaded_segments (0x84f54 : word) = Some W_84f54.
Proof. vm_refl. Qed.
Lemma D_84f54 : decode_any W_84f54 = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f58 : bv 32 := 0x000b8463.
Lemma F_84f58 : fetch_word Ubsan.M.loaded_segments (0x84f58 : word) = Some W_84f58.
Proof. vm_refl. Qed.
Lemma D_84f58 : decode_any W_84f58 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f5c : bv 32 := 0xd98fd06f.
Lemma F_84f5c : fetch_word Ubsan.M.loaded_segments (0x84f5c : word) = Some W_84f5c.
Proof. vm_refl. Qed.
Lemma D_84f5c : decode_any W_84f5c = Some (Jal 0 2086296, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f60 : bv 32 := 0x000c9463.
Lemma F_84f60 : fetch_word Ubsan.M.loaded_segments (0x84f60 : word) = Some W_84f60.
Proof. vm_refl. Qed.
Lemma D_84f60 : decode_any W_84f60 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f64 : bv 32 := 0xd90fd06f.
Lemma F_84f64 : fetch_word Ubsan.M.loaded_segments (0x84f64 : word) = Some W_84f64.
Proof. vm_refl. Qed.
Lemma D_84f64 : decode_any W_84f64 = Some (Jal 0 2086288, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f68 : bv 32 := 0x000ca603.
Lemma F_84f68 : fetch_word Ubsan.M.loaded_segments (0x84f68 : word) = Some W_84f68.
Proof. vm_refl. Qed.
Lemma D_84f68 : decode_any W_84f68 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f6c : bv 32 := 0x005678b3.
Lemma F_84f6c : fetch_word Ubsan.M.loaded_segments (0x84f6c : word) = Some W_84f6c.
Proof. vm_refl. Qed.
Lemma D_84f6c : decode_any W_84f6c = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f70 : bv 32 := 0x01567633.
Lemma F_84f70 : fetch_word Ubsan.M.loaded_segments (0x84f70 : word) = Some W_84f70.
Proof. vm_refl. Qed.
Lemma D_84f70 : decode_any W_84f70 = Some (Op ALU_AND 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f74 : bv 32 := 0xfff64613.
Lemma F_84f74 : fetch_word Ubsan.M.loaded_segments (0x84f74 : word) = Some W_84f74.
Proof. vm_refl. Qed.
Lemma D_84f74 : decode_any W_84f74 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f78 : bv 32 := 0x00cdf633.
Lemma F_84f78 : fetch_word Ubsan.M.loaded_segments (0x84f78 : word) = Some W_84f78.
Proof. vm_refl. Qed.
Lemma D_84f78 : decode_any W_84f78 = Some (Op ALU_AND 12 27 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f7c : bv 32 := 0x01166633.
Lemma F_84f7c : fetch_word Ubsan.M.loaded_segments (0x84f7c : word) = Some W_84f7c.
Proof. vm_refl. Qed.
Lemma D_84f7c : decode_any W_84f7c = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f80 : bv 32 := 0x01038ab3.
Lemma F_84f80 : fetch_word Ubsan.M.loaded_segments (0x84f80 : word) = Some W_84f80.
Proof. vm_refl. Qed.
Lemma D_84f80 : decode_any W_84f80 = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f84 : bv 32 := 0x00cca023.
Lemma F_84f84 : fetch_word Ubsan.M.loaded_segments (0x84f84 : word) = Some W_84f84.
Proof. vm_refl. Qed.
Lemma D_84f84 : decode_any W_84f84 = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f88 : bv 32 := 0x000a9463.
Lemma F_84f88 : fetch_word Ubsan.M.loaded_segments (0x84f88 : word) = Some W_84f88.
Proof. vm_refl. Qed.
Lemma D_84f88 : decode_any W_84f88 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f8c : bv 32 := 0xd68fd06f.
Lemma F_84f8c : fetch_word Ubsan.M.loaded_segments (0x84f8c : word) = Some W_84f8c.
Proof. vm_refl. Qed.
Lemma D_84f8c : decode_any W_84f8c = Some (Jal 0 2086248, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f90 : bv 32 := 0x010ab633.
Lemma F_84f90 : fetch_word Ubsan.M.loaded_segments (0x84f90 : word) = Some W_84f90.
Proof. vm_refl. Qed.
Lemma D_84f90 : decode_any W_84f90 = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f94 : bv 32 := 0x00964633.
Lemma F_84f94 : fetch_word Ubsan.M.loaded_segments (0x84f94 : word) = Some W_84f94.
Proof. vm_refl. Qed.
Lemma D_84f94 : decode_any W_84f94 = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f98 : bv 32 := 0x00164613.
Lemma F_84f98 : fetch_word Ubsan.M.loaded_segments (0x84f98 : word) = Some W_84f98.
Proof. vm_refl. Qed.
Lemma D_84f98 : decode_any W_84f98 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84f9c : bv 32 := 0x00061463.
Lemma F_84f9c : fetch_word Ubsan.M.loaded_segments (0x84f9c : word) = Some W_84f9c.
Proof. vm_refl. Qed.
Lemma D_84f9c : decode_any W_84f9c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fa0 : bv 32 := 0xd54fd06f.
Lemma F_84fa0 : fetch_word Ubsan.M.loaded_segments (0x84fa0 : word) = Some W_84fa0.
Proof. vm_refl. Qed.
Lemma D_84fa0 : decode_any W_84fa0 = Some (Jal 0 2086228, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fa4 : bv 32 := 0x00ba0633.
Lemma F_84fa4 : fetch_word Ubsan.M.loaded_segments (0x84fa4 : word) = Some W_84fa4.
Proof. vm_refl. Qed.
Lemma D_84fa4 : decode_any W_84fa4 = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fa8 : bv 32 := 0x00061463.
Lemma F_84fa8 : fetch_word Ubsan.M.loaded_segments (0x84fa8 : word) = Some W_84fa8.
Proof. vm_refl. Qed.
Lemma D_84fa8 : decode_any W_84fa8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fac : bv 32 := 0xd48fd06f.
Lemma F_84fac : fetch_word Ubsan.M.loaded_segments (0x84fac : word) = Some W_84fac.
Proof. vm_refl. Qed.
Lemma D_84fac : decode_any W_84fac = Some (Jal 0 2086216, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fb0 : bv 32 := 0x01a63633.
Lemma F_84fb0 : fetch_word Ubsan.M.loaded_segments (0x84fb0 : word) = Some W_84fb0.
Proof. vm_refl. Qed.
Lemma D_84fb0 : decode_any W_84fb0 = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fb4 : bv 32 := 0x07813803.
Lemma F_84fb4 : fetch_word Ubsan.M.loaded_segments (0x84fb4 : word) = Some W_84fb4.
Proof. vm_refl. Qed.
Lemma D_84fb4 : decode_any W_84fb4 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fb8 : bv 32 := 0x01064633.
Lemma F_84fb8 : fetch_word Ubsan.M.loaded_segments (0x84fb8 : word) = Some W_84fb8.
Proof. vm_refl. Qed.
Lemma D_84fb8 : decode_any W_84fb8 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fbc : bv 32 := 0x00164613.
Lemma F_84fbc : fetch_word Ubsan.M.loaded_segments (0x84fbc : word) = Some W_84fbc.
Proof. vm_refl. Qed.
Lemma D_84fbc : decode_any W_84fbc = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fc0 : bv 32 := 0x00061463.
Lemma F_84fc0 : fetch_word Ubsan.M.loaded_segments (0x84fc0 : word) = Some W_84fc0.
Proof. vm_refl. Qed.
Lemma D_84fc0 : decode_any W_84fc0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fc4 : bv 32 := 0xd30fd06f.
Lemma F_84fc4 : fetch_word Ubsan.M.loaded_segments (0x84fc4 : word) = Some W_84fc4.
Proof. vm_refl. Qed.
Lemma D_84fc4 : decode_any W_84fc4 = Some (Jal 0 2086192, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fc8 : bv 32 := 0x001e0e1b.
Lemma F_84fc8 : fetch_word Ubsan.M.loaded_segments (0x84fc8 : word) = Some W_84fc8.
Proof. vm_refl. Qed.
Lemma D_84fc8 : decode_any W_84fc8 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fcc : bv 32 := 0x00d585b3.
Lemma F_84fcc : fetch_word Ubsan.M.loaded_segments (0x84fcc : word) = Some W_84fcc.
Proof. vm_refl. Qed.
Lemma D_84fcc : decode_any W_84fcc = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fd0 : bv 32 := 0x007c8cb3.
Lemma F_84fd0 : fetch_word Ubsan.M.loaded_segments (0x84fd0 : word) = Some W_84fd0.
Proof. vm_refl. Qed.
Lemma D_84fd0 : decode_any W_84fd0 = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fd4 : bv 32 := 0x000a8813.
Lemma F_84fd4 : fetch_word Ubsan.M.loaded_segments (0x84fd4 : word) = Some W_84fd4.
Proof. vm_refl. Qed.
Lemma D_84fd4 : decode_any W_84fd4 = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fd8 : bv 32 := 0xf00e14e3.
Lemma F_84fd8 : fetch_word Ubsan.M.loaded_segments (0x84fd8 : word) = Some W_84fd8.
Proof. vm_refl. Qed.
Lemma D_84fd8 : decode_any W_84fd8 = Some (Branch BC_NE 28 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fdc : bv 32 := 0x02013583.
Lemma F_84fdc : fetch_word Ubsan.M.loaded_segments (0x84fdc : word) = Some W_84fdc.
Proof. vm_refl. Qed.
Lemma D_84fdc : decode_any W_84fdc = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fe0 : bv 32 := 0x16059e63.
Lemma F_84fe0 : fetch_word Ubsan.M.loaded_segments (0x84fe0 : word) = Some W_84fe0.
Proof. vm_refl. Qed.
Lemma D_84fe0 : decode_any W_84fe0 = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fe4 : bv 32 := 0xffffc693.
Lemma F_84fe4 : fetch_word Ubsan.M.loaded_segments (0x84fe4 : word) = Some W_84fe4.
Proof. vm_refl. Qed.
Lemma D_84fe4 : decode_any W_84fe4 = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fe8 : bv 32 := 0x00271293.
Lemma F_84fe8 : fetch_word Ubsan.M.loaded_segments (0x84fe8 : word) = Some W_84fe8.
Proof. vm_refl. Qed.
Lemma D_84fe8 : decode_any W_84fe8 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84fec : bv 32 := 0x05813383.
Lemma F_84fec : fetch_word Ubsan.M.loaded_segments (0x84fec : word) = Some W_84fec.
Proof. vm_refl. Qed.
Lemma D_84fec : decode_any W_84fec = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ff0 : bv 32 := 0x00239393.
Lemma F_84ff0 : fetch_word Ubsan.M.loaded_segments (0x84ff0 : word) = Some W_84ff0.
Proof. vm_refl. Qed.
Lemma D_84ff0 : decode_any W_84ff0 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ff4 : bv 32 := 0x00337613.
Lemma F_84ff4 : fetch_word Ubsan.M.loaded_segments (0x84ff4 : word) = Some W_84ff4.
Proof. vm_refl. Qed.
Lemma D_84ff4 : decode_any W_84ff4 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ff8 : bv 32 := 0x00397793.
Lemma F_84ff8 : fetch_word Ubsan.M.loaded_segments (0x84ff8 : word) = Some W_84ff8.
Proof. vm_refl. Qed.
Lemma D_84ff8 : decode_any W_84ff8 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ffc : bv 32 := 0x07013a03.
Lemma F_84ffc : fetch_word Ubsan.M.loaded_segments (0x84ffc : word) = Some W_84ffc.
Proof. vm_refl. Qed.
Lemma D_84ffc : decode_any W_84ffc = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.
