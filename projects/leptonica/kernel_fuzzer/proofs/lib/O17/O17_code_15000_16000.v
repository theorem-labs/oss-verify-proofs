(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.H Require GcFlushS17.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_15000 : bv 32 := 0x03613823.
Lemma F_15000 : fetch_word Plain.M.loaded_segments (0x150fc : word) = Some W_15000.
Proof. vm_refl. Qed.
Lemma D_15000 : decode_any W_15000 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15004 : bv 32 := 0x03713423.
Lemma F_15004 : fetch_word Plain.M.loaded_segments (0x15100 : word) = Some W_15004.
Proof. vm_refl. Qed.
Lemma D_15004 : decode_any W_15004 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15008 : bv 32 := 0x03813023.
Lemma F_15008 : fetch_word Plain.M.loaded_segments (0x15104 : word) = Some W_15008.
Proof. vm_refl. Qed.
Lemma D_15008 : decode_any W_15008 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1500c : bv 32 := 0x01913c23.
Lemma F_1500c : fetch_word Plain.M.loaded_segments (0x15108 : word) = Some W_1500c.
Proof. vm_refl. Qed.
Lemma D_1500c : decode_any W_1500c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15010 : bv 32 := 0x04050463.
Lemma F_15010 : fetch_word Plain.M.loaded_segments (0x1510c : word) = Some W_15010.
Proof. vm_refl. Qed.
Lemma D_15010 : decode_any W_15010 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15014 : bv 32 := 0x80000637.
Lemma F_15014 : fetch_word Plain.M.loaded_segments (0x15110 : word) = Some W_15014.
Proof. vm_refl. Qed.
Lemma D_15014 : decode_any W_15014 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15018 : bv 32 := 0x00c586b3.
Lemma F_15018 : fetch_word Plain.M.loaded_segments (0x15114 : word) = Some W_15018.
Proof. vm_refl. Qed.
Lemma D_15018 : decode_any W_15018 = Some (Op ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1501c : bv 32 := 0x01b6061b.
Lemma F_1501c : fetch_word Plain.M.loaded_segments (0x15118 : word) = Some W_1501c.
Proof. vm_refl. Qed.
Lemma D_1501c : decode_any W_1501c = Some (OpImm32 12 12 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15020 : bv 32 := 0x06d66063.
Lemma F_15020 : fetch_word Plain.M.loaded_segments (0x1511c : word) = Some W_15020.
Proof. vm_refl. Qed.
Lemma D_15020 : decode_any W_15020 = Some (Branch BC_LTU 12 13 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15024 : bv 32 := 0x0000a517.
Lemma F_15024 : fetch_word Plain.M.loaded_segments (0x15120 : word) = Some W_15024.
Proof. vm_refl. Qed.
Lemma D_15024 : decode_any W_15024 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15028 : bv 32 := 0x03053503.
Lemma F_15028 : fetch_word Plain.M.loaded_segments (0x15124 : word) = Some W_15028.
Proof. vm_refl. Qed.
Lemma D_15028 : decode_any W_15028 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1502c : bv 32 := 0x00052503.
Lemma F_1502c : fetch_word Plain.M.loaded_segments (0x15128 : word) = Some W_1502c.
Proof. vm_refl. Qed.
Lemma D_1502c : decode_any W_1502c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15030 : bv 32 := 0x00500613.
Lemma F_15030 : fetch_word Plain.M.loaded_segments (0x1512c : word) = Some W_15030.
Proof. vm_refl. Qed.
Lemma D_15030 : decode_any W_15030 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15034 : bv 32 := 0x3ca64063.
Lemma F_15034 : fetch_word Plain.M.loaded_segments (0x15130 : word) = Some W_15034.
Proof. vm_refl. Qed.
Lemma D_15034 : decode_any W_15034 = Some (Branch BC_LT 12 10 960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15038 : bv 32 := 0xffffb517.
Lemma F_15038 : fetch_word Plain.M.loaded_segments (0x15134 : word) = Some W_15038.
Proof. vm_refl. Qed.
Lemma D_15038 : decode_any W_15038 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1503c : bv 32 := 0xffffb617.
Lemma F_1503c : fetch_word Plain.M.loaded_segments (0x15138 : word) = Some W_1503c.
Proof. vm_refl. Qed.
Lemma D_1503c : decode_any W_1503c = Some (Auipc 12 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15040 : bv 32 := 0x68a50513.
Lemma F_15040 : fetch_word Plain.M.loaded_segments (0x1513c : word) = Some W_15040.
Proof. vm_refl. Qed.
Lemma D_15040 : decode_any W_15040 = Some (OpImm ALU_ADD 10 10 1674, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15044 : bv 32 := 0x55760693.
Lemma F_15044 : fetch_word Plain.M.loaded_segments (0x15140 : word) = Some W_15044.
Proof. vm_refl. Qed.
Lemma D_15044 : decode_any W_15044 = Some (OpImm ALU_ADD 13 12 1367, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15048 : bv 32 := 0x00058613.
Lemma F_15048 : fetch_word Plain.M.loaded_segments (0x15144 : word) = Some W_15048.
Proof. vm_refl. Qed.
Lemma D_15048 : decode_any W_15048 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1504c : bv 32 := 0x00068593.
Lemma F_1504c : fetch_word Plain.M.loaded_segments (0x15148 : word) = Some W_1504c.
Proof. vm_refl. Qed.
Lemma D_1504c : decode_any W_1504c = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15050 : bv 32 := 0x8b9fe0ef.
Lemma F_15050 : fetch_word Plain.M.loaded_segments (0x1514c : word) = Some W_15050.
Proof. vm_refl. Qed.
Lemma D_15050 : decode_any W_15050 = Some (Jal 1 2091192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15054 : bv 32 := 0x3a00006f.
Lemma F_15054 : fetch_word Plain.M.loaded_segments (0x15150 : word) = Some W_15054.
Proof. vm_refl. Qed.
Lemma D_15054 : decode_any W_15054 = Some (Jal 0 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15080 : bv 32 := 0x00054603.
Lemma F_15080 : fetch_word Plain.M.loaded_segments (0x1517c : word) = Some W_15080.
Proof. vm_refl. Qed.
Lemma D_15080 : decode_any W_15080 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15084 : bv 32 := 0x07300693.
Lemma F_15084 : fetch_word Plain.M.loaded_segments (0x15180 : word) = Some W_15084.
Proof. vm_refl. Qed.
Lemma D_15084 : decode_any W_15084 = Some (OpImm ALU_ADD 13 0 115, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15088 : bv 32 := 0x06d61263.
Lemma F_15088 : fetch_word Plain.M.loaded_segments (0x15184 : word) = Some W_15088.
Proof. vm_refl. Qed.
Lemma D_15088 : decode_any W_15088 = Some (Branch BC_NE 12 13 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1508c : bv 32 := 0x00154603.
Lemma F_1508c : fetch_word Plain.M.loaded_segments (0x15188 : word) = Some W_1508c.
Proof. vm_refl. Qed.
Lemma D_1508c : decode_any W_1508c = Some (Load SZ1 false 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15090 : bv 32 := 0x07000693.
Lemma F_15090 : fetch_word Plain.M.loaded_segments (0x1518c : word) = Some W_15090.
Proof. vm_refl. Qed.
Lemma D_15090 : decode_any W_15090 = Some (OpImm ALU_ADD 13 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15094 : bv 32 := 0x04d61c63.
Lemma F_15094 : fetch_word Plain.M.loaded_segments (0x15190 : word) = Some W_15094.
Proof. vm_refl. Qed.
Lemma D_15094 : decode_any W_15094 = Some (Branch BC_NE 12 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15098 : bv 32 := 0x00254603.
Lemma F_15098 : fetch_word Plain.M.loaded_segments (0x15194 : word) = Some W_15098.
Proof. vm_refl. Qed.
Lemma D_15098 : decode_any W_15098 = Some (Load SZ1 false 12 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1509c : bv 32 := 0x06900693.
Lemma F_1509c : fetch_word Plain.M.loaded_segments (0x15198 : word) = Some W_1509c.
Proof. vm_refl. Qed.
Lemma D_1509c : decode_any W_1509c = Some (OpImm ALU_ADD 13 0 105, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150a0 : bv 32 := 0x04d61663.
Lemma F_150a0 : fetch_word Plain.M.loaded_segments (0x1519c : word) = Some W_150a0.
Proof. vm_refl. Qed.
Lemma D_150a0 : decode_any W_150a0 = Some (Branch BC_NE 12 13 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150a4 : bv 32 := 0x00354603.
Lemma F_150a4 : fetch_word Plain.M.loaded_segments (0x151a0 : word) = Some W_150a4.
Proof. vm_refl. Qed.
Lemma D_150a4 : decode_any W_150a4 = Some (Load SZ1 false 12 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150a8 : bv 32 := 0x07800693.
Lemma F_150a8 : fetch_word Plain.M.loaded_segments (0x151a4 : word) = Some W_150a8.
Proof. vm_refl. Qed.
Lemma D_150a8 : decode_any W_150a8 = Some (OpImm ALU_ADD 13 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150ac : bv 32 := 0x04d61063.
Lemma F_150ac : fetch_word Plain.M.loaded_segments (0x151a8 : word) = Some W_150ac.
Proof. vm_refl. Qed.
Lemma D_150ac : decode_any W_150ac = Some (Branch BC_NE 12 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b0 : bv 32 := 0x00452483.
Lemma F_150b0 : fetch_word Plain.M.loaded_segments (0x151ac : word) = Some W_150b0.
Proof. vm_refl. Qed.
Lemma D_150b0 : decode_any W_150b0 = Some (Load SZ4 true 9 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b4 : bv 32 := 0xfff0c637.
Lemma F_150b4 : fetch_word Plain.M.loaded_segments (0x151b0 : word) = Some W_150b4.
Proof. vm_refl. Qed.
Lemma D_150b4 : decode_any W_150b4 = Some (Lui 12 1048332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150b8 : bv 32 := 0xdbf6061b.
Lemma F_150b8 : fetch_word Plain.M.loaded_segments (0x151b4 : word) = Some W_150b8.
Proof. vm_refl. Qed.
Lemma D_150b8 : decode_any W_150b8 = Some (OpImm32 12 12 3519, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150bc : bv 32 := 0x00c486bb.
Lemma F_150bc : fetch_word Plain.M.loaded_segments (0x151b8 : word) = Some W_150bc.
Proof. vm_refl. Qed.
Lemma D_150bc : decode_any W_150bc = Some (Op32 ALU_ADD 13 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c0 : bv 32 := 0x08d66463.
Lemma F_150c0 : fetch_word Plain.M.loaded_segments (0x151bc : word) = Some W_150c0.
Proof. vm_refl. Qed.
Lemma D_150c0 : decode_any W_150c0 = Some (Branch BC_LTU 12 13 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c4 : bv 32 := 0x0000a517.
Lemma F_150c4 : fetch_word Plain.M.loaded_segments (0x151c0 : word) = Some W_150c4.
Proof. vm_refl. Qed.
Lemma D_150c4 : decode_any W_150c4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c8 : bv 32 := 0xf9053503.
Lemma F_150c8 : fetch_word Plain.M.loaded_segments (0x151c4 : word) = Some W_150c8.
Proof. vm_refl. Qed.
Lemma D_150c8 : decode_any W_150c8 = Some (Load SZ8 true 10 10 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150cc : bv 32 := 0x00052503.
Lemma F_150cc : fetch_word Plain.M.loaded_segments (0x151c8 : word) = Some W_150cc.
Proof. vm_refl. Qed.
Lemma D_150cc : decode_any W_150cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d0 : bv 32 := 0x00500593.
Lemma F_150d0 : fetch_word Plain.M.loaded_segments (0x151cc : word) = Some W_150d0.
Proof. vm_refl. Qed.
Lemma D_150d0 : decode_any W_150d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d4 : bv 32 := 0x32a5c063.
Lemma F_150d4 : fetch_word Plain.M.loaded_segments (0x151d0 : word) = Some W_150d4.
Proof. vm_refl. Qed.
Lemma D_150d4 : decode_any W_150d4 = Some (Branch BC_LT 11 10 800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d8 : bv 32 := 0xffffc517.
Lemma F_150d8 : fetch_word Plain.M.loaded_segments (0x151d4 : word) = Some W_150d8.
Proof. vm_refl. Qed.
Lemma D_150d8 : decode_any W_150d8 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150dc : bv 32 := 0xffffb597.
Lemma F_150dc : fetch_word Plain.M.loaded_segments (0x151d8 : word) = Some W_150dc.
Proof. vm_refl. Qed.
Lemma D_150dc : decode_any W_150dc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150e0 : bv 32 := 0x85a50513.
Lemma F_150e0 : fetch_word Plain.M.loaded_segments (0x151dc : word) = Some W_150e0.
Proof. vm_refl. Qed.
Lemma D_150e0 : decode_any W_150e0 = Some (OpImm ALU_ADD 10 10 2138, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150e4 : bv 32 := 0x4b758593.
Lemma F_150e4 : fetch_word Plain.M.loaded_segments (0x151e0 : word) = Some W_150e4.
Proof. vm_refl. Qed.
Lemma D_150e4 : decode_any W_150e4 = Some (OpImm ALU_ADD 11 11 1207, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150e8 : bv 32 := 0x0280006f.
Lemma F_150e8 : fetch_word Plain.M.loaded_segments (0x151e4 : word) = Some W_150e8.
Proof. vm_refl. Qed.
Lemma D_150e8 : decode_any W_150e8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150ec : bv 32 := 0x0000a517.
Lemma F_150ec : fetch_word Plain.M.loaded_segments (0x151e8 : word) = Some W_150ec.
Proof. vm_refl. Qed.
Lemma D_150ec : decode_any W_150ec = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150f0 : bv 32 := 0xf6853503.
Lemma F_150f0 : fetch_word Plain.M.loaded_segments (0x151ec : word) = Some W_150f0.
Proof. vm_refl. Qed.
Lemma D_150f0 : decode_any W_150f0 = Some (Load SZ8 true 10 10 3944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150f4 : bv 32 := 0x00052503.
Lemma F_150f4 : fetch_word Plain.M.loaded_segments (0x151f0 : word) = Some W_150f4.
Proof. vm_refl. Qed.
Lemma D_150f4 : decode_any W_150f4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150f8 : bv 32 := 0x00500593.
Lemma F_150f8 : fetch_word Plain.M.loaded_segments (0x151f4 : word) = Some W_150f8.
Proof. vm_refl. Qed.
Lemma D_150f8 : decode_any W_150f8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150fc : bv 32 := 0x2ea5cc63.
Lemma F_150fc : fetch_word Plain.M.loaded_segments (0x151f8 : word) = Some W_150fc.
Proof. vm_refl. Qed.
Lemma D_150fc : decode_any W_150fc = Some (Branch BC_LT 11 10 760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15100 : bv 32 := 0xffffb517.
Lemma F_15100 : fetch_word Plain.M.loaded_segments (0x151fc : word) = Some W_15100.
Proof. vm_refl. Qed.
Lemma D_15100 : decode_any W_15100 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15104 : bv 32 := 0xffffb597.
Lemma F_15104 : fetch_word Plain.M.loaded_segments (0x15200 : word) = Some W_15104.
Proof. vm_refl. Qed.
Lemma D_15104 : decode_any W_15104 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15108 : bv 32 := 0x5e550513.
Lemma F_15108 : fetch_word Plain.M.loaded_segments (0x15204 : word) = Some W_15108.
Proof. vm_refl. Qed.
Lemma D_15108 : decode_any W_15108 = Some (OpImm ALU_ADD 10 10 1509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1510c : bv 32 := 0x48f58593.
Lemma F_1510c : fetch_word Plain.M.loaded_segments (0x15208 : word) = Some W_1510c.
Proof. vm_refl. Qed.
Lemma D_1510c : decode_any W_1510c = Some (OpImm ALU_ADD 11 11 1167, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15110 : bv 32 := 0x00000613.
Lemma F_15110 : fetch_word Plain.M.loaded_segments (0x1520c : word) = Some W_15110.
Proof. vm_refl. Qed.
Lemma D_15110 : decode_any W_15110 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15114 : bv 32 := 0x06813083.
Lemma F_15114 : fetch_word Plain.M.loaded_segments (0x15210 : word) = Some W_15114.
Proof. vm_refl. Qed.
Lemma D_15114 : decode_any W_15114 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15118 : bv 32 := 0x06013403.
Lemma F_15118 : fetch_word Plain.M.loaded_segments (0x15214 : word) = Some W_15118.
Proof. vm_refl. Qed.
Lemma D_15118 : decode_any W_15118 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1511c : bv 32 := 0x05813483.
Lemma F_1511c : fetch_word Plain.M.loaded_segments (0x15218 : word) = Some W_1511c.
Proof. vm_refl. Qed.
Lemma D_1511c : decode_any W_1511c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15120 : bv 32 := 0x05013903.
Lemma F_15120 : fetch_word Plain.M.loaded_segments (0x1521c : word) = Some W_15120.
Proof. vm_refl. Qed.
Lemma D_15120 : decode_any W_15120 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15124 : bv 32 := 0x04813983.
Lemma F_15124 : fetch_word Plain.M.loaded_segments (0x15220 : word) = Some W_15124.
Proof. vm_refl. Qed.
Lemma D_15124 : decode_any W_15124 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15128 : bv 32 := 0x04013a03.
Lemma F_15128 : fetch_word Plain.M.loaded_segments (0x15224 : word) = Some W_15128.
Proof. vm_refl. Qed.
Lemma D_15128 : decode_any W_15128 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1512c : bv 32 := 0x03813a83.
Lemma F_1512c : fetch_word Plain.M.loaded_segments (0x15228 : word) = Some W_1512c.
Proof. vm_refl. Qed.
Lemma D_1512c : decode_any W_1512c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15130 : bv 32 := 0x03013b03.
Lemma F_15130 : fetch_word Plain.M.loaded_segments (0x1522c : word) = Some W_15130.
Proof. vm_refl. Qed.
Lemma D_15130 : decode_any W_15130 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15134 : bv 32 := 0x02813b83.
Lemma F_15134 : fetch_word Plain.M.loaded_segments (0x15230 : word) = Some W_15134.
Proof. vm_refl. Qed.
Lemma D_15134 : decode_any W_15134 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15138 : bv 32 := 0x02013c03.
Lemma F_15138 : fetch_word Plain.M.loaded_segments (0x15234 : word) = Some W_15138.
Proof. vm_refl. Qed.
Lemma D_15138 : decode_any W_15138 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1513c : bv 32 := 0x01813c83.
Lemma F_1513c : fetch_word Plain.M.loaded_segments (0x15238 : word) = Some W_1513c.
Proof. vm_refl. Qed.
Lemma D_1513c : decode_any W_1513c = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15140 : bv 32 := 0x07010113.
Lemma F_15140 : fetch_word Plain.M.loaded_segments (0x1523c : word) = Some W_15140.
Proof. vm_refl. Qed.
Lemma D_15140 : decode_any W_15140 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15144 : bv 32 := 0x861fe06f.
Lemma F_15144 : fetch_word Plain.M.loaded_segments (0x15240 : word) = Some W_15144.
Proof. vm_refl. Qed.
Lemma D_15144 : decode_any W_15144 = Some (Jal 0 2091104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15148 : bv 32 := 0x00852903.
Lemma F_15148 : fetch_word Plain.M.loaded_segments (0x15244 : word) = Some W_15148.
Proof. vm_refl. Qed.
Lemma D_15148 : decode_any W_15148 = Some (Load SZ4 true 18 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1514c : bv 32 := 0x00c906bb.
Lemma F_1514c : fetch_word Plain.M.loaded_segments (0x15248 : word) = Some W_1514c.
Proof. vm_refl. Qed.
Lemma D_1514c : decode_any W_1514c = Some (Op32 ALU_ADD 13 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15150 : bv 32 := 0x02d66663.
Lemma F_15150 : fetch_word Plain.M.loaded_segments (0x1524c : word) = Some W_15150.
Proof. vm_refl. Qed.
Lemma D_15150 : decode_any W_15150 = Some (Branch BC_LTU 12 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15154 : bv 32 := 0x0000a517.
Lemma F_15154 : fetch_word Plain.M.loaded_segments (0x15250 : word) = Some W_15154.
Proof. vm_refl. Qed.
Lemma D_15154 : decode_any W_15154 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15158 : bv 32 := 0xf0053503.
Lemma F_15158 : fetch_word Plain.M.loaded_segments (0x15254 : word) = Some W_15158.
Proof. vm_refl. Qed.
Lemma D_15158 : decode_any W_15158 = Some (Load SZ8 true 10 10 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1515c : bv 32 := 0x00052503.
Lemma F_1515c : fetch_word Plain.M.loaded_segments (0x15258 : word) = Some W_1515c.
Proof. vm_refl. Qed.
Lemma D_1515c : decode_any W_1515c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15160 : bv 32 := 0x00500593.
Lemma F_15160 : fetch_word Plain.M.loaded_segments (0x1525c : word) = Some W_15160.
Proof. vm_refl. Qed.
Lemma D_15160 : decode_any W_15160 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15164 : bv 32 := 0x28a5c863.
Lemma F_15164 : fetch_word Plain.M.loaded_segments (0x15260 : word) = Some W_15164.
Proof. vm_refl. Qed.
Lemma D_15164 : decode_any W_15164 = Some (Branch BC_LT 11 10 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15168 : bv 32 := 0xffffb517.
Lemma F_15168 : fetch_word Plain.M.loaded_segments (0x15264 : word) = Some W_15168.
Proof. vm_refl. Qed.
Lemma D_15168 : decode_any W_15168 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1516c : bv 32 := 0xffffb597.
Lemma F_1516c : fetch_word Plain.M.loaded_segments (0x15268 : word) = Some W_1516c.
Proof. vm_refl. Qed.
Lemma D_1516c : decode_any W_1516c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15170 : bv 32 := 0x10d50513.
Lemma F_15170 : fetch_word Plain.M.loaded_segments (0x1526c : word) = Some W_15170.
Proof. vm_refl. Qed.
Lemma D_15170 : decode_any W_15170 = Some (OpImm ALU_ADD 10 10 269, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15174 : bv 32 := 0x42758593.
Lemma F_15174 : fetch_word Plain.M.loaded_segments (0x15270 : word) = Some W_15174.
Proof. vm_refl. Qed.
Lemma D_15174 : decode_any W_15174 = Some (OpImm ALU_ADD 11 11 1063, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15178 : bv 32 := 0xf99ff06f.
Lemma F_15178 : fetch_word Plain.M.loaded_segments (0x15274 : word) = Some W_15178.
Proof. vm_refl. Qed.
Lemma D_15178 : decode_any W_15178 = Some (Jal 0 2097048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1517c : bv 32 := 0x02990633.
Lemma F_1517c : fetch_word Plain.M.loaded_segments (0x15278 : word) = Some W_1517c.
Proof. vm_refl. Qed.
Lemma D_1517c : decode_any W_1517c = Some (Mul M_MUL 12 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15180 : bv 32 := 0x17d786b7.
Lemma F_15180 : fetch_word Plain.M.loaded_segments (0x1527c : word) = Some W_15180.
Proof. vm_refl. Qed.
Lemma D_15180 : decode_any W_15180 = Some (Lui 13 97656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15184 : bv 32 := 0x4016869b.
Lemma F_15184 : fetch_word Plain.M.loaded_segments (0x15280 : word) = Some W_15184.
Proof. vm_refl. Qed.
Lemma D_15184 : decode_any W_15184 = Some (OpImm32 13 13 1025, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15188 : bv 32 := 0x02d66663.
Lemma F_15188 : fetch_word Plain.M.loaded_segments (0x15284 : word) = Some W_15188.
Proof. vm_refl. Qed.
Lemma D_15188 : decode_any W_15188 = Some (Branch BC_LTU 12 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1518c : bv 32 := 0x0000a517.
Lemma F_1518c : fetch_word Plain.M.loaded_segments (0x15288 : word) = Some W_1518c.
Proof. vm_refl. Qed.
Lemma D_1518c : decode_any W_1518c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15190 : bv 32 := 0xec853503.
Lemma F_15190 : fetch_word Plain.M.loaded_segments (0x1528c : word) = Some W_15190.
Proof. vm_refl. Qed.
Lemma D_15190 : decode_any W_15190 = Some (Load SZ8 true 10 10 3784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15194 : bv 32 := 0x00052503.
Lemma F_15194 : fetch_word Plain.M.loaded_segments (0x15290 : word) = Some W_15194.
Proof. vm_refl. Qed.
Lemma D_15194 : decode_any W_15194 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15198 : bv 32 := 0x00500593.
Lemma F_15198 : fetch_word Plain.M.loaded_segments (0x15294 : word) = Some W_15198.
Proof. vm_refl. Qed.
Lemma D_15198 : decode_any W_15198 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1519c : bv 32 := 0x24a5cc63.
Lemma F_1519c : fetch_word Plain.M.loaded_segments (0x15298 : word) = Some W_1519c.
Proof. vm_refl. Qed.
Lemma D_1519c : decode_any W_1519c = Some (Branch BC_LT 11 10 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151a0 : bv 32 := 0xffffb517.
Lemma F_151a0 : fetch_word Plain.M.loaded_segments (0x1529c : word) = Some W_151a0.
Proof. vm_refl. Qed.
Lemma D_151a0 : decode_any W_151a0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151a4 : bv 32 := 0xffffb597.
Lemma F_151a4 : fetch_word Plain.M.loaded_segments (0x152a0 : word) = Some W_151a4.
Proof. vm_refl. Qed.
Lemma D_151a4 : decode_any W_151a4 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151a8 : bv 32 := 0x08b50513.
Lemma F_151a8 : fetch_word Plain.M.loaded_segments (0x152a4 : word) = Some W_151a8.
Proof. vm_refl. Qed.
Lemma D_151a8 : decode_any W_151a8 = Some (OpImm ALU_ADD 10 10 139, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151ac : bv 32 := 0x3ef58593.
Lemma F_151ac : fetch_word Plain.M.loaded_segments (0x152a8 : word) = Some W_151ac.
Proof. vm_refl. Qed.
Lemma D_151ac : decode_any W_151ac = Some (OpImm ALU_ADD 11 11 1007, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b0 : bv 32 := 0xf61ff06f.
Lemma F_151b0 : fetch_word Plain.M.loaded_segments (0x152ac : word) = Some W_151b0.
Proof. vm_refl. Qed.
Lemma D_151b0 : decode_any W_151b0 = Some (Jal 0 2096992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b4 : bv 32 := 0x01456b83.
Lemma F_151b4 : fetch_word Plain.M.loaded_segments (0x152b0 : word) = Some W_151b4.
Proof. vm_refl. Qed.
Lemma D_151b4 : decode_any W_151b4 = Some (Load SZ4 false 23 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b8 : bv 32 := 0x10000613.
Lemma F_151b8 : fetch_word Plain.M.loaded_segments (0x152b4 : word) = Some W_151b8.
Proof. vm_refl. Qed.
Lemma D_151b8 : decode_any W_151b8 = Some (OpImm ALU_ADD 12 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151bc : bv 32 := 0x0f766063.
Lemma F_151bc : fetch_word Plain.M.loaded_segments (0x152b8 : word) = Some W_151bc.
Proof. vm_refl. Qed.
Lemma D_151bc : decode_any W_151bc = Some (Branch BC_LTU 12 23 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c0 : bv 32 := 0x007b8613.
Lemma F_151c0 : fetch_word Plain.M.loaded_segments (0x152bc : word) = Some W_151c0.
Proof. vm_refl. Qed.
Lemma D_151c0 : decode_any W_151c0 = Some (OpImm ALU_ADD 12 23 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c4 : bv 32 := 0x0025d693.
Lemma F_151c4 : fetch_word Plain.M.loaded_segments (0x152c0 : word) = Some W_151c4.
Proof. vm_refl. Qed.
Lemma D_151c4 : decode_any W_151c4 = Some (ShiftImm ALU_SRL 13 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c8 : bv 32 := 0x0cd67a63.
Lemma F_151c8 : fetch_word Plain.M.loaded_segments (0x152c4 : word) = Some W_151c8.
Proof. vm_refl. Qed.
Lemma D_151c8 : decode_any W_151c8 = Some (Branch BC_GEU 12 13 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151cc : bv 32 := 0x00058413.
Lemma F_151cc : fetch_word Plain.M.loaded_segments (0x152c8 : word) = Some W_151cc.
Proof. vm_refl. Qed.
Lemma D_151cc : decode_any W_151cc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d0 : bv 32 := 0x00050c93.
Lemma F_151d0 : fetch_word Plain.M.loaded_segments (0x152cc : word) = Some W_151d0.
Proof. vm_refl. Qed.
Lemma D_151d0 : decode_any W_151d0 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d4 : bv 32 := 0x00c52a03.
Lemma F_151d4 : fetch_word Plain.M.loaded_segments (0x152d0 : word) = Some W_151d4.
Proof. vm_refl. Qed.
Lemma D_151d4 : decode_any W_151d4 = Some (Load SZ4 true 20 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d8 : bv 32 := 0x00048513.
Lemma F_151d8 : fetch_word Plain.M.loaded_segments (0x152d4 : word) = Some W_151d8.
Proof. vm_refl. Qed.
Lemma D_151d8 : decode_any W_151d8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151dc : bv 32 := 0x00090593.
Lemma F_151dc : fetch_word Plain.M.loaded_segments (0x152d8 : word) = Some W_151dc.
Proof. vm_refl. Qed.
Lemma D_151dc : decode_any W_151dc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151e0 : bv 32 := 0x000a0613.
Lemma F_151e0 : fetch_word Plain.M.loaded_segments (0x152dc : word) = Some W_151e0.
Proof. vm_refl. Qed.
Lemma D_151e0 : decode_any W_151e0 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151e4 : bv 32 := 0x9edfe0ef.
Lemma F_151e4 : fetch_word Plain.M.loaded_segments (0x152e0 : word) = Some W_151e4.
Proof. vm_refl. Qed.
Lemma D_151e4 : decode_any W_151e4 = Some (Jal 1 2091500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151e8 : bv 32 := 0x00a13423.
Lemma F_151e8 : fetch_word Plain.M.loaded_segments (0x152e4 : word) = Some W_151e8.
Proof. vm_refl. Qed.
Lemma D_151e8 : decode_any W_151e8 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151ec : bv 32 := 0x0c050c63.
Lemma F_151ec : fetch_word Plain.M.loaded_segments (0x152e8 : word) = Some W_151ec.
Proof. vm_refl. Qed.
Lemma D_151ec : decode_any W_151ec = Some (Branch BC_EQ 10 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f0 : bv 32 := 0x000b899b.
Lemma F_151f0 : fetch_word Plain.M.loaded_segments (0x152ec : word) = Some W_151f0.
Proof. vm_refl. Qed.
Lemma D_151f0 : decode_any W_151f0 = Some (OpImm32 19 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f4 : bv 32 := 0xcd9fe0ef.
Lemma F_151f4 : fetch_word Plain.M.loaded_segments (0x152f0 : word) = Some W_151f4.
Proof. vm_refl. Qed.
Lemma D_151f4 : decode_any W_151f4 = Some (Jal 1 2092248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f8 : bv 32 := 0x002b9593.
Lemma F_151f8 : fetch_word Plain.M.loaded_segments (0x152f4 : word) = Some W_151f8.
Proof. vm_refl. Qed.
Lemma D_151f8 : decode_any W_151f8 = Some (ShiftImm ALU_SLL 11 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151fc : bv 32 := 0x00299c13.
Lemma F_151fc : fetch_word Plain.M.loaded_segments (0x152f8 : word) = Some W_151fc.
Proof. vm_refl. Qed.
Lemma D_151fc : decode_any W_151fc = Some (ShiftImm ALU_SLL 24 19 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15200 : bv 32 := 0x40b40b3b.
Lemma F_15200 : fetch_word Plain.M.loaded_segments (0x152fc : word) = Some W_15200.
Proof. vm_refl. Qed.
Lemma D_15200 : decode_any W_15200 = Some (Op32 ALU_SUB 22 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15204 : bv 32 := 0x018c8c33.
Lemma F_15204 : fetch_word Plain.M.loaded_segments (0x15300 : word) = Some W_15204.
Proof. vm_refl. Qed.
Lemma D_15204 : decode_any W_15204 = Some (Op ALU_ADD 24 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15208 : bv 32 := 0x018c2a83.
Lemma F_15208 : fetch_word Plain.M.loaded_segments (0x15304 : word) = Some W_15208.
Proof. vm_refl. Qed.
Lemma D_15208 : decode_any W_15208 = Some (Load SZ4 true 21 24 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1520c : bv 32 := 0x02a90533.
Lemma F_1520c : fetch_word Plain.M.loaded_segments (0x15308 : word) = Some W_1520c.
Proof. vm_refl. Qed.
Lemma D_1520c : decode_any W_1520c = Some (Mul M_MUL 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15210 : bv 32 := 0x0025141b.
Lemma F_15210 : fetch_word Plain.M.loaded_segments (0x1530c : word) = Some W_15210.
Proof. vm_refl. Qed.
Lemma D_15210 : decode_any W_15210 = Some (ShiftImm32 ALU_SLL 8 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15214 : bv 32 := 0xfe4b0b1b.
Lemma F_15214 : fetch_word Plain.M.loaded_segments (0x15310 : word) = Some W_15214.
Proof. vm_refl. Qed.
Lemma D_15214 : decode_any W_15214 = Some (OpImm32 22 22 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15218 : bv 32 := 0x00810513.
Lemma F_15218 : fetch_word Plain.M.loaded_segments (0x15314 : word) = Some W_15218.
Proof. vm_refl. Qed.
Lemma D_15218 : decode_any W_15218 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1521c : bv 32 := 0xcf1fe0ef.
Lemma F_1521c : fetch_word Plain.M.loaded_segments (0x15318 : word) = Some W_1521c.
Proof. vm_refl. Qed.
Lemma D_1521c : decode_any W_1521c = Some (Jal 1 2092272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15220 : bv 32 := 0x0d641663.
Lemma F_15220 : fetch_word Plain.M.loaded_segments (0x1531c : word) = Some W_15220.
Proof. vm_refl. Qed.
Lemma D_15220 : decode_any W_15220 = Some (Branch BC_NE 8 22 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15224 : bv 32 := 0x0d541463.
Lemma F_15224 : fetch_word Plain.M.loaded_segments (0x15320 : word) = Some W_15224.
Proof. vm_refl. Qed.
Lemma D_15224 : decode_any W_15224 = Some (Branch BC_NE 8 21 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15228 : bv 32 := 0x00048513.
Lemma F_15228 : fetch_word Plain.M.loaded_segments (0x15324 : word) = Some W_15228.
Proof. vm_refl. Qed.
Lemma D_15228 : decode_any W_15228 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1522c : bv 32 := 0x00090593.
Lemma F_1522c : fetch_word Plain.M.loaded_segments (0x15328 : word) = Some W_1522c.
Proof. vm_refl. Qed.
Lemma D_1522c : decode_any W_1522c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15230 : bv 32 := 0x000a0613.
Lemma F_15230 : fetch_word Plain.M.loaded_segments (0x1532c : word) = Some W_15230.
Proof. vm_refl. Qed.
Lemma D_15230 : decode_any W_15230 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15234 : bv 32 := 0xfd4fe0ef.
Lemma F_15234 : fetch_word Plain.M.loaded_segments (0x15330 : word) = Some W_15234.
Proof. vm_refl. Qed.
Lemma D_15234 : decode_any W_15234 = Some (Jal 1 2090964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15238 : bv 32 := 0x00a13023.
Lemma F_15238 : fetch_word Plain.M.loaded_segments (0x15334 : word) = Some W_15238.
Proof. vm_refl. Qed.
Lemma D_15238 : decode_any W_15238 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1523c : bv 32 := 0x0e050463.
Lemma F_1523c : fetch_word Plain.M.loaded_segments (0x15338 : word) = Some W_1523c.
Proof. vm_refl. Qed.
Lemma D_1523c : decode_any W_1523c = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15240 : bv 32 := 0x100b8663.
Lemma F_15240 : fetch_word Plain.M.loaded_segments (0x1533c : word) = Some W_15240.
Proof. vm_refl. Qed.
Lemma D_15240 : decode_any W_15240 = Some (Branch BC_EQ 23 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15244 : bv 32 := 0x018c8513.
Lemma F_15244 : fetch_word Plain.M.loaded_segments (0x15340 : word) = Some W_15244.
Proof. vm_refl. Qed.
Lemma D_15244 : decode_any W_15244 = Some (OpImm ALU_ADD 10 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15248 : bv 32 := 0x00400593.
Lemma F_15248 : fetch_word Plain.M.loaded_segments (0x15344 : word) = Some W_15248.
Proof. vm_refl. Qed.
Lemma D_15248 : decode_any W_15248 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1524c : bv 32 := 0x00098613.
Lemma F_1524c : fetch_word Plain.M.loaded_segments (0x15348 : word) = Some W_1524c.
Proof. vm_refl. Qed.
Lemma D_1524c : decode_any W_1524c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15250 : bv 32 := 0xf00ff0ef.
Lemma F_15250 : fetch_word Plain.M.loaded_segments (0x1534c : word) = Some W_15250.
Proof. vm_refl. Qed.
Lemma D_15250 : decode_any W_15250 = Some (Jal 1 2094848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15254 : bv 32 := 0x10050063.
Lemma F_15254 : fetch_word Plain.M.loaded_segments (0x15350 : word) = Some W_15254.
Proof. vm_refl. Qed.
Lemma D_15254 : decode_any W_15254 = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15258 : bv 32 := 0x00050493.
Lemma F_15258 : fetch_word Plain.M.loaded_segments (0x15354 : word) = Some W_15258.
Proof. vm_refl. Qed.
Lemma D_15258 : decode_any W_15258 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1525c : bv 32 := 0x00013503.
Lemma F_1525c : fetch_word Plain.M.loaded_segments (0x15358 : word) = Some W_1525c.
Proof. vm_refl. Qed.
Lemma D_1525c : decode_any W_1525c = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15260 : bv 32 := 0x00048593.
Lemma F_15260 : fetch_word Plain.M.loaded_segments (0x1535c : word) = Some W_15260.
Proof. vm_refl. Qed.
Lemma D_15260 : decode_any W_15260 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15264 : bv 32 := 0xdf5fe0ef.
Lemma F_15264 : fetch_word Plain.M.loaded_segments (0x15360 : word) = Some W_15264.
Proof. vm_refl. Qed.
Lemma D_15264 : decode_any W_15264 = Some (Jal 1 2092532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15268 : bv 32 := 0x10050e63.
Lemma F_15268 : fetch_word Plain.M.loaded_segments (0x15364 : word) = Some W_15268.
Proof. vm_refl. Qed.
Lemma D_15268 : decode_any W_15268 = Some (Branch BC_EQ 10 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529c : bv 32 := 0x0000a517.
Lemma F_1529c : fetch_word Plain.M.loaded_segments (0x15398 : word) = Some W_1529c.
Proof. vm_refl. Qed.
Lemma D_1529c : decode_any W_1529c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a0 : bv 32 := 0xdb853503.
Lemma F_152a0 : fetch_word Plain.M.loaded_segments (0x1539c : word) = Some W_152a0.
Proof. vm_refl. Qed.
Lemma D_152a0 : decode_any W_152a0 = Some (Load SZ8 true 10 10 3512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a4 : bv 32 := 0x00052503.
Lemma F_152a4 : fetch_word Plain.M.loaded_segments (0x153a0 : word) = Some W_152a4.
Proof. vm_refl. Qed.
Lemma D_152a4 : decode_any W_152a4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a8 : bv 32 := 0x00500593.
Lemma F_152a8 : fetch_word Plain.M.loaded_segments (0x153a4 : word) = Some W_152a8.
Proof. vm_refl. Qed.
Lemma D_152a8 : decode_any W_152a8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ac : bv 32 := 0x14a5c463.
Lemma F_152ac : fetch_word Plain.M.loaded_segments (0x153a8 : word) = Some W_152ac.
Proof. vm_refl. Qed.
Lemma D_152ac : decode_any W_152ac = Some (Branch BC_LT 11 10 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b0 : bv 32 := 0xffffb517.
Lemma F_152b0 : fetch_word Plain.M.loaded_segments (0x153ac : word) = Some W_152b0.
Proof. vm_refl. Qed.
Lemma D_152b0 : decode_any W_152b0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b4 : bv 32 := 0xffffb597.
Lemma F_152b4 : fetch_word Plain.M.loaded_segments (0x153b0 : word) = Some W_152b4.
Proof. vm_refl. Qed.
Lemma D_152b4 : decode_any W_152b4 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b8 : bv 32 := 0x4ba50513.
Lemma F_152b8 : fetch_word Plain.M.loaded_segments (0x153b4 : word) = Some W_152b8.
Proof. vm_refl. Qed.
Lemma D_152b8 : decode_any W_152b8 = Some (OpImm ALU_ADD 10 10 1210, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bc : bv 32 := 0x2df58593.
Lemma F_152bc : fetch_word Plain.M.loaded_segments (0x153b8 : word) = Some W_152bc.
Proof. vm_refl. Qed.
Lemma D_152bc : decode_any W_152bc = Some (OpImm ALU_ADD 11 11 735, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c0 : bv 32 := 0xe51ff06f.
Lemma F_152c0 : fetch_word Plain.M.loaded_segments (0x153bc : word) = Some W_152c0.
Proof. vm_refl. Qed.
Lemma D_152c0 : decode_any W_152c0 = Some (Jal 0 2096720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c4 : bv 32 := 0x0000a517.
Lemma F_152c4 : fetch_word Plain.M.loaded_segments (0x153c0 : word) = Some W_152c4.
Proof. vm_refl. Qed.
Lemma D_152c4 : decode_any W_152c4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c8 : bv 32 := 0xd9053503.
Lemma F_152c8 : fetch_word Plain.M.loaded_segments (0x153c4 : word) = Some W_152c8.
Proof. vm_refl. Qed.
Lemma D_152c8 : decode_any W_152c8 = Some (Load SZ8 true 10 10 3472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cc : bv 32 := 0x00052503.
Lemma F_152cc : fetch_word Plain.M.loaded_segments (0x153c8 : word) = Some W_152cc.
Proof. vm_refl. Qed.
Lemma D_152cc : decode_any W_152cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d0 : bv 32 := 0x00500593.
Lemma F_152d0 : fetch_word Plain.M.loaded_segments (0x153cc : word) = Some W_152d0.
Proof. vm_refl. Qed.
Lemma D_152d0 : decode_any W_152d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d4 : bv 32 := 0x12a5c063.
Lemma F_152d4 : fetch_word Plain.M.loaded_segments (0x153d0 : word) = Some W_152d4.
Proof. vm_refl. Qed.
Lemma D_152d4 : decode_any W_152d4 = Some (Branch BC_LT 11 10 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d8 : bv 32 := 0xffffb517.
Lemma F_152d8 : fetch_word Plain.M.loaded_segments (0x153d4 : word) = Some W_152d8.
Proof. vm_refl. Qed.
Lemma D_152d8 : decode_any W_152d8 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dc : bv 32 := 0xffffb597.
Lemma F_152dc : fetch_word Plain.M.loaded_segments (0x153d8 : word) = Some W_152dc.
Proof. vm_refl. Qed.
Lemma D_152dc : decode_any W_152dc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e0 : bv 32 := 0x13150513.
Lemma F_152e0 : fetch_word Plain.M.loaded_segments (0x153dc : word) = Some W_152e0.
Proof. vm_refl. Qed.
Lemma D_152e0 : decode_any W_152e0 = Some (OpImm ALU_ADD 10 10 305, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e4 : bv 32 := 0x2b758593.
Lemma F_152e4 : fetch_word Plain.M.loaded_segments (0x153e0 : word) = Some W_152e4.
Proof. vm_refl. Qed.
Lemma D_152e4 : decode_any W_152e4 = Some (OpImm ALU_ADD 11 11 695, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e8 : bv 32 := 0xe29ff06f.
Lemma F_152e8 : fetch_word Plain.M.loaded_segments (0x153e4 : word) = Some W_152e8.
Proof. vm_refl. Qed.
Lemma D_152e8 : decode_any W_152e8 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec : bv 32 := 0x0000a517.
Lemma F_152ec : fetch_word Plain.M.loaded_segments (0x153e8 : word) = Some W_152ec.
Proof. vm_refl. Qed.
Lemma D_152ec : decode_any W_152ec = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f0 : bv 32 := 0xd6853503.
Lemma F_152f0 : fetch_word Plain.M.loaded_segments (0x153ec : word) = Some W_152f0.
Proof. vm_refl. Qed.
Lemma D_152f0 : decode_any W_152f0 = Some (Load SZ8 true 10 10 3432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f4 : bv 32 := 0x00052503.
Lemma F_152f4 : fetch_word Plain.M.loaded_segments (0x153f0 : word) = Some W_152f4.
Proof. vm_refl. Qed.
Lemma D_152f4 : decode_any W_152f4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f8 : bv 32 := 0x00500593.
Lemma F_152f8 : fetch_word Plain.M.loaded_segments (0x153f4 : word) = Some W_152f8.
Proof. vm_refl. Qed.
Lemma D_152f8 : decode_any W_152f8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152fc : bv 32 := 0x0ea5cc63.
Lemma F_152fc : fetch_word Plain.M.loaded_segments (0x153f8 : word) = Some W_152fc.
Proof. vm_refl. Qed.
Lemma D_152fc : decode_any W_152fc = Some (Branch BC_LT 11 10 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15300 : bv 32 := 0xffffb517.
Lemma F_15300 : fetch_word Plain.M.loaded_segments (0x153fc : word) = Some W_15300.
Proof. vm_refl. Qed.
Lemma D_15300 : decode_any W_15300 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15304 : bv 32 := 0xffffb597.
Lemma F_15304 : fetch_word Plain.M.loaded_segments (0x15400 : word) = Some W_15304.
Proof. vm_refl. Qed.
Lemma D_15304 : decode_any W_15304 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15308 : bv 32 := 0x19750513.
Lemma F_15308 : fetch_word Plain.M.loaded_segments (0x15404 : word) = Some W_15308.
Proof. vm_refl. Qed.
Lemma D_15308 : decode_any W_15308 = Some (OpImm ALU_ADD 10 10 407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1530c : bv 32 := 0x28f58593.
Lemma F_1530c : fetch_word Plain.M.loaded_segments (0x15408 : word) = Some W_1530c.
Proof. vm_refl. Qed.
Lemma D_1530c : decode_any W_1530c = Some (OpImm ALU_ADD 11 11 655, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15310 : bv 32 := 0x00040613.
Lemma F_15310 : fetch_word Plain.M.loaded_segments (0x1540c : word) = Some W_15310.
Proof. vm_refl. Qed.
Lemma D_15310 : decode_any W_15310 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15314 : bv 32 := 0x000b0693.
Lemma F_15314 : fetch_word Plain.M.loaded_segments (0x15410 : word) = Some W_15314.
Proof. vm_refl. Qed.
Lemma D_15314 : decode_any W_15314 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15318 : bv 32 := 0x000a8713.
Lemma F_15318 : fetch_word Plain.M.loaded_segments (0x15414 : word) = Some W_15318.
Proof. vm_refl. Qed.
Lemma D_15318 : decode_any W_15318 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1531c : bv 32 := 0xdecfe0ef.
Lemma F_1531c : fetch_word Plain.M.loaded_segments (0x15418 : word) = Some W_1531c.
Proof. vm_refl. Qed.
Lemma D_1531c : decode_any W_1531c = Some (Jal 1 2090476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15320 : bv 32 := 0x0d40006f.
Lemma F_15320 : fetch_word Plain.M.loaded_segments (0x1541c : word) = Some W_15320.
Proof. vm_refl. Qed.
Lemma D_15320 : decode_any W_15320 = Some (Jal 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15324 : bv 32 := 0x0000a517.
Lemma F_15324 : fetch_word Plain.M.loaded_segments (0x15420 : word) = Some W_15324.
Proof. vm_refl. Qed.
Lemma D_15324 : decode_any W_15324 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15328 : bv 32 := 0xd3053503.
Lemma F_15328 : fetch_word Plain.M.loaded_segments (0x15424 : word) = Some W_15328.
Proof. vm_refl. Qed.
Lemma D_15328 : decode_any W_15328 = Some (Load SZ8 true 10 10 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1532c : bv 32 := 0x00052503.
Lemma F_1532c : fetch_word Plain.M.loaded_segments (0x15428 : word) = Some W_1532c.
Proof. vm_refl. Qed.
Lemma D_1532c : decode_any W_1532c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15330 : bv 32 := 0x00500593.
Lemma F_15330 : fetch_word Plain.M.loaded_segments (0x1542c : word) = Some W_15330.
Proof. vm_refl. Qed.
Lemma D_15330 : decode_any W_15330 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15334 : bv 32 := 0x0ca5c063.
Lemma F_15334 : fetch_word Plain.M.loaded_segments (0x15430 : word) = Some W_15334.
Proof. vm_refl. Qed.
Lemma D_15334 : decode_any W_15334 = Some (Branch BC_LT 11 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15338 : bv 32 := 0xffffb517.
Lemma F_15338 : fetch_word Plain.M.loaded_segments (0x15434 : word) = Some W_15338.
Proof. vm_refl. Qed.
Lemma D_15338 : decode_any W_15338 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1533c : bv 32 := 0xffffb597.
Lemma F_1533c : fetch_word Plain.M.loaded_segments (0x15438 : word) = Some W_1533c.
Proof. vm_refl. Qed.
Lemma D_1533c : decode_any W_1533c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15340 : bv 32 := 0x4a650513.
Lemma F_15340 : fetch_word Plain.M.loaded_segments (0x1543c : word) = Some W_15340.
Proof. vm_refl. Qed.
Lemma D_15340 : decode_any W_15340 = Some (OpImm ALU_ADD 10 10 1190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15344 : bv 32 := 0x25758593.
Lemma F_15344 : fetch_word Plain.M.loaded_segments (0x15440 : word) = Some W_15344.
Proof. vm_refl. Qed.
Lemma D_15344 : decode_any W_15344 = Some (OpImm ALU_ADD 11 11 599, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15348 : bv 32 := 0x0a00006f.
Lemma F_15348 : fetch_word Plain.M.loaded_segments (0x15444 : word) = Some W_15348.
Proof. vm_refl. Qed.
Lemma D_15348 : decode_any W_15348 = Some (Jal 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1534c : bv 32 := 0x00000493.
Lemma F_1534c : fetch_word Plain.M.loaded_segments (0x15448 : word) = Some W_1534c.
Proof. vm_refl. Qed.
Lemma D_1534c : decode_any W_1534c = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15350 : bv 32 := 0x0380006f.
Lemma F_15350 : fetch_word Plain.M.loaded_segments (0x1544c : word) = Some W_15350.
Proof. vm_refl. Qed.
Lemma D_15350 : decode_any W_15350 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15354 : bv 32 := 0x00010513.
Lemma F_15354 : fetch_word Plain.M.loaded_segments (0x15450 : word) = Some W_15354.
Proof. vm_refl. Qed.
Lemma D_15354 : decode_any W_15354 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15358 : bv 32 := 0xbb5fe0ef.
Lemma F_15358 : fetch_word Plain.M.loaded_segments (0x15454 : word) = Some W_15358.
Proof. vm_refl. Qed.
Lemma D_15358 : decode_any W_15358 = Some (Jal 1 2091956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1535c : bv 32 := 0x0000a517.
Lemma F_1535c : fetch_word Plain.M.loaded_segments (0x15458 : word) = Some W_1535c.
Proof. vm_refl. Qed.
Lemma D_1535c : decode_any W_1535c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15360 : bv 32 := 0xcf853503.
Lemma F_15360 : fetch_word Plain.M.loaded_segments (0x1545c : word) = Some W_15360.
Proof. vm_refl. Qed.
Lemma D_15360 : decode_any W_15360 = Some (Load SZ8 true 10 10 3320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15364 : bv 32 := 0x00052503.
Lemma F_15364 : fetch_word Plain.M.loaded_segments (0x15460 : word) = Some W_15364.
Proof. vm_refl. Qed.
Lemma D_15364 : decode_any W_15364 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15368 : bv 32 := 0x00500593.
Lemma F_15368 : fetch_word Plain.M.loaded_segments (0x15464 : word) = Some W_15368.
Proof. vm_refl. Qed.
Lemma D_15368 : decode_any W_15368 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1536c : bv 32 := 0x08a5c463.
Lemma F_1536c : fetch_word Plain.M.loaded_segments (0x15468 : word) = Some W_1536c.
Proof. vm_refl. Qed.
Lemma D_1536c : decode_any W_1536c = Some (Branch BC_LT 11 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15370 : bv 32 := 0xffffb517.
Lemma F_15370 : fetch_word Plain.M.loaded_segments (0x1546c : word) = Some W_15370.
Proof. vm_refl. Qed.
Lemma D_15370 : decode_any W_15370 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15374 : bv 32 := 0xffffb597.
Lemma F_15374 : fetch_word Plain.M.loaded_segments (0x15470 : word) = Some W_15374.
Proof. vm_refl. Qed.
Lemma D_15374 : decode_any W_15374 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15378 : bv 32 := 0x70b50513.
Lemma F_15378 : fetch_word Plain.M.loaded_segments (0x15474 : word) = Some W_15378.
Proof. vm_refl. Qed.
Lemma D_15378 : decode_any W_15378 = Some (OpImm ALU_ADD 10 10 1803, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1537c : bv 32 := 0x21f58593.
Lemma F_1537c : fetch_word Plain.M.loaded_segments (0x15478 : word) = Some W_1537c.
Proof. vm_refl. Qed.
Lemma D_1537c : decode_any W_1537c = Some (OpImm ALU_ADD 11 11 543, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15380 : bv 32 := 0x0680006f.
Lemma F_15380 : fetch_word Plain.M.loaded_segments (0x1547c : word) = Some W_15380.
Proof. vm_refl. Qed.
Lemma D_15380 : decode_any W_15380 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15384 : bv 32 := 0x00013503.
Lemma F_15384 : fetch_word Plain.M.loaded_segments (0x15480 : word) = Some W_15384.
Proof. vm_refl. Qed.
Lemma D_15384 : decode_any W_15384 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15388 : bv 32 := 0xe35fe0ef.
Lemma F_15388 : fetch_word Plain.M.loaded_segments (0x15484 : word) = Some W_15388.
Proof. vm_refl. Qed.
Lemma D_15388 : decode_any W_15388 = Some (Jal 1 2092596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1538c : bv 32 := 0x01cc0593.
Lemma F_1538c : fetch_word Plain.M.loaded_segments (0x15488 : word) = Some W_1538c.
Proof. vm_refl. Qed.
Lemma D_1538c : decode_any W_1538c = Some (OpImm ALU_ADD 11 24 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15390 : bv 32 := 0x00040613.
Lemma F_15390 : fetch_word Plain.M.loaded_segments (0x1548c : word) = Some W_15390.
Proof. vm_refl. Qed.
Lemma D_15390 : decode_any W_15390 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15394 : bv 32 := 0x2a8080ef.
Lemma F_15394 : fetch_word Plain.M.loaded_segments (0x15490 : word) = Some W_15394.
Proof. vm_refl. Qed.
Lemma D_15394 : decode_any W_15394 = Some (Jal 1 33448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15398 : bv 32 := 0x000b8e63.
Lemma F_15398 : fetch_word Plain.M.loaded_segments (0x15494 : word) = Some W_15398.
Proof. vm_refl. Qed.
Lemma D_15398 : decode_any W_15398 = Some (Branch BC_EQ 23 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1539c : bv 32 := 0x00013583.
Lemma F_1539c : fetch_word Plain.M.loaded_segments (0x15498 : word) = Some W_1539c.
Proof. vm_refl. Qed.
Lemma D_1539c : decode_any W_1539c = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a0 : bv 32 := 0x01410613.
Lemma F_153a0 : fetch_word Plain.M.loaded_segments (0x1549c : word) = Some W_153a0.
Proof. vm_refl. Qed.
Lemma D_153a0 : decode_any W_153a0 = Some (OpImm ALU_ADD 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a4 : bv 32 := 0x00048513.
Lemma F_153a4 : fetch_word Plain.M.loaded_segments (0x154a0 : word) = Some W_153a4.
Proof. vm_refl. Qed.
Lemma D_153a4 : decode_any W_153a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a8 : bv 32 := 0xa28ff0ef.
Lemma F_153a8 : fetch_word Plain.M.loaded_segments (0x154a4 : word) = Some W_153a8.
Proof. vm_refl. Qed.
Lemma D_153a8 : decode_any W_153a8 = Some (Jal 1 2093608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153ac : bv 32 := 0x01412503.
Lemma F_153ac : fetch_word Plain.M.loaded_segments (0x154a8 : word) = Some W_153ac.
Proof. vm_refl. Qed.
Lemma D_153ac : decode_any W_153ac = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b0 : bv 32 := 0x00050663.
Lemma F_153b0 : fetch_word Plain.M.loaded_segments (0x154ac : word) = Some W_153b0.
Proof. vm_refl. Qed.
Lemma D_153b0 : decode_any W_153b0 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b4 : bv 32 := 0x00013503.
Lemma F_153b4 : fetch_word Plain.M.loaded_segments (0x154b0 : word) = Some W_153b4.
Proof. vm_refl. Qed.
Lemma D_153b4 : decode_any W_153b4 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b8 : bv 32 := 0x0400006f.
Lemma F_153b8 : fetch_word Plain.M.loaded_segments (0x154b4 : word) = Some W_153b8.
Proof. vm_refl. Qed.
Lemma D_153b8 : decode_any W_153b8 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153bc : bv 32 := 0x00010513.
Lemma F_153bc : fetch_word Plain.M.loaded_segments (0x154b8 : word) = Some W_153bc.
Proof. vm_refl. Qed.
Lemma D_153bc : decode_any W_153bc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153c0 : bv 32 := 0xb4dfe0ef.
Lemma F_153c0 : fetch_word Plain.M.loaded_segments (0x154bc : word) = Some W_153c0.
Proof. vm_refl. Qed.
Lemma D_153c0 : decode_any W_153c0 = Some (Jal 1 2091852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153c4 : bv 32 := 0x0000a517.
Lemma F_153c4 : fetch_word Plain.M.loaded_segments (0x154c0 : word) = Some W_153c4.
Proof. vm_refl. Qed.
Lemma D_153c4 : decode_any W_153c4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153c8 : bv 32 := 0xc9053503.
Lemma F_153c8 : fetch_word Plain.M.loaded_segments (0x154c4 : word) = Some W_153c8.
Proof. vm_refl. Qed.
Lemma D_153c8 : decode_any W_153c8 = Some (Load SZ8 true 10 10 3216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153cc : bv 32 := 0x00052503.
Lemma F_153cc : fetch_word Plain.M.loaded_segments (0x154c8 : word) = Some W_153cc.
Proof. vm_refl. Qed.
Lemma D_153cc : decode_any W_153cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d0 : bv 32 := 0x00500593.
Lemma F_153d0 : fetch_word Plain.M.loaded_segments (0x154cc : word) = Some W_153d0.
Proof. vm_refl. Qed.
Lemma D_153d0 : decode_any W_153d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d4 : bv 32 := 0x02a5c063.
Lemma F_153d4 : fetch_word Plain.M.loaded_segments (0x154d0 : word) = Some W_153d4.
Proof. vm_refl. Qed.
Lemma D_153d4 : decode_any W_153d4 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d8 : bv 32 := 0xffffb517.
Lemma F_153d8 : fetch_word Plain.M.loaded_segments (0x154d4 : word) = Some W_153d8.
Proof. vm_refl. Qed.
Lemma D_153d8 : decode_any W_153d8 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153dc : bv 32 := 0xffffb597.
Lemma F_153dc : fetch_word Plain.M.loaded_segments (0x154d8 : word) = Some W_153dc.
Proof. vm_refl. Qed.
Lemma D_153dc : decode_any W_153dc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e0 : bv 32 := 0xf5050513.
Lemma F_153e0 : fetch_word Plain.M.loaded_segments (0x154dc : word) = Some W_153e0.
Proof. vm_refl. Qed.
Lemma D_153e0 : decode_any W_153e0 = Some (OpImm ALU_ADD 10 10 3920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e4 : bv 32 := 0x1b758593.
Lemma F_153e4 : fetch_word Plain.M.loaded_segments (0x154e0 : word) = Some W_153e4.
Proof. vm_refl. Qed.
Lemma D_153e4 : decode_any W_153e4 = Some (OpImm ALU_ADD 11 11 439, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e8 : bv 32 := 0x00000613.
Lemma F_153e8 : fetch_word Plain.M.loaded_segments (0x154e4 : word) = Some W_153e8.
Proof. vm_refl. Qed.
Lemma D_153e8 : decode_any W_153e8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153ec : bv 32 := 0xdb8fe0ef.
Lemma F_153ec : fetch_word Plain.M.loaded_segments (0x154e8 : word) = Some W_153ec.
Proof. vm_refl. Qed.
Lemma D_153ec : decode_any W_153ec = Some (Jal 1 2090424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f0 : bv 32 := 0x0080006f.
Lemma F_153f0 : fetch_word Plain.M.loaded_segments (0x154ec : word) = Some W_153f0.
Proof. vm_refl. Qed.
Lemma D_153f0 : decode_any W_153f0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f4 : bv 32 := 0x00000513.
Lemma F_153f4 : fetch_word Plain.M.loaded_segments (0x154f0 : word) = Some W_153f4.
Proof. vm_refl. Qed.
Lemma D_153f4 : decode_any W_153f4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f8 : bv 32 := 0x06813083.
Lemma F_153f8 : fetch_word Plain.M.loaded_segments (0x154f4 : word) = Some W_153f8.
Proof. vm_refl. Qed.
Lemma D_153f8 : decode_any W_153f8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153fc : bv 32 := 0x06013403.
Lemma F_153fc : fetch_word Plain.M.loaded_segments (0x154f8 : word) = Some W_153fc.
Proof. vm_refl. Qed.
Lemma D_153fc : decode_any W_153fc = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15400 : bv 32 := 0x05813483.
Lemma F_15400 : fetch_word Plain.M.loaded_segments (0x154fc : word) = Some W_15400.
Proof. vm_refl. Qed.
Lemma D_15400 : decode_any W_15400 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15404 : bv 32 := 0x05013903.
Lemma F_15404 : fetch_word Plain.M.loaded_segments (0x15500 : word) = Some W_15404.
Proof. vm_refl. Qed.
Lemma D_15404 : decode_any W_15404 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15408 : bv 32 := 0x04813983.
Lemma F_15408 : fetch_word Plain.M.loaded_segments (0x15504 : word) = Some W_15408.
Proof. vm_refl. Qed.
Lemma D_15408 : decode_any W_15408 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1540c : bv 32 := 0x04013a03.
Lemma F_1540c : fetch_word Plain.M.loaded_segments (0x15508 : word) = Some W_1540c.
Proof. vm_refl. Qed.
Lemma D_1540c : decode_any W_1540c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15410 : bv 32 := 0x03813a83.
Lemma F_15410 : fetch_word Plain.M.loaded_segments (0x1550c : word) = Some W_15410.
Proof. vm_refl. Qed.
Lemma D_15410 : decode_any W_15410 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15414 : bv 32 := 0x03013b03.
Lemma F_15414 : fetch_word Plain.M.loaded_segments (0x15510 : word) = Some W_15414.
Proof. vm_refl. Qed.
Lemma D_15414 : decode_any W_15414 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15418 : bv 32 := 0x02813b83.
Lemma F_15418 : fetch_word Plain.M.loaded_segments (0x15514 : word) = Some W_15418.
Proof. vm_refl. Qed.
Lemma D_15418 : decode_any W_15418 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1541c : bv 32 := 0x02013c03.
Lemma F_1541c : fetch_word Plain.M.loaded_segments (0x15518 : word) = Some W_1541c.
Proof. vm_refl. Qed.
Lemma D_1541c : decode_any W_1541c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15420 : bv 32 := 0x01813c83.
Lemma F_15420 : fetch_word Plain.M.loaded_segments (0x1551c : word) = Some W_15420.
Proof. vm_refl. Qed.
Lemma D_15420 : decode_any W_15420 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15424 : bv 32 := 0x07010113.
Lemma F_15424 : fetch_word Plain.M.loaded_segments (0x15520 : word) = Some W_15424.
Proof. vm_refl. Qed.
Lemma D_15424 : decode_any W_15424 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15428 : bv 32 := 0x00008067.
Lemma F_15428 : fetch_word Plain.M.loaded_segments (0x15524 : word) = Some W_15428.
Proof. vm_refl. Qed.
Lemma D_15428 : decode_any W_15428 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1542c : bv 32 := 0xfd010113.
Lemma F_1542c : fetch_word Plain.M.loaded_segments (0x15528 : word) = Some W_1542c.
Proof. vm_refl. Qed.
Lemma D_1542c : decode_any W_1542c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15430 : bv 32 := 0x02113423.
Lemma F_15430 : fetch_word Plain.M.loaded_segments (0x1552c : word) = Some W_15430.
Proof. vm_refl. Qed.
Lemma D_15430 : decode_any W_15430 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15434 : bv 32 := 0x02813023.
Lemma F_15434 : fetch_word Plain.M.loaded_segments (0x15530 : word) = Some W_15434.
Proof. vm_refl. Qed.
Lemma D_15434 : decode_any W_15434 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15438 : bv 32 := 0x00913c23.
Lemma F_15438 : fetch_word Plain.M.loaded_segments (0x15534 : word) = Some W_15438.
Proof. vm_refl. Qed.
Lemma D_15438 : decode_any W_15438 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1543c : bv 32 := 0x01213823.
Lemma F_1543c : fetch_word Plain.M.loaded_segments (0x15538 : word) = Some W_1543c.
Proof. vm_refl. Qed.
Lemma D_1543c : decode_any W_1543c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15440 : bv 32 := 0x01313423.
Lemma F_15440 : fetch_word Plain.M.loaded_segments (0x1553c : word) = Some W_15440.
Proof. vm_refl. Qed.
Lemma D_15440 : decode_any W_15440 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15444 : bv 32 := 0x01413023.
Lemma F_15444 : fetch_word Plain.M.loaded_segments (0x15540 : word) = Some W_15444.
Proof. vm_refl. Qed.
Lemma D_15444 : decode_any W_15444 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15448 : bv 32 := 0x06b05463.
Lemma F_15448 : fetch_word Plain.M.loaded_segments (0x15544 : word) = Some W_15448.
Proof. vm_refl. Qed.
Lemma D_15448 : decode_any W_15448 = Some (Branch BC_GE 0 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1544c : bv 32 := 0x08a05663.
Lemma F_1544c : fetch_word Plain.M.loaded_segments (0x15548 : word) = Some W_1544c.
Proof. vm_refl. Qed.
Lemma D_1544c : decode_any W_1544c = Some (Branch BC_GE 0 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15450 : bv 32 := 0x00058413.
Lemma F_15450 : fetch_word Plain.M.loaded_segments (0x1554c : word) = Some W_15450.
Proof. vm_refl. Qed.
Lemma D_15450 : decode_any W_15450 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15454 : bv 32 := 0x02a585b3.
Lemma F_15454 : fetch_word Plain.M.loaded_segments (0x15550 : word) = Some W_15454.
Proof. vm_refl. Qed.
Lemma D_15454 : decode_any W_15454 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15458 : bv 32 := 0x01d5d593.
Lemma F_15458 : fetch_word Plain.M.loaded_segments (0x15554 : word) = Some W_15458.
Proof. vm_refl. Qed.
Lemma D_15458 : decode_any W_15458 = Some (ShiftImm ALU_SRL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1545c : bv 32 := 0x0a058263.
Lemma F_1545c : fetch_word Plain.M.loaded_segments (0x15558 : word) = Some W_1545c.
Proof. vm_refl. Qed.
Lemma D_1545c : decode_any W_1545c = Some (Branch BC_EQ 11 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15500 : bv 32 := 0xfffe85b7.
Lemma F_15500 : fetch_word Plain.M.loaded_segments (0x155fc : word) = Some W_15500.
Proof. vm_refl. Qed.
Lemma D_15500 : decode_any W_15500 = Some (Lui 11 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15504 : bv 32 := 0x95f5849b.
Lemma F_15504 : fetch_word Plain.M.loaded_segments (0x15600 : word) = Some W_15504.
Proof. vm_refl. Qed.
Lemma D_15504 : decode_any W_15504 = Some (OpImm32 9 11 2399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15508 : bv 32 := 0x00050913.
Lemma F_15508 : fetch_word Plain.M.loaded_segments (0x15604 : word) = Some W_15508.
Proof. vm_refl. Qed.
Lemma D_15508 : decode_any W_15508 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1550c : bv 32 := 0x00100513.
Lemma F_1550c : fetch_word Plain.M.loaded_segments (0x15608 : word) = Some W_1550c.
Proof. vm_refl. Qed.
Lemma D_1550c : decode_any W_1550c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15510 : bv 32 := 0x01800593.
Lemma F_15510 : fetch_word Plain.M.loaded_segments (0x1560c : word) = Some W_15510.
Proof. vm_refl. Qed.
Lemma D_15510 : decode_any W_15510 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15514 : bv 32 := 0x6bd000ef.
Lemma F_15514 : fetch_word Plain.M.loaded_segments (0x15610 : word) = Some W_15514.
Proof. vm_refl. Qed.
Lemma D_15514 : decode_any W_15514 = Some (Jal 1 3772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15518 : bv 32 := 0x009405bb.
Lemma F_15518 : fetch_word Plain.M.loaded_segments (0x15614 : word) = Some W_15518.
Proof. vm_refl. Qed.
Lemma D_15518 : decode_any W_15518 = Some (Op32 ALU_ADD 11 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1551c : bv 32 := 0x01252023.
Lemma F_1551c : fetch_word Plain.M.loaded_segments (0x15618 : word) = Some W_1551c.
Proof. vm_refl. Qed.
Lemma D_1551c : decode_any W_1551c = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15520 : bv 32 := 0x00852223.
Lemma F_15520 : fetch_word Plain.M.loaded_segments (0x1561c : word) = Some W_15520.
Proof. vm_refl. Qed.
Lemma D_15520 : decode_any W_15520 = Some (Store SZ4 10 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15524 : bv 32 := 0x02b4e463.
Lemma F_15524 : fetch_word Plain.M.loaded_segments (0x15620 : word) = Some W_15524.
Proof. vm_refl. Qed.
Lemma D_15524 : decode_any W_15524 = Some (Branch BC_LTU 9 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1554c : bv 32 := 0x009905bb.
Lemma F_1554c : fetch_word Plain.M.loaded_segments (0x15648 : word) = Some W_1554c.
Proof. vm_refl. Qed.
Lemma D_1554c : decode_any W_1554c = Some (Op32 ALU_ADD 11 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15550 : bv 32 := 0x0ab4ee63.
Lemma F_15550 : fetch_word Plain.M.loaded_segments (0x1564c : word) = Some W_15550.
Proof. vm_refl. Qed.
Lemma D_15550 : decode_any W_15550 = Some (Branch BC_LTU 9 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155ec : bv 32 := 0x02813083.
Lemma F_155ec : fetch_word Plain.M.loaded_segments (0x156e8 : word) = Some W_155ec.
Proof. vm_refl. Qed.
Lemma D_155ec : decode_any W_155ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f0 : bv 32 := 0x02013403.
Lemma F_155f0 : fetch_word Plain.M.loaded_segments (0x156ec : word) = Some W_155f0.
Proof. vm_refl. Qed.
Lemma D_155f0 : decode_any W_155f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f4 : bv 32 := 0x01813483.
Lemma F_155f4 : fetch_word Plain.M.loaded_segments (0x156f0 : word) = Some W_155f4.
Proof. vm_refl. Qed.
Lemma D_155f4 : decode_any W_155f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f8 : bv 32 := 0x01013903.
Lemma F_155f8 : fetch_word Plain.M.loaded_segments (0x156f4 : word) = Some W_155f8.
Proof. vm_refl. Qed.
Lemma D_155f8 : decode_any W_155f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155fc : bv 32 := 0x00813983.
Lemma F_155fc : fetch_word Plain.M.loaded_segments (0x156f8 : word) = Some W_155fc.
Proof. vm_refl. Qed.
Lemma D_155fc : decode_any W_155fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15600 : bv 32 := 0x00013a03.
Lemma F_15600 : fetch_word Plain.M.loaded_segments (0x156fc : word) = Some W_15600.
Proof. vm_refl. Qed.
Lemma D_15600 : decode_any W_15600 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15604 : bv 32 := 0x03010113.
Lemma F_15604 : fetch_word Plain.M.loaded_segments (0x15700 : word) = Some W_15604.
Proof. vm_refl. Qed.
Lemma D_15604 : decode_any W_15604 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15608 : bv 32 := 0x00008067.
Lemma F_15608 : fetch_word Plain.M.loaded_segments (0x15704 : word) = Some W_15608.
Proof. vm_refl. Qed.
Lemma D_15608 : decode_any W_15608 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1560c : bv 32 := 0x00050993.
Lemma F_1560c : fetch_word Plain.M.loaded_segments (0x15708 : word) = Some W_1560c.
Proof. vm_refl. Qed.
Lemma D_1560c : decode_any W_1560c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15610 : bv 32 := 0x00800593.
Lemma F_15610 : fetch_word Plain.M.loaded_segments (0x1570c : word) = Some W_15610.
Proof. vm_refl. Qed.
Lemma D_15610 : decode_any W_15610 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15614 : bv 32 := 0x00090513.
Lemma F_15614 : fetch_word Plain.M.loaded_segments (0x15710 : word) = Some W_15614.
Proof. vm_refl. Qed.
Lemma D_15614 : decode_any W_15614 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15618 : bv 32 := 0x5b9000ef.
Lemma F_15618 : fetch_word Plain.M.loaded_segments (0x15714 : word) = Some W_15618.
Proof. vm_refl. Qed.
Lemma D_15618 : decode_any W_15618 = Some (Jal 1 3512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1561c : bv 32 := 0x00050493.
Lemma F_1561c : fetch_word Plain.M.loaded_segments (0x15718 : word) = Some W_1561c.
Proof. vm_refl. Qed.
Lemma D_1561c : decode_any W_1561c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15620 : bv 32 := 0x00391913.
Lemma F_15620 : fetch_word Plain.M.loaded_segments (0x1571c : word) = Some W_15620.
Proof. vm_refl. Qed.
Lemma D_15620 : decode_any W_15620 = Some (ShiftImm ALU_SLL 18 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15624 : bv 32 := 0x01250933.
Lemma F_15624 : fetch_word Plain.M.loaded_segments (0x15720 : word) = Some W_15624.
Proof. vm_refl. Qed.
Lemma D_15624 : decode_any W_15624 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15628 : bv 32 := 0x00050a13.
Lemma F_15628 : fetch_word Plain.M.loaded_segments (0x15724 : word) = Some W_15628.
Proof. vm_refl. Qed.
Lemma D_15628 : decode_any W_15628 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1562c : bv 32 := 0x00400593.
Lemma F_1562c : fetch_word Plain.M.loaded_segments (0x15728 : word) = Some W_1562c.
Proof. vm_refl. Qed.
Lemma D_1562c : decode_any W_1562c = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15630 : bv 32 := 0x00040513.
Lemma F_15630 : fetch_word Plain.M.loaded_segments (0x1572c : word) = Some W_15630.
Proof. vm_refl. Qed.
Lemma D_15630 : decode_any W_15630 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15634 : bv 32 := 0x59d000ef.
Lemma F_15634 : fetch_word Plain.M.loaded_segments (0x15730 : word) = Some W_15634.
Proof. vm_refl. Qed.
Lemma D_15634 : decode_any W_15634 = Some (Jal 1 3484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15638 : bv 32 := 0x00aa3023.
Lemma F_15638 : fetch_word Plain.M.loaded_segments (0x15734 : word) = Some W_15638.
Proof. vm_refl. Qed.
Lemma D_15638 : decode_any W_15638 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1563c : bv 32 := 0x008a0a13.
Lemma F_1563c : fetch_word Plain.M.loaded_segments (0x15738 : word) = Some W_1563c.
Proof. vm_refl. Qed.
Lemma D_1563c : decode_any W_1563c = Some (OpImm ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15640 : bv 32 := 0xff2a16e3.
Lemma F_15640 : fetch_word Plain.M.loaded_segments (0x1573c : word) = Some W_15640.
Proof. vm_refl. Qed.
Lemma D_15640 : decode_any W_15640 = Some (Branch BC_NE 20 18 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15644 : bv 32 := 0x00098513.
Lemma F_15644 : fetch_word Plain.M.loaded_segments (0x15740 : word) = Some W_15644.
Proof. vm_refl. Qed.
Lemma D_15644 : decode_any W_15644 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15648 : bv 32 := 0x0099b823.
Lemma F_15648 : fetch_word Plain.M.loaded_segments (0x15744 : word) = Some W_15648.
Proof. vm_refl. Qed.
Lemma D_15648 : decode_any W_15648 = Some (Store SZ8 19 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1564c : bv 32 := 0xfa1ff06f.
Lemma F_1564c : fetch_word Plain.M.loaded_segments (0x15748 : word) = Some W_1564c.
Proof. vm_refl. Qed.
Lemma D_1564c : decode_any W_1564c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15650 : bv 32 := 0xfd010113.
Lemma F_15650 : fetch_word Plain.M.loaded_segments (0x1574c : word) = Some W_15650.
Proof. vm_refl. Qed.
Lemma D_15650 : decode_any W_15650 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15654 : bv 32 := 0x02113423.
Lemma F_15654 : fetch_word Plain.M.loaded_segments (0x15750 : word) = Some W_15654.
Proof. vm_refl. Qed.
Lemma D_15654 : decode_any W_15654 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15658 : bv 32 := 0x02813023.
Lemma F_15658 : fetch_word Plain.M.loaded_segments (0x15754 : word) = Some W_15658.
Proof. vm_refl. Qed.
Lemma D_15658 : decode_any W_15658 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1565c : bv 32 := 0x00913c23.
Lemma F_1565c : fetch_word Plain.M.loaded_segments (0x15758 : word) = Some W_1565c.
Proof. vm_refl. Qed.
Lemma D_1565c : decode_any W_1565c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15660 : bv 32 := 0x01213823.
Lemma F_15660 : fetch_word Plain.M.loaded_segments (0x1575c : word) = Some W_15660.
Proof. vm_refl. Qed.
Lemma D_15660 : decode_any W_15660 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15664 : bv 32 := 0x01313423.
Lemma F_15664 : fetch_word Plain.M.loaded_segments (0x15760 : word) = Some W_15664.
Proof. vm_refl. Qed.
Lemma D_15664 : decode_any W_15664 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15668 : bv 32 := 0x04050c63.
Lemma F_15668 : fetch_word Plain.M.loaded_segments (0x15764 : word) = Some W_15668.
Proof. vm_refl. Qed.
Lemma D_15668 : decode_any W_15668 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1566c : bv 32 := 0x00050413.
Lemma F_1566c : fetch_word Plain.M.loaded_segments (0x15768 : word) = Some W_1566c.
Proof. vm_refl. Qed.
Lemma D_1566c : decode_any W_1566c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15670 : bv 32 := 0x00053483.
Lemma F_15670 : fetch_word Plain.M.loaded_segments (0x1576c : word) = Some W_15670.
Proof. vm_refl. Qed.
Lemma D_15670 : decode_any W_15670 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15674 : bv 32 := 0x08048663.
Lemma F_15674 : fetch_word Plain.M.loaded_segments (0x15770 : word) = Some W_15674.
Proof. vm_refl. Qed.
Lemma D_15674 : decode_any W_15674 = Some (Branch BC_EQ 9 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15678 : bv 32 := 0x0004a503.
Lemma F_15678 : fetch_word Plain.M.loaded_segments (0x15774 : word) = Some W_15678.
Proof. vm_refl. Qed.
Lemma D_15678 : decode_any W_15678 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1567c : bv 32 := 0x02a05663.
Lemma F_1567c : fetch_word Plain.M.loaded_segments (0x15778 : word) = Some W_1567c.
Proof. vm_refl. Qed.
Lemma D_1567c : decode_any W_1567c = Some (Branch BC_GE 0 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15680 : bv 32 := 0x00000913.
Lemma F_15680 : fetch_word Plain.M.loaded_segments (0x1577c : word) = Some W_15680.
Proof. vm_refl. Qed.
Lemma D_15680 : decode_any W_15680 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15684 : bv 32 := 0x00000993.
Lemma F_15684 : fetch_word Plain.M.loaded_segments (0x15780 : word) = Some W_15684.
Proof. vm_refl. Qed.
Lemma D_15684 : decode_any W_15684 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15688 : bv 32 := 0x0104b503.
Lemma F_15688 : fetch_word Plain.M.loaded_segments (0x15784 : word) = Some W_15688.
Proof. vm_refl. Qed.
Lemma D_15688 : decode_any W_15688 = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c : bv 32 := 0x01250533.
Lemma F_1568c : fetch_word Plain.M.loaded_segments (0x15788 : word) = Some W_1568c.
Proof. vm_refl. Qed.
Lemma D_1568c : decode_any W_1568c = Some (Op ALU_ADD 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15690 : bv 32 := 0x00053503.
Lemma F_15690 : fetch_word Plain.M.loaded_segments (0x1578c : word) = Some W_15690.
Proof. vm_refl. Qed.
Lemma D_15690 : decode_any W_15690 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15694 : bv 32 := 0x675000ef.
Lemma F_15694 : fetch_word Plain.M.loaded_segments (0x15790 : word) = Some W_15694.
Proof. vm_refl. Qed.
Lemma D_15694 : decode_any W_15694 = Some (Jal 1 3700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15698 : bv 32 := 0x0004a503.
Lemma F_15698 : fetch_word Plain.M.loaded_segments (0x15794 : word) = Some W_15698.
Proof. vm_refl. Qed.
Lemma D_15698 : decode_any W_15698 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1569c : bv 32 := 0x00198993.
Lemma F_1569c : fetch_word Plain.M.loaded_segments (0x15798 : word) = Some W_1569c.
Proof. vm_refl. Qed.
Lemma D_1569c : decode_any W_1569c = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a0 : bv 32 := 0x00890913.
Lemma F_156a0 : fetch_word Plain.M.loaded_segments (0x1579c : word) = Some W_156a0.
Proof. vm_refl. Qed.
Lemma D_156a0 : decode_any W_156a0 = Some (OpImm ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a4 : bv 32 := 0xfea9c2e3.
Lemma F_156a4 : fetch_word Plain.M.loaded_segments (0x157a0 : word) = Some W_156a4.
Proof. vm_refl. Qed.
Lemma D_156a4 : decode_any W_156a4 = Some (Branch BC_LT 19 10 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a8 : bv 32 := 0x0104b503.
Lemma F_156a8 : fetch_word Plain.M.loaded_segments (0x157a4 : word) = Some W_156a8.
Proof. vm_refl. Qed.
Lemma D_156a8 : decode_any W_156a8 = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ac : bv 32 := 0x65d000ef.
Lemma F_156ac : fetch_word Plain.M.loaded_segments (0x157a8 : word) = Some W_156ac.
Proof. vm_refl. Qed.
Lemma D_156ac : decode_any W_156ac = Some (Jal 1 3676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b0 : bv 32 := 0x00048513.
Lemma F_156b0 : fetch_word Plain.M.loaded_segments (0x157ac : word) = Some W_156b0.
Proof. vm_refl. Qed.
Lemma D_156b0 : decode_any W_156b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b4 : bv 32 := 0x655000ef.
Lemma F_156b4 : fetch_word Plain.M.loaded_segments (0x157b0 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (Jal 1 3668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b8 : bv 32 := 0x00043023.
Lemma F_156b8 : fetch_word Plain.M.loaded_segments (0x157b4 : word) = Some W_156b8.
Proof. vm_refl. Qed.
Lemma D_156b8 : decode_any W_156b8 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156bc : bv 32 := 0x0440006f.
Lemma F_156bc : fetch_word Plain.M.loaded_segments (0x157b8 : word) = Some W_156bc.
Proof. vm_refl. Qed.
Lemma D_156bc : decode_any W_156bc = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15700 : bv 32 := 0x02813083.
Lemma F_15700 : fetch_word Plain.M.loaded_segments (0x157fc : word) = Some W_15700.
Proof. vm_refl. Qed.
Lemma D_15700 : decode_any W_15700 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15704 : bv 32 := 0x02013403.
Lemma F_15704 : fetch_word Plain.M.loaded_segments (0x15800 : word) = Some W_15704.
Proof. vm_refl. Qed.
Lemma D_15704 : decode_any W_15704 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15708 : bv 32 := 0x01813483.
Lemma F_15708 : fetch_word Plain.M.loaded_segments (0x15804 : word) = Some W_15708.
Proof. vm_refl. Qed.
Lemma D_15708 : decode_any W_15708 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1570c : bv 32 := 0x01013903.
Lemma F_1570c : fetch_word Plain.M.loaded_segments (0x15808 : word) = Some W_1570c.
Proof. vm_refl. Qed.
Lemma D_1570c : decode_any W_1570c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15710 : bv 32 := 0x00813983.
Lemma F_15710 : fetch_word Plain.M.loaded_segments (0x1580c : word) = Some W_15710.
Proof. vm_refl. Qed.
Lemma D_15710 : decode_any W_15710 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15714 : bv 32 := 0x03010113.
Lemma F_15714 : fetch_word Plain.M.loaded_segments (0x15810 : word) = Some W_15714.
Proof. vm_refl. Qed.
Lemma D_15714 : decode_any W_15714 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15718 : bv 32 := 0x00008067.
Lemma F_15718 : fetch_word Plain.M.loaded_segments (0x15814 : word) = Some W_15718.
Proof. vm_refl. Qed.
Lemma D_15718 : decode_any W_15718 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1571c : bv 32 := 0x06050863.
Lemma F_1571c : fetch_word Plain.M.loaded_segments (0x15818 : word) = Some W_1571c.
Proof. vm_refl. Qed.
Lemma D_1571c : decode_any W_1571c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15720 : bv 32 := 0x0405c063.
Lemma F_15720 : fetch_word Plain.M.loaded_segments (0x1581c : word) = Some W_15720.
Proof. vm_refl. Qed.
Lemma D_15720 : decode_any W_15720 = Some (Branch BC_LT 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15724 : bv 32 := 0x00052683.
Lemma F_15724 : fetch_word Plain.M.loaded_segments (0x15820 : word) = Some W_15724.
Proof. vm_refl. Qed.
Lemma D_15724 : decode_any W_15724 = Some (Load SZ4 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15728 : bv 32 := 0x02d5dc63.
Lemma F_15728 : fetch_word Plain.M.loaded_segments (0x15824 : word) = Some W_15728.
Proof. vm_refl. Qed.
Lemma D_15728 : decode_any W_15728 = Some (Branch BC_GE 11 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1572c : bv 32 := 0x08064663.
Lemma F_1572c : fetch_word Plain.M.loaded_segments (0x15828 : word) = Some W_1572c.
Proof. vm_refl. Qed.
Lemma D_1572c : decode_any W_1572c = Some (Branch BC_LT 12 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15730 : bv 32 := 0x00452683.
Lemma F_15730 : fetch_word Plain.M.loaded_segments (0x1582c : word) = Some W_15730.
Proof. vm_refl. Qed.
Lemma D_15730 : decode_any W_15730 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15734 : bv 32 := 0x08d65263.
Lemma F_15734 : fetch_word Plain.M.loaded_segments (0x15830 : word) = Some W_15734.
Proof. vm_refl. Qed.
Lemma D_15734 : decode_any W_15734 = Some (Branch BC_GE 12 13 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15738 : bv 32 := 0x00050693.
Lemma F_15738 : fetch_word Plain.M.loaded_segments (0x15834 : word) = Some W_15738.
Proof. vm_refl. Qed.
Lemma D_15738 : decode_any W_15738 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1573c : bv 32 := 0x00000513.
Lemma F_1573c : fetch_word Plain.M.loaded_segments (0x15838 : word) = Some W_1573c.
Proof. vm_refl. Qed.
Lemma D_1573c : decode_any W_1573c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15740 : bv 32 := 0x0106b683.
Lemma F_15740 : fetch_word Plain.M.loaded_segments (0x1583c : word) = Some W_15740.
Proof. vm_refl. Qed.
Lemma D_15740 : decode_any W_15740 = Some (Load SZ8 true 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15744 : bv 32 := 0x00359593.
Lemma F_15744 : fetch_word Plain.M.loaded_segments (0x15840 : word) = Some W_15744.
Proof. vm_refl. Qed.
Lemma D_15744 : decode_any W_15744 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15748 : bv 32 := 0x00b685b3.
Lemma F_15748 : fetch_word Plain.M.loaded_segments (0x15844 : word) = Some W_15748.
Proof. vm_refl. Qed.
Lemma D_15748 : decode_any W_15748 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1574c : bv 32 := 0x0005b583.
Lemma F_1574c : fetch_word Plain.M.loaded_segments (0x15848 : word) = Some W_1574c.
Proof. vm_refl. Qed.
Lemma D_1574c : decode_any W_1574c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15750 : bv 32 := 0x00261613.
Lemma F_15750 : fetch_word Plain.M.loaded_segments (0x1584c : word) = Some W_15750.
Proof. vm_refl. Qed.
Lemma D_15750 : decode_any W_15750 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15754 : bv 32 := 0x00c585b3.
Lemma F_15754 : fetch_word Plain.M.loaded_segments (0x15850 : word) = Some W_15754.
Proof. vm_refl. Qed.
Lemma D_15754 : decode_any W_15754 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15758 : bv 32 := 0x00a5a027.
Lemma F_15758 : fetch_word Plain.M.loaded_segments (0x15854 : word) = Some W_15758.
Proof. vm_refl. Qed.
Lemma D_15758 : decode_any W_15758 = Some (FStore FMT_S 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1575c : bv 32 := 0x00008067.
Lemma F_1575c : fetch_word Plain.M.loaded_segments (0x15858 : word) = Some W_1575c.
Proof. vm_refl. Qed.
Lemma D_1575c : decode_any W_1575c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1578c : bv 32 := 0x0000a517.
Lemma F_1578c : fetch_word Plain.M.loaded_segments (0x15888 : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15790 : bv 32 := 0x8c853503.
Lemma F_15790 : fetch_word Plain.M.loaded_segments (0x1588c : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (Load SZ8 true 10 10 2248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15794 : bv 32 := 0x00052503.
Lemma F_15794 : fetch_word Plain.M.loaded_segments (0x15890 : word) = Some W_15794.
Proof. vm_refl. Qed.
Lemma D_15794 : decode_any W_15794 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15798 : bv 32 := 0x00500593.
Lemma F_15798 : fetch_word Plain.M.loaded_segments (0x15894 : word) = Some W_15798.
Proof. vm_refl. Qed.
Lemma D_15798 : decode_any W_15798 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1579c : bv 32 := 0x04a5c463.
Lemma F_1579c : fetch_word Plain.M.loaded_segments (0x15898 : word) = Some W_1579c.
Proof. vm_refl. Qed.
Lemma D_1579c : decode_any W_1579c = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a0 : bv 32 := 0xffffb517.
Lemma F_157a0 : fetch_word Plain.M.loaded_segments (0x1589c : word) = Some W_157a0.
Proof. vm_refl. Qed.
Lemma D_157a0 : decode_any W_157a0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a4 : bv 32 := 0xffffb597.
Lemma F_157a4 : fetch_word Plain.M.loaded_segments (0x158a0 : word) = Some W_157a4.
Proof. vm_refl. Qed.
Lemma D_157a4 : decode_any W_157a4 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a8 : bv 32 := 0xb4c50513.
Lemma F_157a8 : fetch_word Plain.M.loaded_segments (0x158a4 : word) = Some W_157a8.
Proof. vm_refl. Qed.
Lemma D_157a8 : decode_any W_157a8 = Some (OpImm ALU_ADD 10 10 2892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ac : bv 32 := 0xcac58593.
Lemma F_157ac : fetch_word Plain.M.loaded_segments (0x158a8 : word) = Some W_157ac.
Proof. vm_refl. Qed.
Lemma D_157ac : decode_any W_157ac = Some (OpImm ALU_ADD 11 11 3244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b0 : bv 32 := 0x00100613.
Lemma F_157b0 : fetch_word Plain.M.loaded_segments (0x158ac : word) = Some W_157b0.
Proof. vm_refl. Qed.
Lemma D_157b0 : decode_any W_157b0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b4 : bv 32 := 0x920fe06f.
Lemma F_157b4 : fetch_word Plain.M.loaded_segments (0x158b0 : word) = Some W_157b4.
Proof. vm_refl. Qed.
Lemma D_157b4 : decode_any W_157b4 = Some (Jal 0 2089248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ec : bv 32 := 0xfc010113.
Lemma F_157ec : fetch_word Plain.M.loaded_segments (0x158e8 : word) = Some W_157ec.
Proof. vm_refl. Qed.
Lemma D_157ec : decode_any W_157ec = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f0 : bv 32 := 0x02113c23.
Lemma F_157f0 : fetch_word Plain.M.loaded_segments (0x158ec : word) = Some W_157f0.
Proof. vm_refl. Qed.
Lemma D_157f0 : decode_any W_157f0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f4 : bv 32 := 0x02813823.
Lemma F_157f4 : fetch_word Plain.M.loaded_segments (0x158f0 : word) = Some W_157f4.
Proof. vm_refl. Qed.
Lemma D_157f4 : decode_any W_157f4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f8 : bv 32 := 0x02913423.
Lemma F_157f8 : fetch_word Plain.M.loaded_segments (0x158f4 : word) = Some W_157f8.
Proof. vm_refl. Qed.
Lemma D_157f8 : decode_any W_157f8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157fc : bv 32 := 0x03213023.
Lemma F_157fc : fetch_word Plain.M.loaded_segments (0x158f8 : word) = Some W_157fc.
Proof. vm_refl. Qed.
Lemma D_157fc : decode_any W_157fc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15800 : bv 32 := 0x01313c23.
Lemma F_15800 : fetch_word Plain.M.loaded_segments (0x158fc : word) = Some W_15800.
Proof. vm_refl. Qed.
Lemma D_15800 : decode_any W_15800 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15804 : bv 32 := 0x04050e63.
Lemma F_15804 : fetch_word Plain.M.loaded_segments (0x15900 : word) = Some W_15804.
Proof. vm_refl. Qed.
Lemma D_15804 : decode_any W_15804 = Some (Branch BC_EQ 10 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15808 : bv 32 := 0x00060913.
Lemma F_15808 : fetch_word Plain.M.loaded_segments (0x15904 : word) = Some W_15808.
Proof. vm_refl. Qed.
Lemma D_15808 : decode_any W_15808 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1580c : bv 32 := 0x00058993.
Lemma F_1580c : fetch_word Plain.M.loaded_segments (0x15908 : word) = Some W_1580c.
Proof. vm_refl. Qed.
Lemma D_1580c : decode_any W_1580c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15810 : bv 32 := 0x00050413.
Lemma F_15810 : fetch_word Plain.M.loaded_segments (0x1590c : word) = Some W_15810.
Proof. vm_refl. Qed.
Lemma D_15810 : decode_any W_15810 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15814 : bv 32 := 0x01410593.
Lemma F_15814 : fetch_word Plain.M.loaded_segments (0x15910 : word) = Some W_15814.
Proof. vm_refl. Qed.
Lemma D_15814 : decode_any W_15814 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15818 : bv 32 := 0x01010613.
Lemma F_15818 : fetch_word Plain.M.loaded_segments (0x15914 : word) = Some W_15818.
Proof. vm_refl. Qed.
Lemma D_15818 : decode_any W_15818 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1581c : bv 32 := 0x00c10693.
Lemma F_1581c : fetch_word Plain.M.loaded_segments (0x15918 : word) = Some W_1581c.
Proof. vm_refl. Qed.
Lemma D_1581c : decode_any W_1581c = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15820 : bv 32 := 0xfb8fe0ef.
Lemma F_15820 : fetch_word Plain.M.loaded_segments (0x1591c : word) = Some W_15820.
Proof. vm_refl. Qed.
Lemma D_15820 : decode_any W_15820 = Some (Jal 1 2090936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15824 : bv 32 := 0x00c12503.
Lemma F_15824 : fetch_word Plain.M.loaded_segments (0x15920 : word) = Some W_15824.
Proof. vm_refl. Qed.
Lemma D_15824 : decode_any W_15824 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15828 : bv 32 := 0x00800593.
Lemma F_15828 : fetch_word Plain.M.loaded_segments (0x15924 : word) = Some W_15828.
Proof. vm_refl. Qed.
Lemma D_15828 : decode_any W_15828 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1582c : bv 32 := 0x06b51c63.
Lemma F_1582c : fetch_word Plain.M.loaded_segments (0x15928 : word) = Some W_1582c.
Proof. vm_refl. Qed.
Lemma D_1582c : decode_any W_1582c = Some (Branch BC_NE 10 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15830 : bv 32 := 0x01396533.
Lemma F_15830 : fetch_word Plain.M.loaded_segments (0x1592c : word) = Some W_15830.
Proof. vm_refl. Qed.
Lemma D_15830 : decode_any W_15830 = Some (Op ALU_OR 10 18 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15834 : bv 32 := 0x08054c63.
Lemma F_15834 : fetch_word Plain.M.loaded_segments (0x15930 : word) = Some W_15834.
Proof. vm_refl. Qed.
Lemma D_15834 : decode_any W_15834 = Some (Branch BC_LT 10 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15838 : bv 32 := 0x01012503.
Lemma F_15838 : fetch_word Plain.M.loaded_segments (0x15934 : word) = Some W_15838.
Proof. vm_refl. Qed.
Lemma D_15838 : decode_any W_15838 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1583c : bv 32 := 0x08a9d863.
Lemma F_1583c : fetch_word Plain.M.loaded_segments (0x15938 : word) = Some W_1583c.
Proof. vm_refl. Qed.
Lemma D_1583c : decode_any W_1583c = Some (Branch BC_GE 19 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15840 : bv 32 := 0x01412583.
Lemma F_15840 : fetch_word Plain.M.loaded_segments (0x1593c : word) = Some W_15840.
Proof. vm_refl. Qed.
Lemma D_15840 : decode_any W_15840 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15844 : bv 32 := 0x08b95463.
Lemma F_15844 : fetch_word Plain.M.loaded_segments (0x15940 : word) = Some W_15844.
Proof. vm_refl. Qed.
Lemma D_15844 : decode_any W_15844 = Some (Branch BC_GE 18 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15848 : bv 32 := 0xbe5ff0ef.
Lemma F_15848 : fetch_word Plain.M.loaded_segments (0x15944 : word) = Some W_15848.
Proof. vm_refl. Qed.
Lemma D_15848 : decode_any W_15848 = Some (Jal 1 2096100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1584c : bv 32 := 0x00050493.
Lemma F_1584c : fetch_word Plain.M.loaded_segments (0x15948 : word) = Some W_1584c.
Proof. vm_refl. Qed.
Lemma D_1584c : decode_any W_1584c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850 : bv 32 := 0x0c050a63.
Lemma F_15850 : fetch_word Plain.M.loaded_segments (0x1594c : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854 : bv 32 := 0x0134a423.
Lemma F_15854 : fetch_word Plain.M.loaded_segments (0x15950 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (Store SZ4 9 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15858 : bv 32 := 0x0124a623.
Lemma F_15858 : fetch_word Plain.M.loaded_segments (0x15954 : word) = Some W_15858.
Proof. vm_refl. Qed.
Lemma D_15858 : decode_any W_15858 = Some (Store SZ4 9 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c : bv 32 := 0x0f40006f.
Lemma F_1585c : fetch_word Plain.M.loaded_segments (0x15958 : word) = Some W_1585c.
Proof. vm_refl. Qed.
Lemma D_1585c : decode_any W_1585c = Some (Jal 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a4 : bv 32 := 0x00009517.
Lemma F_158a4 : fetch_word Plain.M.loaded_segments (0x159a0 : word) = Some W_158a4.
Proof. vm_refl. Qed.
Lemma D_158a4 : decode_any W_158a4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a8 : bv 32 := 0x7b053503.
Lemma F_158a8 : fetch_word Plain.M.loaded_segments (0x159a4 : word) = Some W_158a8.
Proof. vm_refl. Qed.
Lemma D_158a8 : decode_any W_158a8 = Some (Load SZ8 true 10 10 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ac : bv 32 := 0x00052503.
Lemma F_158ac : fetch_word Plain.M.loaded_segments (0x159a8 : word) = Some W_158ac.
Proof. vm_refl. Qed.
Lemma D_158ac : decode_any W_158ac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b0 : bv 32 := 0x00500593.
Lemma F_158b0 : fetch_word Plain.M.loaded_segments (0x159ac : word) = Some W_158b0.
Proof. vm_refl. Qed.
Lemma D_158b0 : decode_any W_158b0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b4 : bv 32 := 0x04a5c663.
Lemma F_158b4 : fetch_word Plain.M.loaded_segments (0x159b0 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (Branch BC_LT 11 10 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b8 : bv 32 := 0xffffb517.
Lemma F_158b8 : fetch_word Plain.M.loaded_segments (0x159b4 : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158bc : bv 32 := 0xffffb597.
Lemma F_158bc : fetch_word Plain.M.loaded_segments (0x159b8 : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c0 : bv 32 := 0x1ec50513.
Lemma F_158c0 : fetch_word Plain.M.loaded_segments (0x159bc : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (OpImm ALU_ADD 10 10 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c4 : bv 32 := 0x15f58593.
Lemma F_158c4 : fetch_word Plain.M.loaded_segments (0x159c0 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (OpImm ALU_ADD 11 11 351, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c8 : bv 32 := 0x0280006f.
Lemma F_158c8 : fetch_word Plain.M.loaded_segments (0x159c4 : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158cc : bv 32 := 0x00009517.
Lemma F_158cc : fetch_word Plain.M.loaded_segments (0x159c8 : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d0 : bv 32 := 0x78853503.
Lemma F_158d0 : fetch_word Plain.M.loaded_segments (0x159cc : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (Load SZ8 true 10 10 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d4 : bv 32 := 0x00052503.
Lemma F_158d4 : fetch_word Plain.M.loaded_segments (0x159d0 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d8 : bv 32 := 0x00500593.
Lemma F_158d8 : fetch_word Plain.M.loaded_segments (0x159d4 : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158dc : bv 32 := 0x02a5c263.
Lemma F_158dc : fetch_word Plain.M.loaded_segments (0x159d8 : word) = Some W_158dc.
Proof. vm_refl. Qed.
Lemma D_158dc : decode_any W_158dc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e0 : bv 32 := 0xffffb517.
Lemma F_158e0 : fetch_word Plain.M.loaded_segments (0x159dc : word) = Some W_158e0.
Proof. vm_refl. Qed.
Lemma D_158e0 : decode_any W_158e0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e4 : bv 32 := 0xffffb597.
Lemma F_158e4 : fetch_word Plain.M.loaded_segments (0x159e0 : word) = Some W_158e4.
Proof. vm_refl. Qed.
Lemma D_158e4 : decode_any W_158e4 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e8 : bv 32 := 0x09850513.
Lemma F_158e8 : fetch_word Plain.M.loaded_segments (0x159e4 : word) = Some W_158e8.
Proof. vm_refl. Qed.
Lemma D_158e8 : decode_any W_158e8 = Some (OpImm ALU_ADD 10 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ec : bv 32 := 0x13758593.
Lemma F_158ec : fetch_word Plain.M.loaded_segments (0x159e8 : word) = Some W_158ec.
Proof. vm_refl. Qed.
Lemma D_158ec : decode_any W_158ec = Some (OpImm ALU_ADD 11 11 311, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f0 : bv 32 := 0x00000613.
Lemma F_158f0 : fetch_word Plain.M.loaded_segments (0x159ec : word) = Some W_158f0.
Proof. vm_refl. Qed.
Lemma D_158f0 : decode_any W_158f0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f4 : bv 32 := 0x8b0fe0ef.
Lemma F_158f4 : fetch_word Plain.M.loaded_segments (0x159f0 : word) = Some W_158f4.
Proof. vm_refl. Qed.
Lemma D_158f4 : decode_any W_158f4 = Some (Jal 1 2089136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f8 : bv 32 := 0x00050493.
Lemma F_158f8 : fetch_word Plain.M.loaded_segments (0x159f4 : word) = Some W_158f8.
Proof. vm_refl. Qed.
Lemma D_158f8 : decode_any W_158f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158fc : bv 32 := 0x0080006f.
Lemma F_158fc : fetch_word Plain.M.loaded_segments (0x159f8 : word) = Some W_158fc.
Proof. vm_refl. Qed.
Lemma D_158fc : decode_any W_158fc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15904 : bv 32 := 0x00048513.
Lemma F_15904 : fetch_word Plain.M.loaded_segments (0x15a00 : word) = Some W_15904.
Proof. vm_refl. Qed.
Lemma D_15904 : decode_any W_15904 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15908 : bv 32 := 0x03813083.
Lemma F_15908 : fetch_word Plain.M.loaded_segments (0x15a04 : word) = Some W_15908.
Proof. vm_refl. Qed.
Lemma D_15908 : decode_any W_15908 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590c : bv 32 := 0x03013403.
Lemma F_1590c : fetch_word Plain.M.loaded_segments (0x15a08 : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15910 : bv 32 := 0x02813483.
Lemma F_15910 : fetch_word Plain.M.loaded_segments (0x15a0c : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15914 : bv 32 := 0x02013903.
Lemma F_15914 : fetch_word Plain.M.loaded_segments (0x15a10 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15918 : bv 32 := 0x01813983.
Lemma F_15918 : fetch_word Plain.M.loaded_segments (0x15a14 : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1591c : bv 32 := 0x04010113.
Lemma F_1591c : fetch_word Plain.M.loaded_segments (0x15a18 : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15920 : bv 32 := 0x00008067.
Lemma F_15920 : fetch_word Plain.M.loaded_segments (0x15a1c : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15924 : bv 32 := 0x00009517.
Lemma F_15924 : fetch_word Plain.M.loaded_segments (0x15a20 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15928 : bv 32 := 0x73053503.
Lemma F_15928 : fetch_word Plain.M.loaded_segments (0x15a24 : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (Load SZ8 true 10 10 1840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1592c : bv 32 := 0x00052503.
Lemma F_1592c : fetch_word Plain.M.loaded_segments (0x15a28 : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15930 : bv 32 := 0x00500593.
Lemma F_15930 : fetch_word Plain.M.loaded_segments (0x15a2c : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15934 : bv 32 := 0x00a5ce63.
Lemma F_15934 : fetch_word Plain.M.loaded_segments (0x15a30 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15938 : bv 32 := 0xffffb517.
Lemma F_15938 : fetch_word Plain.M.loaded_segments (0x15a34 : word) = Some W_15938.
Proof. vm_refl. Qed.
Lemma D_15938 : decode_any W_15938 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1593c : bv 32 := 0xffffb597.
Lemma F_1593c : fetch_word Plain.M.loaded_segments (0x15a38 : word) = Some W_1593c.
Proof. vm_refl. Qed.
Lemma D_1593c : decode_any W_1593c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15940 : bv 32 := 0x9b450513.
Lemma F_15940 : fetch_word Plain.M.loaded_segments (0x15a3c : word) = Some W_15940.
Proof. vm_refl. Qed.
Lemma D_15940 : decode_any W_15940 = Some (OpImm ALU_ADD 10 10 2484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15944 : bv 32 := 0xa7358593.
Lemma F_15944 : fetch_word Plain.M.loaded_segments (0x15a40 : word) = Some W_15944.
Proof. vm_refl. Qed.
Lemma D_15944 : decode_any W_15944 = Some (OpImm ALU_ADD 11 11 2675, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15948 : bv 32 := 0x00100613.
Lemma F_15948 : fetch_word Plain.M.loaded_segments (0x15a44 : word) = Some W_15948.
Proof. vm_refl. Qed.
Lemma D_15948 : decode_any W_15948 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1594c : bv 32 := 0xf89fd0ef.
Lemma F_1594c : fetch_word Plain.M.loaded_segments (0x15a48 : word) = Some W_1594c.
Proof. vm_refl. Qed.
Lemma D_1594c : decode_any W_1594c = Some (Jal 1 2088840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15950 : bv 32 := 0x01012503.
Lemma F_15950 : fetch_word Plain.M.loaded_segments (0x15a4c : word) = Some W_15950.
Proof. vm_refl. Qed.
Lemma D_15950 : decode_any W_15950 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15954 : bv 32 := 0xfaa058e3.
Lemma F_15954 : fetch_word Plain.M.loaded_segments (0x15a50 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (Branch BC_GE 0 10 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15958 : bv 32 := 0x01412583.
Lemma F_15958 : fetch_word Plain.M.loaded_segments (0x15a54 : word) = Some W_15958.
Proof. vm_refl. Qed.
Lemma D_15958 : decode_any W_15958 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c : bv 32 := 0x00000913.
Lemma F_1595c : fetch_word Plain.M.loaded_segments (0x15a58 : word) = Some W_1595c.
Proof. vm_refl. Qed.
Lemma D_1595c : decode_any W_1595c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15960 : bv 32 := 0x00c0006f.
Lemma F_15960 : fetch_word Plain.M.loaded_segments (0x15a5c : word) = Some W_15960.
Proof. vm_refl. Qed.
Lemma D_15960 : decode_any W_15960 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15964 : bv 32 := 0x0019091b.
Lemma F_15964 : fetch_word Plain.M.loaded_segments (0x15a60 : word) = Some W_15964.
Proof. vm_refl. Qed.
Lemma D_15964 : decode_any W_15964 = Some (OpImm32 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15968 : bv 32 := 0xf8a95ee3.
Lemma F_15968 : fetch_word Plain.M.loaded_segments (0x15a64 : word) = Some W_15968.
Proof. vm_refl. Qed.
Lemma D_15968 : decode_any W_15968 = Some (Branch BC_GE 18 10 8092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1596c : bv 32 := 0xfeb05ce3.
Lemma F_1596c : fetch_word Plain.M.loaded_segments (0x15a68 : word) = Some W_1596c.
Proof. vm_refl. Qed.
Lemma D_1596c : decode_any W_1596c = Some (Branch BC_GE 0 11 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15970 : bv 32 := 0x00000993.
Lemma F_15970 : fetch_word Plain.M.loaded_segments (0x15a6c : word) = Some W_15970.
Proof. vm_refl. Qed.
Lemma D_15970 : decode_any W_15970 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15974 : bv 32 := 0x00810693.
Lemma F_15974 : fetch_word Plain.M.loaded_segments (0x15a70 : word) = Some W_15974.
Proof. vm_refl. Qed.
Lemma D_15974 : decode_any W_15974 = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15978 : bv 32 := 0x00040513.
Lemma F_15978 : fetch_word Plain.M.loaded_segments (0x15a74 : word) = Some W_15978.
Proof. vm_refl. Qed.
Lemma D_15978 : decode_any W_15978 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1597c : bv 32 := 0x00098593.
Lemma F_1597c : fetch_word Plain.M.loaded_segments (0x15a78 : word) = Some W_1597c.
Proof. vm_refl. Qed.
Lemma D_1597c : decode_any W_1597c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15980 : bv 32 := 0x00090613.
Lemma F_15980 : fetch_word Plain.M.loaded_segments (0x15a7c : word) = Some W_15980.
Proof. vm_refl. Qed.
Lemma D_15980 : decode_any W_15980 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15984 : bv 32 := 0x8b9fe0ef.
Lemma F_15984 : fetch_word Plain.M.loaded_segments (0x15a80 : word) = Some W_15984.
Proof. vm_refl. Qed.
Lemma D_15984 : decode_any W_15984 = Some (Jal 1 2091192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15988 : bv 32 := 0x00816503.
Lemma F_15988 : fetch_word Plain.M.loaded_segments (0x15a84 : word) = Some W_15988.
Proof. vm_refl. Qed.
Lemma D_15988 : decode_any W_15988 = Some (Load SZ4 false 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1598c : bv 32 := 0xd0157553.
Lemma F_1598c : fetch_word Plain.M.loaded_segments (0x15a88 : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (Fcvt FC_S FC_WU 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x00048513.
Lemma F_15990 : fetch_word Plain.M.loaded_segments (0x15a8c : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0x00090593.
Lemma F_15994 : fetch_word Plain.M.loaded_segments (0x15a90 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15998 : bv 32 := 0x00098613.
Lemma F_15998 : fetch_word Plain.M.loaded_segments (0x15a94 : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1599c : bv 32 := 0xd81ff0ef.
Lemma F_1599c : fetch_word Plain.M.loaded_segments (0x15a98 : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (Jal 1 2096512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a0 : bv 32 := 0x01412583.
Lemma F_159a0 : fetch_word Plain.M.loaded_segments (0x15a9c : word) = Some W_159a0.
Proof. vm_refl. Qed.
Lemma D_159a0 : decode_any W_159a0 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a4 : bv 32 := 0x0019899b.
Lemma F_159a4 : fetch_word Plain.M.loaded_segments (0x15aa0 : word) = Some W_159a4.
Proof. vm_refl. Qed.
Lemma D_159a4 : decode_any W_159a4 = Some (OpImm32 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a8 : bv 32 := 0xfcb9c6e3.
Lemma F_159a8 : fetch_word Plain.M.loaded_segments (0x15aa4 : word) = Some W_159a8.
Proof. vm_refl. Qed.
Lemma D_159a8 : decode_any W_159a8 = Some (Branch BC_LT 19 11 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ac : bv 32 := 0x01012503.
Lemma F_159ac : fetch_word Plain.M.loaded_segments (0x15aa8 : word) = Some W_159ac.
Proof. vm_refl. Qed.
Lemma D_159ac : decode_any W_159ac = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b0 : bv 32 := 0xfb5ff06f.
Lemma F_159b0 : fetch_word Plain.M.loaded_segments (0x15aac : word) = Some W_159b0.
Proof. vm_refl. Qed.
Lemma D_159b0 : decode_any W_159b0 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.
