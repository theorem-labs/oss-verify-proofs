(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6caa4 : bv 32 := 0x00050663.
Lemma F_6caa4 : fetch_word Plain.M.loaded_segments (0x6cafc : word) = Some W_6caa4.
Proof. vm_refl. Qed.
Lemma D_6caa4 : decode_any W_6caa4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caa8 : bv 32 := 0x01052503.
Lemma F_6caa8 : fetch_word Plain.M.loaded_segments (0x6cb00 : word) = Some W_6caa8.
Proof. vm_refl. Qed.
Lemma D_6caa8 : decode_any W_6caa8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caac : bv 32 := 0x00008067.
Lemma F_6caac : fetch_word Plain.M.loaded_segments (0x6cb04 : word) = Some W_6caac.
Proof. vm_refl. Qed.
Lemma D_6caac : decode_any W_6caac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda0 : bv 32 := 0x00058463.
Lemma F_6cda0 : fetch_word Plain.M.loaded_segments (0x6cdf8 : word) = Some W_6cda0.
Proof. vm_refl. Qed.
Lemma D_6cda0 : decode_any W_6cda0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda4 : bv 32 := 0x0005a023.
Lemma F_6cda4 : fetch_word Plain.M.loaded_segments (0x6cdfc : word) = Some W_6cda4.
Proof. vm_refl. Qed.
Lemma D_6cda4 : decode_any W_6cda4 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda8 : bv 32 := 0x00060463.
Lemma F_6cda8 : fetch_word Plain.M.loaded_segments (0x6ce00 : word) = Some W_6cda8.
Proof. vm_refl. Qed.
Lemma D_6cda8 : decode_any W_6cda8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdac : bv 32 := 0x00062023.
Lemma F_6cdac : fetch_word Plain.M.loaded_segments (0x6ce04 : word) = Some W_6cdac.
Proof. vm_refl. Qed.
Lemma D_6cdac : decode_any W_6cdac = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb0 : bv 32 := 0x00068463.
Lemma F_6cdb0 : fetch_word Plain.M.loaded_segments (0x6ce08 : word) = Some W_6cdb0.
Proof. vm_refl. Qed.
Lemma D_6cdb0 : decode_any W_6cdb0 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb8 : bv 32 := 0x02050a63.
Lemma F_6cdb8 : fetch_word Plain.M.loaded_segments (0x6ce10 : word) = Some W_6cdb8.
Proof. vm_refl. Qed.
Lemma D_6cdb8 : decode_any W_6cdb8 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdbc : bv 32 := 0x00058663.
Lemma F_6cdbc : fetch_word Plain.M.loaded_segments (0x6ce14 : word) = Some W_6cdbc.
Proof. vm_refl. Qed.
Lemma D_6cdbc : decode_any W_6cdbc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc0 : bv 32 := 0x00052703.
Lemma F_6cdc0 : fetch_word Plain.M.loaded_segments (0x6ce18 : word) = Some W_6cdc0.
Proof. vm_refl. Qed.
Lemma D_6cdc0 : decode_any W_6cdc0 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc4 : bv 32 := 0x00e5a023.
Lemma F_6cdc4 : fetch_word Plain.M.loaded_segments (0x6ce1c : word) = Some W_6cdc4.
Proof. vm_refl. Qed.
Lemma D_6cdc4 : decode_any W_6cdc4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc8 : bv 32 := 0x00060663.
Lemma F_6cdc8 : fetch_word Plain.M.loaded_segments (0x6ce20 : word) = Some W_6cdc8.
Proof. vm_refl. Qed.
Lemma D_6cdc8 : decode_any W_6cdc8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdcc : bv 32 := 0x00452583.
Lemma F_6cdcc : fetch_word Plain.M.loaded_segments (0x6ce24 : word) = Some W_6cdcc.
Proof. vm_refl. Qed.
Lemma D_6cdcc : decode_any W_6cdcc = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd0 : bv 32 := 0x00b62023.
Lemma F_6cdd0 : fetch_word Plain.M.loaded_segments (0x6ce28 : word) = Some W_6cdd0.
Proof. vm_refl. Qed.
Lemma D_6cdd0 : decode_any W_6cdd0 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd4 : bv 32 := 0x00000593.
Lemma F_6cdd4 : fetch_word Plain.M.loaded_segments (0x6ce2c : word) = Some W_6cdd4.
Proof. vm_refl. Qed.
Lemma D_6cdd4 : decode_any W_6cdd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd8 : bv 32 := 0x00068663.
Lemma F_6cdd8 : fetch_word Plain.M.loaded_segments (0x6ce30 : word) = Some W_6cdd8.
Proof. vm_refl. Qed.
Lemma D_6cdd8 : decode_any W_6cdd8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde4 : bv 32 := 0x00058513.
Lemma F_6cde4 : fetch_word Plain.M.loaded_segments (0x6ce3c : word) = Some W_6cde4.
Proof. vm_refl. Qed.
Lemma D_6cde4 : decode_any W_6cde4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde8 : bv 32 := 0x00008067.
Lemma F_6cde8 : fetch_word Plain.M.loaded_segments (0x6ce40 : word) = Some W_6cde8.
Proof. vm_refl. Qed.
Lemma D_6cde8 : decode_any W_6cde8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9e8 : bv 32 := 0x00050663.
Lemma F_6d9e8 : fetch_word Plain.M.loaded_segments (0x6da40 : word) = Some W_6d9e8.
Proof. vm_refl. Qed.
Lemma D_6d9e8 : decode_any W_6d9e8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9ec : bv 32 := 0x03853503.
Lemma F_6d9ec : fetch_word Plain.M.loaded_segments (0x6da44 : word) = Some W_6d9ec.
Proof. vm_refl. Qed.
Lemma D_6d9ec : decode_any W_6d9ec = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9f0 : bv 32 := 0x00008067.
Lemma F_6d9f0 : fetch_word Plain.M.loaded_segments (0x6da48 : word) = Some W_6d9f0.
Proof. vm_refl. Qed.
Lemma D_6d9f0 : decode_any W_6d9f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f60 : bv 32 := 0xfc010113.
Lemma F_78f60 : fetch_word Plain.M.loaded_segments (0x78fb8 : word) = Some W_78f60.
Proof. vm_refl. Qed.
Lemma D_78f60 : decode_any W_78f60 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f64 : bv 32 := 0x02113c23.
Lemma F_78f64 : fetch_word Plain.M.loaded_segments (0x78fbc : word) = Some W_78f64.
Proof. vm_refl. Qed.
Lemma D_78f64 : decode_any W_78f64 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f68 : bv 32 := 0x02813823.
Lemma F_78f68 : fetch_word Plain.M.loaded_segments (0x78fc0 : word) = Some W_78f68.
Proof. vm_refl. Qed.
Lemma D_78f68 : decode_any W_78f68 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f6c : bv 32 := 0x02913423.
Lemma F_78f6c : fetch_word Plain.M.loaded_segments (0x78fc4 : word) = Some W_78f6c.
Proof. vm_refl. Qed.
Lemma D_78f6c : decode_any W_78f6c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f70 : bv 32 := 0x03213023.
Lemma F_78f70 : fetch_word Plain.M.loaded_segments (0x78fc8 : word) = Some W_78f70.
Proof. vm_refl. Qed.
Lemma D_78f70 : decode_any W_78f70 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f74 : bv 32 := 0x01313c23.
Lemma F_78f74 : fetch_word Plain.M.loaded_segments (0x78fcc : word) = Some W_78f74.
Proof. vm_refl. Qed.
Lemma D_78f74 : decode_any W_78f74 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f78 : bv 32 := 0x01413823.
Lemma F_78f78 : fetch_word Plain.M.loaded_segments (0x78fd0 : word) = Some W_78f78.
Proof. vm_refl. Qed.
Lemma D_78f78 : decode_any W_78f78 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f7c : bv 32 := 0x24058463.
Lemma F_78f7c : fetch_word Plain.M.loaded_segments (0x78fd4 : word) = Some W_78f7c.
Proof. vm_refl. Qed.
Lemma D_78f7c : decode_any W_78f7c = Some (Branch BC_EQ 11 0 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f80 : bv 32 := 0x00058493.
Lemma F_78f80 : fetch_word Plain.M.loaded_segments (0x78fd8 : word) = Some W_78f80.
Proof. vm_refl. Qed.
Lemma D_78f80 : decode_any W_78f80 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f84 : bv 32 := 0x00050993.
Lemma F_78f84 : fetch_word Plain.M.loaded_segments (0x78fdc : word) = Some W_78f84.
Proof. vm_refl. Qed.
Lemma D_78f84 : decode_any W_78f84 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f88 : bv 32 := 0x0005a023.
Lemma F_78f88 : fetch_word Plain.M.loaded_segments (0x78fe0 : word) = Some W_78f88.
Proof. vm_refl. Qed.
Lemma D_78f88 : decode_any W_78f88 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f8c : bv 32 := 0x20050863.
Lemma F_78f8c : fetch_word Plain.M.loaded_segments (0x78fe4 : word) = Some W_78f8c.
Proof. vm_refl. Qed.
Lemma D_78f8c : decode_any W_78f8c = Some (Branch BC_EQ 10 0 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f90 : bv 32 := 0x00060413.
Lemma F_78f90 : fetch_word Plain.M.loaded_segments (0x78fe8 : word) = Some W_78f90.
Proof. vm_refl. Qed.
Lemma D_78f90 : decode_any W_78f90 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f94 : bv 32 := 0x00098513.
Lemma F_78f94 : fetch_word Plain.M.loaded_segments (0x78fec : word) = Some W_78f94.
Proof. vm_refl. Qed.
Lemma D_78f94 : decode_any W_78f94 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f98 : bv 32 := 0x991f40ef.
Lemma F_78f98 : fetch_word Plain.M.loaded_segments (0x78ff0 : word) = Some W_78f98.
Proof. vm_refl. Qed.
Lemma D_78f98 : decode_any W_78f98 = Some (Jal 1 2050448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f9c : bv 32 := 0x00100593.
Lemma F_78f9c : fetch_word Plain.M.loaded_segments (0x78ff4 : word) = Some W_78f9c.
Proof. vm_refl. Qed.
Lemma D_78f9c : decode_any W_78f9c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fa0 : bv 32 := 0x1eb51e63.
Lemma F_78fa0 : fetch_word Plain.M.loaded_segments (0x78ff8 : word) = Some W_78fa0.
Proof. vm_refl. Qed.
Lemma D_78fa0 : decode_any W_78fa0 = Some (Branch BC_NE 10 11 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fa4 : bv 32 := 0x00040913.
Lemma F_78fa4 : fetch_word Plain.M.loaded_segments (0x78ffc : word) = Some W_78fa4.
Proof. vm_refl. Qed.
Lemma D_78fa4 : decode_any W_78fa4 = Some (OpImm ALU_ADD 18 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fa8 : bv 32 := 0x08041263.
Lemma F_78fa8 : fetch_word Plain.M.loaded_segments (0x79000 : word) = Some W_78fa8.
Proof. vm_refl. Qed.
Lemma D_78fa8 : decode_any W_78fa8 = Some (Branch BC_NE 8 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fac : bv 32 := 0x10000513.
Lemma F_78fac : fetch_word Plain.M.loaded_segments (0x79004 : word) = Some W_78fac.
Proof. vm_refl. Qed.
Lemma D_78fac : decode_any W_78fac = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fb0 : bv 32 := 0x00400593.
Lemma F_78fb0 : fetch_word Plain.M.loaded_segments (0x79008 : word) = Some W_78fb0.
Proof. vm_refl. Qed.
Lemma D_78fb0 : decode_any W_78fb0 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fb4 : bv 32 := 0x230810ef.
Lemma F_78fb4 : fetch_word Plain.M.loaded_segments (0x7900c : word) = Some W_78fb4.
Proof. vm_refl. Qed.
Lemma D_78fb4 : decode_any W_78fb4 = Some (Jal 1 528944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fb8 : bv 32 := 0x00050913.
Lemma F_78fb8 : fetch_word Plain.M.loaded_segments (0x79010 : word) = Some W_78fb8.
Proof. vm_refl. Qed.
Lemma D_78fb8 : decode_any W_78fb8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fbc : bv 32 := 0x00000513.
Lemma F_78fbc : fetch_word Plain.M.loaded_segments (0x79014 : word) = Some W_78fbc.
Proof. vm_refl. Qed.
Lemma D_78fbc : decode_any W_78fbc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fc0 : bv 32 := 0x40090593.
Lemma F_78fc0 : fetch_word Plain.M.loaded_segments (0x79018 : word) = Some W_78fc0.
Proof. vm_refl. Qed.
Lemma D_78fc0 : decode_any W_78fc0 = Some (OpImm ALU_ADD 11 18 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fc4 : bv 32 := 0x00090613.
Lemma F_78fc4 : fetch_word Plain.M.loaded_segments (0x7901c : word) = Some W_78fc4.
Proof. vm_refl. Qed.
Lemma D_78fc4 : decode_any W_78fc4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fc8 : bv 32 := 0x00157693.
Lemma F_78fc8 : fetch_word Plain.M.loaded_segments (0x79020 : word) = Some W_78fc8.
Proof. vm_refl. Qed.
Lemma D_78fc8 : decode_any W_78fc8 = Some (OpImm ALU_AND 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fcc : bv 32 := 0x03e51713.
Lemma F_78fcc : fetch_word Plain.M.loaded_segments (0x79024 : word) = Some W_78fcc.
Proof. vm_refl. Qed.
Lemma D_78fcc : decode_any W_78fcc = Some (ShiftImm ALU_SLL 14 10 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fd0 : bv 32 := 0x03d51793.
Lemma F_78fd0 : fetch_word Plain.M.loaded_segments (0x79028 : word) = Some W_78fd0.
Proof. vm_refl. Qed.
Lemma D_78fd0 : decode_any W_78fd0 = Some (ShiftImm ALU_SLL 15 10 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fd4 : bv 32 := 0x03c51813.
Lemma F_78fd4 : fetch_word Plain.M.loaded_segments (0x7902c : word) = Some W_78fd4.
Proof. vm_refl. Qed.
Lemma D_78fd4 : decode_any W_78fd4 = Some (ShiftImm ALU_SLL 16 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fd8 : bv 32 := 0x03b51893.
Lemma F_78fd8 : fetch_word Plain.M.loaded_segments (0x79030 : word) = Some W_78fd8.
Proof. vm_refl. Qed.
Lemma D_78fd8 : decode_any W_78fd8 = Some (ShiftImm ALU_SLL 17 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fdc : bv 32 := 0x03a51293.
Lemma F_78fdc : fetch_word Plain.M.loaded_segments (0x79034 : word) = Some W_78fdc.
Proof. vm_refl. Qed.
Lemma D_78fdc : decode_any W_78fdc = Some (ShiftImm ALU_SLL 5 10 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fe0 : bv 32 := 0x03951313.
Lemma F_78fe0 : fetch_word Plain.M.loaded_segments (0x79038 : word) = Some W_78fe0.
Proof. vm_refl. Qed.
Lemma D_78fe0 : decode_any W_78fe0 = Some (ShiftImm ALU_SLL 6 10 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fe4 : bv 32 := 0x0075539b.
Lemma F_78fe4 : fetch_word Plain.M.loaded_segments (0x7903c : word) = Some W_78fe4.
Proof. vm_refl. Qed.
Lemma D_78fe4 : decode_any W_78fe4 = Some (ShiftImm32 ALU_SRL 7 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fe8 : bv 32 := 0x03f75713.
Lemma F_78fe8 : fetch_word Plain.M.loaded_segments (0x79040 : word) = Some W_78fe8.
Proof. vm_refl. Qed.
Lemma D_78fe8 : decode_any W_78fe8 = Some (ShiftImm ALU_SRL 14 14 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78fec : bv 32 := 0x03f7d793.
Lemma F_78fec : fetch_word Plain.M.loaded_segments (0x79044 : word) = Some W_78fec.
Proof. vm_refl. Qed.
Lemma D_78fec : decode_any W_78fec = Some (ShiftImm ALU_SRL 15 15 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ff0 : bv 32 := 0x03f85813.
Lemma F_78ff0 : fetch_word Plain.M.loaded_segments (0x79048 : word) = Some W_78ff0.
Proof. vm_refl. Qed.
Lemma D_78ff0 : decode_any W_78ff0 = Some (ShiftImm ALU_SRL 16 16 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ff4 : bv 32 := 0x03f8d893.
Lemma F_78ff4 : fetch_word Plain.M.loaded_segments (0x7904c : word) = Some W_78ff4.
Proof. vm_refl. Qed.
Lemma D_78ff4 : decode_any W_78ff4 = Some (ShiftImm ALU_SRL 17 17 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ff8 : bv 32 := 0x03f2d293.
Lemma F_78ff8 : fetch_word Plain.M.loaded_segments (0x79050 : word) = Some W_78ff8.
Proof. vm_refl. Qed.
Lemma D_78ff8 : decode_any W_78ff8 = Some (ShiftImm ALU_SRL 5 5 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ffc : bv 32 := 0x03f35313.
Lemma F_78ffc : fetch_word Plain.M.loaded_segments (0x79054 : word) = Some W_78ffc.
Proof. vm_refl. Qed.
Lemma D_78ffc : decode_any W_78ffc = Some (ShiftImm ALU_SRL 6 6 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79000 : bv 32 := 0x00d386b3.
Lemma F_79000 : fetch_word Plain.M.loaded_segments (0x79058 : word) = Some W_79000.
Proof. vm_refl. Qed.
Lemma D_79000 : decode_any W_79000 = Some (Op ALU_ADD 13 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79004 : bv 32 := 0x00e686b3.
Lemma F_79004 : fetch_word Plain.M.loaded_segments (0x7905c : word) = Some W_79004.
Proof. vm_refl. Qed.
Lemma D_79004 : decode_any W_79004 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79008 : bv 32 := 0x010787b3.
Lemma F_79008 : fetch_word Plain.M.loaded_segments (0x79060 : word) = Some W_79008.
Proof. vm_refl. Qed.
Lemma D_79008 : decode_any W_79008 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7900c : bv 32 := 0x005888b3.
Lemma F_7900c : fetch_word Plain.M.loaded_segments (0x79064 : word) = Some W_7900c.
Proof. vm_refl. Qed.
Lemma D_7900c : decode_any W_7900c = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79010 : bv 32 := 0x00f686b3.
Lemma F_79010 : fetch_word Plain.M.loaded_segments (0x79068 : word) = Some W_79010.
Proof. vm_refl. Qed.
Lemma D_79010 : decode_any W_79010 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79014 : bv 32 := 0x006888b3.
Lemma F_79014 : fetch_word Plain.M.loaded_segments (0x7906c : word) = Some W_79014.
Proof. vm_refl. Qed.
Lemma D_79014 : decode_any W_79014 = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79018 : bv 32 := 0x011686b3.
Lemma F_79018 : fetch_word Plain.M.loaded_segments (0x79070 : word) = Some W_79018.
Proof. vm_refl. Qed.
Lemma D_79018 : decode_any W_79018 = Some (Op ALU_ADD 13 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7901c : bv 32 := 0x00d62023.
Lemma F_7901c : fetch_word Plain.M.loaded_segments (0x79074 : word) = Some W_7901c.
Proof. vm_refl. Qed.
Lemma D_7901c : decode_any W_7901c = Some (Store SZ4 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79020 : bv 32 := 0x00460613.
Lemma F_79020 : fetch_word Plain.M.loaded_segments (0x79078 : word) = Some W_79020.
Proof. vm_refl. Qed.
Lemma D_79020 : decode_any W_79020 = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79024 : bv 32 := 0x00150513.
Lemma F_79024 : fetch_word Plain.M.loaded_segments (0x7907c : word) = Some W_79024.
Proof. vm_refl. Qed.
Lemma D_79024 : decode_any W_79024 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79028 : bv 32 := 0xfab610e3.
Lemma F_79028 : fetch_word Plain.M.loaded_segments (0x79080 : word) = Some W_79028.
Proof. vm_refl. Qed.
Lemma D_79028 : decode_any W_79028 = Some (Branch BC_NE 12 11 8096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7902c : bv 32 := 0x00c10593.
Lemma F_7902c : fetch_word Plain.M.loaded_segments (0x79084 : word) = Some W_7902c.
Proof. vm_refl. Qed.
Lemma D_7902c : decode_any W_7902c = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79030 : bv 32 := 0x00810613.
Lemma F_79030 : fetch_word Plain.M.loaded_segments (0x79088 : word) = Some W_79030.
Proof. vm_refl. Qed.
Lemma D_79030 : decode_any W_79030 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79034 : bv 32 := 0x00098513.
Lemma F_79034 : fetch_word Plain.M.loaded_segments (0x7908c : word) = Some W_79034.
Proof. vm_refl. Qed.
Lemma D_79034 : decode_any W_79034 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79038 : bv 32 := 0x00000693.
Lemma F_79038 : fetch_word Plain.M.loaded_segments (0x79090 : word) = Some W_79038.
Proof. vm_refl. Qed.
Lemma D_79038 : decode_any W_79038 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7903c : bv 32 := 0xd65f30ef.
Lemma F_7903c : fetch_word Plain.M.loaded_segments (0x79094 : word) = Some W_7903c.
Proof. vm_refl. Qed.
Lemma D_7903c : decode_any W_7903c = Some (Jal 1 2047332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79040 : bv 32 := 0x00098513.
Lemma F_79040 : fetch_word Plain.M.loaded_segments (0x79098 : word) = Some W_79040.
Proof. vm_refl. Qed.
Lemma D_79040 : decode_any W_79040 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79044 : bv 32 := 0xa61f30ef.
Lemma F_79044 : fetch_word Plain.M.loaded_segments (0x7909c : word) = Some W_79044.
Proof. vm_refl. Qed.
Lemma D_79044 : decode_any W_79044 = Some (Jal 1 2046560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79048 : bv 32 := 0x00050a13.
Lemma F_79048 : fetch_word Plain.M.loaded_segments (0x790a0 : word) = Some W_79048.
Proof. vm_refl. Qed.
Lemma D_79048 : decode_any W_79048 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7904c : bv 32 := 0x00098513.
Lemma F_7904c : fetch_word Plain.M.loaded_segments (0x790a4 : word) = Some W_7904c.
Proof. vm_refl. Qed.
Lemma D_7904c : decode_any W_7904c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79050 : bv 32 := 0x999f40ef.
Lemma F_79050 : fetch_word Plain.M.loaded_segments (0x790a8 : word) = Some W_79050.
Proof. vm_refl. Qed.
Lemma D_79050 : decode_any W_79050 = Some (Jal 1 2050456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79054 : bv 32 := 0x00812583.
Lemma F_79054 : fetch_word Plain.M.loaded_segments (0x790ac : word) = Some W_79054.
Proof. vm_refl. Qed.
Lemma D_79054 : decode_any W_79054 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79058 : bv 32 := 0x1ab05e63.
Lemma F_79058 : fetch_word Plain.M.loaded_segments (0x790b0 : word) = Some W_79058.
Proof. vm_refl. Qed.
Lemma D_79058 : decode_any W_79058 = Some (Branch BC_GE 0 11 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7905c : bv 32 := 0x00000613.
Lemma F_7905c : fetch_word Plain.M.loaded_segments (0x790b4 : word) = Some W_7905c.
Proof. vm_refl. Qed.
Lemma D_7905c : decode_any W_7905c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79060 : bv 32 := 0x00000693.
Lemma F_79060 : fetch_word Plain.M.loaded_segments (0x790b8 : word) = Some W_79060.
Proof. vm_refl. Qed.
Lemma D_79060 : decode_any W_79060 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79064 : bv 32 := 0x00000713.
Lemma F_79064 : fetch_word Plain.M.loaded_segments (0x790bc : word) = Some W_79064.
Proof. vm_refl. Qed.
Lemma D_79064 : decode_any W_79064 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79068 : bv 32 := 0x00c16803.
Lemma F_79068 : fetch_word Plain.M.loaded_segments (0x790c0 : word) = Some W_79068.
Proof. vm_refl. Qed.
Lemma D_79068 : decode_any W_79068 = Some (Load SZ4 false 16 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7906c : bv 32 := 0xfff00893.
Lemma F_7906c : fetch_word Plain.M.loaded_segments (0x790c4 : word) = Some W_7906c.
Proof. vm_refl. Qed.
Lemma D_7906c : decode_any W_7906c = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79070 : bv 32 := 0x002a1a13.
Lemma F_79070 : fetch_word Plain.M.loaded_segments (0x790c8 : word) = Some W_79070.
Proof. vm_refl. Qed.
Lemma D_79070 : decode_any W_79070 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79074 : bv 32 := 0x01f87793.
Lemma F_79074 : fetch_word Plain.M.loaded_segments (0x790cc : word) = Some W_79074.
Proof. vm_refl. Qed.
Lemma D_79074 : decode_any W_79074 = Some (OpImm ALU_AND 15 16 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79078 : bv 32 := 0x410002bb.
Lemma F_79078 : fetch_word Plain.M.loaded_segments (0x790d0 : word) = Some W_79078.
Proof. vm_refl. Qed.
Lemma D_79078 : decode_any W_79078 = Some (Op32 ALU_SUB 5 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7907c : bv 32 := 0x4058581b.
Lemma F_7907c : fetch_word Plain.M.loaded_segments (0x790d4 : word) = Some W_7907c.
Proof. vm_refl. Qed.
Lemma D_7907c : decode_any W_7907c = Some (ShiftImm32 ALU_SRA 16 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79080 : bv 32 := 0x005898bb.
Lemma F_79080 : fetch_word Plain.M.loaded_segments (0x790d8 : word) = Some W_79080.
Proof. vm_refl. Qed.
Lemma D_79080 : decode_any W_79080 = Some (Op32 ALU_SLL 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79084 : bv 32 := 0x02081293.
Lemma F_79084 : fetch_word Plain.M.loaded_segments (0x790dc : word) = Some W_79084.
Proof. vm_refl. Qed.
Lemma D_79084 : decode_any W_79084 = Some (ShiftImm ALU_SLL 5 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79088 : bv 32 := 0x01e2d293.
Lemma F_79088 : fetch_word Plain.M.loaded_segments (0x790e0 : word) = Some W_79088.
Proof. vm_refl. Qed.
Lemma D_79088 : decode_any W_79088 = Some (ShiftImm ALU_SRL 5 5 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7908c : bv 32 := 0x00050313.
Lemma F_7908c : fetch_word Plain.M.loaded_segments (0x790e4 : word) = Some W_7908c.
Proof. vm_refl. Qed.
Lemma D_7908c : decode_any W_7908c = Some (OpImm ALU_ADD 6 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79090 : bv 32 := 0x0140006f.
Lemma F_79090 : fetch_word Plain.M.loaded_segments (0x790e8 : word) = Some W_79090.
Proof. vm_refl. Qed.
Lemma D_79090 : decode_any W_79090 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79094 : bv 32 := 0x0016869b.
Lemma F_79094 : fetch_word Plain.M.loaded_segments (0x790ec : word) = Some W_79094.
Proof. vm_refl. Qed.
Lemma D_79094 : decode_any W_79094 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79098 : bv 32 := 0x01430333.
Lemma F_79098 : fetch_word Plain.M.loaded_segments (0x790f0 : word) = Some W_79098.
Proof. vm_refl. Qed.
Lemma D_79098 : decode_any W_79098 = Some (Op ALU_ADD 6 6 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7909c : bv 32 := 0x00160613.
Lemma F_7909c : fetch_word Plain.M.loaded_segments (0x790f4 : word) = Some W_7909c.
Proof. vm_refl. Qed.
Lemma D_7909c : decode_any W_7909c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790a0 : bv 32 := 0x16b68c63.
Lemma F_790a0 : fetch_word Plain.M.loaded_segments (0x790f8 : word) = Some W_790a0.
Proof. vm_refl. Qed.
Lemma D_790a0 : decode_any W_790a0 = Some (Branch BC_EQ 13 11 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790a4 : bv 32 := 0x09005463.
Lemma F_790a4 : fetch_word Plain.M.loaded_segments (0x790fc : word) = Some W_790a4.
Proof. vm_refl. Qed.
Lemma D_790a4 : decode_any W_790a4 = Some (Branch BC_GE 0 16 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790a8 : bv 32 := 0x02ca03b3.
Lemma F_790a8 : fetch_word Plain.M.loaded_segments (0x79100 : word) = Some W_790a8.
Proof. vm_refl. Qed.
Lemma D_790a8 : decode_any W_790a8 = Some (Mul M_MUL 7 20 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790ac : bv 32 := 0x007283b3.
Lemma F_790ac : fetch_word Plain.M.loaded_segments (0x79104 : word) = Some W_790ac.
Proof. vm_refl. Qed.
Lemma D_790ac : decode_any W_790ac = Some (Op ALU_ADD 7 5 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790b0 : bv 32 := 0x007503b3.
Lemma F_790b0 : fetch_word Plain.M.loaded_segments (0x79108 : word) = Some W_790b0.
Proof. vm_refl. Qed.
Lemma D_790b0 : decode_any W_790b0 = Some (Op ALU_ADD 7 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790b4 : bv 32 := 0x00030e13.
Lemma F_790b4 : fetch_word Plain.M.loaded_segments (0x7910c : word) = Some W_790b4.
Proof. vm_refl. Qed.
Lemma D_790b4 : decode_any W_790b4 = Some (OpImm ALU_ADD 28 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790b8 : bv 32 := 0x00c0006f.
Lemma F_790b8 : fetch_word Plain.M.loaded_segments (0x79110 : word) = Some W_790b8.
Proof. vm_refl. Qed.
Lemma D_790b8 : decode_any W_790b8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790bc : bv 32 := 0x004e0e13.
Lemma F_790bc : fetch_word Plain.M.loaded_segments (0x79114 : word) = Some W_790bc.
Proof. vm_refl. Qed.
Lemma D_790bc : decode_any W_790bc = Some (OpImm ALU_ADD 28 28 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790c0 : bv 32 := 0x067e0063.
Lemma F_790c0 : fetch_word Plain.M.loaded_segments (0x79118 : word) = Some W_790c0.
Proof. vm_refl. Qed.
Lemma D_790c0 : decode_any W_790c0 = Some (Branch BC_EQ 28 7 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790c4 : bv 32 := 0x000e6e83.
Lemma F_790c4 : fetch_word Plain.M.loaded_segments (0x7911c : word) = Some W_790c4.
Proof. vm_refl. Qed.
Lemma D_790c4 : decode_any W_790c4 = Some (Load SZ4 false 29 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790c8 : bv 32 := 0xfe0e8ae3.
Lemma F_790c8 : fetch_word Plain.M.loaded_segments (0x79120 : word) = Some W_790c8.
Proof. vm_refl. Qed.
Lemma D_790c8 : decode_any W_790c8 = Some (Branch BC_EQ 29 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790cc : bv 32 := 0x0ffeff13.
Lemma F_790cc : fetch_word Plain.M.loaded_segments (0x79124 : word) = Some W_790cc.
Proof. vm_refl. Qed.
Lemma D_790cc : decode_any W_790cc = Some (OpImm ALU_AND 30 29 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790d0 : bv 32 := 0x006edf93.
Lemma F_790d0 : fetch_word Plain.M.loaded_segments (0x79128 : word) = Some W_790d0.
Proof. vm_refl. Qed.
Lemma D_790d0 : decode_any W_790d0 = Some (ShiftImm ALU_SRL 31 29 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790d4 : bv 32 := 0x00eed993.
Lemma F_790d4 : fetch_word Plain.M.loaded_segments (0x7912c : word) = Some W_790d4.
Proof. vm_refl. Qed.
Lemma D_790d4 : decode_any W_790d4 = Some (ShiftImm ALU_SRL 19 29 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790d8 : bv 32 := 0x018ede9b.
Lemma F_790d8 : fetch_word Plain.M.loaded_segments (0x79130 : word) = Some W_790d8.
Proof. vm_refl. Qed.
Lemma D_790d8 : decode_any W_790d8 = Some (ShiftImm32 ALU_SRL 29 29 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790dc : bv 32 := 0x002f1f13.
Lemma F_790dc : fetch_word Plain.M.loaded_segments (0x79134 : word) = Some W_790dc.
Proof. vm_refl. Qed.
Lemma D_790dc : decode_any W_790dc = Some (ShiftImm ALU_SLL 30 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790e0 : bv 32 := 0x3fcfff93.
Lemma F_790e0 : fetch_word Plain.M.loaded_segments (0x79138 : word) = Some W_790e0.
Proof. vm_refl. Qed.
Lemma D_790e0 : decode_any W_790e0 = Some (OpImm ALU_AND 31 31 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790e4 : bv 32 := 0x3fc9f993.
Lemma F_790e4 : fetch_word Plain.M.loaded_segments (0x7913c : word) = Some W_790e4.
Proof. vm_refl. Qed.
Lemma D_790e4 : decode_any W_790e4 = Some (OpImm ALU_AND 19 19 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790e8 : bv 32 := 0x002e9e93.
Lemma F_790e8 : fetch_word Plain.M.loaded_segments (0x79140 : word) = Some W_790e8.
Proof. vm_refl. Qed.
Lemma D_790e8 : decode_any W_790e8 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790ec : bv 32 := 0x01e90f33.
Lemma F_790ec : fetch_word Plain.M.loaded_segments (0x79144 : word) = Some W_790ec.
Proof. vm_refl. Qed.
Lemma D_790ec : decode_any W_790ec = Some (Op ALU_ADD 30 18 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790f0 : bv 32 := 0x01f90fb3.
Lemma F_790f0 : fetch_word Plain.M.loaded_segments (0x79148 : word) = Some W_790f0.
Proof. vm_refl. Qed.
Lemma D_790f0 : decode_any W_790f0 = Some (Op ALU_ADD 31 18 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790f4 : bv 32 := 0x013909b3.
Lemma F_790f4 : fetch_word Plain.M.loaded_segments (0x7914c : word) = Some W_790f4.
Proof. vm_refl. Qed.
Lemma D_790f4 : decode_any W_790f4 = Some (Op ALU_ADD 19 18 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790f8 : bv 32 := 0x000f2f03.
Lemma F_790f8 : fetch_word Plain.M.loaded_segments (0x79150 : word) = Some W_790f8.
Proof. vm_refl. Qed.
Lemma D_790f8 : decode_any W_790f8 = Some (Load SZ4 true 30 30 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_790fc : bv 32 := 0x000faf83.
Lemma F_790fc : fetch_word Plain.M.loaded_segments (0x79154 : word) = Some W_790fc.
Proof. vm_refl. Qed.
Lemma D_790fc : decode_any W_790fc = Some (Load SZ4 true 31 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79100 : bv 32 := 0x0009a983.
Lemma F_79100 : fetch_word Plain.M.loaded_segments (0x79158 : word) = Some W_79100.
Proof. vm_refl. Qed.
Lemma D_79100 : decode_any W_79100 = Some (Load SZ4 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79104 : bv 32 := 0x01d90eb3.
Lemma F_79104 : fetch_word Plain.M.loaded_segments (0x7915c : word) = Some W_79104.
Proof. vm_refl. Qed.
Lemma D_79104 : decode_any W_79104 = Some (Op ALU_ADD 29 18 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79108 : bv 32 := 0x000eae83.
Lemma F_79108 : fetch_word Plain.M.loaded_segments (0x79160 : word) = Some W_79108.
Proof. vm_refl. Qed.
Lemma D_79108 : decode_any W_79108 = Some (Load SZ4 true 29 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7910c : bv 32 := 0x00ef0733.
Lemma F_7910c : fetch_word Plain.M.loaded_segments (0x79164 : word) = Some W_7910c.
Proof. vm_refl. Qed.
Lemma D_7910c : decode_any W_7910c = Some (Op ALU_ADD 14 30 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79110 : bv 32 := 0x013f8fb3.
Lemma F_79110 : fetch_word Plain.M.loaded_segments (0x79168 : word) = Some W_79110.
Proof. vm_refl. Qed.
Lemma D_79110 : decode_any W_79110 = Some (Op ALU_ADD 31 31 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79114 : bv 32 := 0x01f70733.
Lemma F_79114 : fetch_word Plain.M.loaded_segments (0x7916c : word) = Some W_79114.
Proof. vm_refl. Qed.
Lemma D_79114 : decode_any W_79114 = Some (Op ALU_ADD 14 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79118 : bv 32 := 0x01d70733.
Lemma F_79118 : fetch_word Plain.M.loaded_segments (0x79170 : word) = Some W_79118.
Proof. vm_refl. Qed.
Lemma D_79118 : decode_any W_79118 = Some (Op ALU_ADD 14 14 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7911c : bv 32 := 0xfa1ff06f.
Lemma F_7911c : fetch_word Plain.M.loaded_segments (0x79174 : word) = Some W_7911c.
Proof. vm_refl. Qed.
Lemma D_7911c : decode_any W_7911c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79120 : bv 32 := 0x00080393.
Lemma F_79120 : fetch_word Plain.M.loaded_segments (0x79178 : word) = Some W_79120.
Proof. vm_refl. Qed.
Lemma D_79120 : decode_any W_79120 = Some (OpImm ALU_ADD 7 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79124 : bv 32 := 0x00079863.
Lemma F_79124 : fetch_word Plain.M.loaded_segments (0x7917c : word) = Some W_79124.
Proof. vm_refl. Qed.
Lemma D_79124 : decode_any W_79124 = Some (Branch BC_NE 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79128 : bv 32 := 0xf6dff06f.
Lemma F_79128 : fetch_word Plain.M.loaded_segments (0x79180 : word) = Some W_79128.
Proof. vm_refl. Qed.
Lemma D_79128 : decode_any W_79128 = Some (Jal 0 2097004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7912c : bv 32 := 0x00000393.
Lemma F_7912c : fetch_word Plain.M.loaded_segments (0x79184 : word) = Some W_7912c.
Proof. vm_refl. Qed.
Lemma D_7912c : decode_any W_7912c = Some (OpImm ALU_ADD 7 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79130 : bv 32 := 0xf60782e3.
Lemma F_79130 : fetch_word Plain.M.loaded_segments (0x79188 : word) = Some W_79130.
Proof. vm_refl. Qed.
Lemma D_79130 : decode_any W_79130 = Some (Branch BC_EQ 15 0 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79134 : bv 32 := 0x00239393.
Lemma F_79134 : fetch_word Plain.M.loaded_segments (0x7918c : word) = Some W_79134.
Proof. vm_refl. Qed.
Lemma D_79134 : decode_any W_79134 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79138 : bv 32 := 0x007303b3.
Lemma F_79138 : fetch_word Plain.M.loaded_segments (0x79190 : word) = Some W_79138.
Proof. vm_refl. Qed.
Lemma D_79138 : decode_any W_79138 = Some (Op ALU_ADD 7 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7913c : bv 32 := 0x0003a383.
Lemma F_7913c : fetch_word Plain.M.loaded_segments (0x79194 : word) = Some W_7913c.
Proof. vm_refl. Qed.
Lemma D_7913c : decode_any W_7913c = Some (Load SZ4 true 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79140 : bv 32 := 0x0113f3b3.
Lemma F_79140 : fetch_word Plain.M.loaded_segments (0x79198 : word) = Some W_79140.
Proof. vm_refl. Qed.
Lemma D_79140 : decode_any W_79140 = Some (Op ALU_AND 7 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79144 : bv 32 := 0xf40388e3.
Lemma F_79144 : fetch_word Plain.M.loaded_segments (0x7919c : word) = Some W_79144.
Proof. vm_refl. Qed.
Lemma D_79144 : decode_any W_79144 = Some (Branch BC_EQ 7 0 8016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79148 : bv 32 := 0x0ff3fe13.
Lemma F_79148 : fetch_word Plain.M.loaded_segments (0x791a0 : word) = Some W_79148.
Proof. vm_refl. Qed.
Lemma D_79148 : decode_any W_79148 = Some (OpImm ALU_AND 28 7 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7914c : bv 32 := 0x0063de93.
Lemma F_7914c : fetch_word Plain.M.loaded_segments (0x791a4 : word) = Some W_7914c.
Proof. vm_refl. Qed.
Lemma D_7914c : decode_any W_7914c = Some (ShiftImm ALU_SRL 29 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79150 : bv 32 := 0x00e3df13.
Lemma F_79150 : fetch_word Plain.M.loaded_segments (0x791a8 : word) = Some W_79150.
Proof. vm_refl. Qed.
Lemma D_79150 : decode_any W_79150 = Some (ShiftImm ALU_SRL 30 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79154 : bv 32 := 0x0183d39b.
Lemma F_79154 : fetch_word Plain.M.loaded_segments (0x791ac : word) = Some W_79154.
Proof. vm_refl. Qed.
Lemma D_79154 : decode_any W_79154 = Some (ShiftImm32 ALU_SRL 7 7 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79158 : bv 32 := 0x002e1e13.
Lemma F_79158 : fetch_word Plain.M.loaded_segments (0x791b0 : word) = Some W_79158.
Proof. vm_refl. Qed.
Lemma D_79158 : decode_any W_79158 = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7915c : bv 32 := 0x3fcefe93.
Lemma F_7915c : fetch_word Plain.M.loaded_segments (0x791b4 : word) = Some W_7915c.
Proof. vm_refl. Qed.
Lemma D_7915c : decode_any W_7915c = Some (OpImm ALU_AND 29 29 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79160 : bv 32 := 0x3fcf7f13.
Lemma F_79160 : fetch_word Plain.M.loaded_segments (0x791b8 : word) = Some W_79160.
Proof. vm_refl. Qed.
Lemma D_79160 : decode_any W_79160 = Some (OpImm ALU_AND 30 30 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79164 : bv 32 := 0x00239393.
Lemma F_79164 : fetch_word Plain.M.loaded_segments (0x791bc : word) = Some W_79164.
Proof. vm_refl. Qed.
Lemma D_79164 : decode_any W_79164 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79168 : bv 32 := 0x01c90e33.
Lemma F_79168 : fetch_word Plain.M.loaded_segments (0x791c0 : word) = Some W_79168.
Proof. vm_refl. Qed.
Lemma D_79168 : decode_any W_79168 = Some (Op ALU_ADD 28 18 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7916c : bv 32 := 0x01d90eb3.
Lemma F_7916c : fetch_word Plain.M.loaded_segments (0x791c4 : word) = Some W_7916c.
Proof. vm_refl. Qed.
Lemma D_7916c : decode_any W_7916c = Some (Op ALU_ADD 29 18 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79170 : bv 32 := 0x01e90f33.
Lemma F_79170 : fetch_word Plain.M.loaded_segments (0x791c8 : word) = Some W_79170.
Proof. vm_refl. Qed.
Lemma D_79170 : decode_any W_79170 = Some (Op ALU_ADD 30 18 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79174 : bv 32 := 0x000e2e03.
Lemma F_79174 : fetch_word Plain.M.loaded_segments (0x791cc : word) = Some W_79174.
Proof. vm_refl. Qed.
Lemma D_79174 : decode_any W_79174 = Some (Load SZ4 true 28 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79178 : bv 32 := 0x000eae83.
Lemma F_79178 : fetch_word Plain.M.loaded_segments (0x791d0 : word) = Some W_79178.
Proof. vm_refl. Qed.
Lemma D_79178 : decode_any W_79178 = Some (Load SZ4 true 29 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7917c : bv 32 := 0x000f2f03.
Lemma F_7917c : fetch_word Plain.M.loaded_segments (0x791d4 : word) = Some W_7917c.
Proof. vm_refl. Qed.
Lemma D_7917c : decode_any W_7917c = Some (Load SZ4 true 30 30 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79180 : bv 32 := 0x007903b3.
Lemma F_79180 : fetch_word Plain.M.loaded_segments (0x791d8 : word) = Some W_79180.
Proof. vm_refl. Qed.
Lemma D_79180 : decode_any W_79180 = Some (Op ALU_ADD 7 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79184 : bv 32 := 0x0003a383.
Lemma F_79184 : fetch_word Plain.M.loaded_segments (0x791dc : word) = Some W_79184.
Proof. vm_refl. Qed.
Lemma D_79184 : decode_any W_79184 = Some (Load SZ4 true 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79188 : bv 32 := 0x00ee0733.
Lemma F_79188 : fetch_word Plain.M.loaded_segments (0x791e0 : word) = Some W_79188.
Proof. vm_refl. Qed.
Lemma D_79188 : decode_any W_79188 = Some (Op ALU_ADD 14 28 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7918c : bv 32 := 0x01ee8eb3.
Lemma F_7918c : fetch_word Plain.M.loaded_segments (0x791e4 : word) = Some W_7918c.
Proof. vm_refl. Qed.
Lemma D_7918c : decode_any W_7918c = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79190 : bv 32 := 0x01d70733.
Lemma F_79190 : fetch_word Plain.M.loaded_segments (0x791e8 : word) = Some W_79190.
Proof. vm_refl. Qed.
Lemma D_79190 : decode_any W_79190 = Some (Op ALU_ADD 14 14 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79194 : bv 32 := 0x00770733.
Lemma F_79194 : fetch_word Plain.M.loaded_segments (0x791ec : word) = Some W_79194.
Proof. vm_refl. Qed.
Lemma D_79194 : decode_any W_79194 = Some (Op ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79198 : bv 32 := 0xefdff06f.
Lemma F_79198 : fetch_word Plain.M.loaded_segments (0x791f0 : word) = Some W_79198.
Proof. vm_refl. Qed.
Lemma D_79198 : decode_any W_79198 = Some (Jal 0 2096892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7919c : bv 32 := 0x00099517.
Lemma F_7919c : fetch_word Plain.M.loaded_segments (0x791f4 : word) = Some W_7919c.
Proof. vm_refl. Qed.
Lemma D_7919c : decode_any W_7919c = Some (Auipc 10 153, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a0 : bv 32 := 0x3d453503.
Lemma F_791a0 : fetch_word Plain.M.loaded_segments (0x791f8 : word) = Some W_791a0.
Proof. vm_refl. Qed.
Lemma D_791a0 : decode_any W_791a0 = Some (Load SZ8 true 10 10 980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a4 : bv 32 := 0x00052503.
Lemma F_791a4 : fetch_word Plain.M.loaded_segments (0x791fc : word) = Some W_791a4.
Proof. vm_refl. Qed.
Lemma D_791a4 : decode_any W_791a4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a8 : bv 32 := 0x00500593.
Lemma F_791a8 : fetch_word Plain.M.loaded_segments (0x79200 : word) = Some W_791a8.
Proof. vm_refl. Qed.
Lemma D_791a8 : decode_any W_791a8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791ac : bv 32 := 0x06a5c063.
Lemma F_791ac : fetch_word Plain.M.loaded_segments (0x79204 : word) = Some W_791ac.
Proof. vm_refl. Qed.
Lemma D_791ac : decode_any W_791ac = Some (Branch BC_LT 11 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b0 : bv 32 := 0xfff98517.
Lemma F_791b0 : fetch_word Plain.M.loaded_segments (0x79208 : word) = Some W_791b0.
Proof. vm_refl. Qed.
Lemma D_791b0 : decode_any W_791b0 = Some (Auipc 10 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b4 : bv 32 := 0xfff9d597.
Lemma F_791b4 : fetch_word Plain.M.loaded_segments (0x7920c : word) = Some W_791b4.
Proof. vm_refl. Qed.
Lemma D_791b4 : decode_any W_791b4 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b8 : bv 32 := 0x69550513.
Lemma F_791b8 : fetch_word Plain.M.loaded_segments (0x79210 : word) = Some W_791b8.
Proof. vm_refl. Qed.
Lemma D_791b8 : decode_any W_791b8 = Some (OpImm ALU_ADD 10 10 1685, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791bc : bv 32 := 0x07658593.
Lemma F_791bc : fetch_word Plain.M.loaded_segments (0x79214 : word) = Some W_791bc.
Proof. vm_refl. Qed.
Lemma D_791bc : decode_any W_791bc = Some (OpImm ALU_ADD 11 11 118, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791c0 : bv 32 := 0x0280006f.
Lemma F_791c0 : fetch_word Plain.M.loaded_segments (0x79218 : word) = Some W_791c0.
Proof. vm_refl. Qed.
Lemma D_791c0 : decode_any W_791c0 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791e8 : bv 32 := 0x00100613.
Lemma F_791e8 : fetch_word Plain.M.loaded_segments (0x79240 : word) = Some W_791e8.
Proof. vm_refl. Qed.
Lemma D_791e8 : decode_any W_791e8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791ec : bv 32 := 0x03813083.
Lemma F_791ec : fetch_word Plain.M.loaded_segments (0x79244 : word) = Some W_791ec.
Proof. vm_refl. Qed.
Lemma D_791ec : decode_any W_791ec = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791f0 : bv 32 := 0x03013403.
Lemma F_791f0 : fetch_word Plain.M.loaded_segments (0x79248 : word) = Some W_791f0.
Proof. vm_refl. Qed.
Lemma D_791f0 : decode_any W_791f0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791f4 : bv 32 := 0x02813483.
Lemma F_791f4 : fetch_word Plain.M.loaded_segments (0x7924c : word) = Some W_791f4.
Proof. vm_refl. Qed.
Lemma D_791f4 : decode_any W_791f4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791f8 : bv 32 := 0x02013903.
Lemma F_791f8 : fetch_word Plain.M.loaded_segments (0x79250 : word) = Some W_791f8.
Proof. vm_refl. Qed.
Lemma D_791f8 : decode_any W_791f8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791fc : bv 32 := 0x01813983.
Lemma F_791fc : fetch_word Plain.M.loaded_segments (0x79254 : word) = Some W_791fc.
Proof. vm_refl. Qed.
Lemma D_791fc : decode_any W_791fc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79200 : bv 32 := 0x01013a03.
Lemma F_79200 : fetch_word Plain.M.loaded_segments (0x79258 : word) = Some W_79200.
Proof. vm_refl. Qed.
Lemma D_79200 : decode_any W_79200 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79204 : bv 32 := 0x04010113.
Lemma F_79204 : fetch_word Plain.M.loaded_segments (0x7925c : word) = Some W_79204.
Proof. vm_refl. Qed.
Lemma D_79204 : decode_any W_79204 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79208 : bv 32 := 0xdede906f.
Lemma F_79208 : fetch_word Plain.M.loaded_segments (0x79260 : word) = Some W_79208.
Proof. vm_refl. Qed.
Lemma D_79208 : decode_any W_79208 = Some (Jal 0 2006508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79218 : bv 32 := 0x00e4a023.
Lemma F_79218 : fetch_word Plain.M.loaded_segments (0x79270 : word) = Some W_79218.
Proof. vm_refl. Qed.
Lemma D_79218 : decode_any W_79218 = Some (Store SZ4 9 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7921c : bv 32 := 0x00041663.
Lemma F_7921c : fetch_word Plain.M.loaded_segments (0x79274 : word) = Some W_7921c.
Proof. vm_refl. Qed.
Lemma D_7921c : decode_any W_7921c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79220 : bv 32 := 0x00090513.
Lemma F_79220 : fetch_word Plain.M.loaded_segments (0x79278 : word) = Some W_79220.
Proof. vm_refl. Qed.
Lemma D_79220 : decode_any W_79220 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79224 : bv 32 := 0x0f8810ef.
Lemma F_79224 : fetch_word Plain.M.loaded_segments (0x7927c : word) = Some W_79224.
Proof. vm_refl. Qed.
Lemma D_79224 : decode_any W_79224 = Some (Jal 1 528632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79228 : bv 32 := 0x00000513.
Lemma F_79228 : fetch_word Plain.M.loaded_segments (0x79280 : word) = Some W_79228.
Proof. vm_refl. Qed.
Lemma D_79228 : decode_any W_79228 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7922c : bv 32 := 0x03813083.
Lemma F_7922c : fetch_word Plain.M.loaded_segments (0x79284 : word) = Some W_7922c.
Proof. vm_refl. Qed.
Lemma D_7922c : decode_any W_7922c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79230 : bv 32 := 0x03013403.
Lemma F_79230 : fetch_word Plain.M.loaded_segments (0x79288 : word) = Some W_79230.
Proof. vm_refl. Qed.
Lemma D_79230 : decode_any W_79230 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79234 : bv 32 := 0x02813483.
Lemma F_79234 : fetch_word Plain.M.loaded_segments (0x7928c : word) = Some W_79234.
Proof. vm_refl. Qed.
Lemma D_79234 : decode_any W_79234 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79238 : bv 32 := 0x02013903.
Lemma F_79238 : fetch_word Plain.M.loaded_segments (0x79290 : word) = Some W_79238.
Proof. vm_refl. Qed.
Lemma D_79238 : decode_any W_79238 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7923c : bv 32 := 0x01813983.
Lemma F_7923c : fetch_word Plain.M.loaded_segments (0x79294 : word) = Some W_7923c.
Proof. vm_refl. Qed.
Lemma D_7923c : decode_any W_7923c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79240 : bv 32 := 0x01013a03.
Lemma F_79240 : fetch_word Plain.M.loaded_segments (0x79298 : word) = Some W_79240.
Proof. vm_refl. Qed.
Lemma D_79240 : decode_any W_79240 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79244 : bv 32 := 0x04010113.
Lemma F_79244 : fetch_word Plain.M.loaded_segments (0x7929c : word) = Some W_79244.
Proof. vm_refl. Qed.
Lemma D_79244 : decode_any W_79244 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79248 : bv 32 := 0x00008067.
Lemma F_79248 : fetch_word Plain.M.loaded_segments (0x792a0 : word) = Some W_79248.
Proof. vm_refl. Qed.
Lemma D_79248 : decode_any W_79248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
