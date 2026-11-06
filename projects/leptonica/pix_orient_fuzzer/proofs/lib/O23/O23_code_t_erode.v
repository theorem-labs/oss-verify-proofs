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
Definition W_8f870 : bv 32 := 0xf8010113.
Lemma F_8f870 : fetch_word Plain.M.loaded_segments (0x8f8c8 : word) = Some W_8f870.
Proof. vm_refl. Qed.
Lemma D_8f870 : decode_any W_8f870 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f874 : bv 32 := 0x06113c23.
Lemma F_8f874 : fetch_word Plain.M.loaded_segments (0x8f8cc : word) = Some W_8f874.
Proof. vm_refl. Qed.
Lemma D_8f874 : decode_any W_8f874 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f878 : bv 32 := 0x06813823.
Lemma F_8f878 : fetch_word Plain.M.loaded_segments (0x8f8d0 : word) = Some W_8f878.
Proof. vm_refl. Qed.
Lemma D_8f878 : decode_any W_8f878 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f87c : bv 32 := 0x06913423.
Lemma F_8f87c : fetch_word Plain.M.loaded_segments (0x8f8d4 : word) = Some W_8f87c.
Proof. vm_refl. Qed.
Lemma D_8f87c : decode_any W_8f87c = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f880 : bv 32 := 0x07213023.
Lemma F_8f880 : fetch_word Plain.M.loaded_segments (0x8f8d8 : word) = Some W_8f880.
Proof. vm_refl. Qed.
Lemma D_8f880 : decode_any W_8f880 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f884 : bv 32 := 0x05313c23.
Lemma F_8f884 : fetch_word Plain.M.loaded_segments (0x8f8dc : word) = Some W_8f884.
Proof. vm_refl. Qed.
Lemma D_8f884 : decode_any W_8f884 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f888 : bv 32 := 0x05413823.
Lemma F_8f888 : fetch_word Plain.M.loaded_segments (0x8f8e0 : word) = Some W_8f888.
Proof. vm_refl. Qed.
Lemma D_8f888 : decode_any W_8f888 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f88c : bv 32 := 0x05513423.
Lemma F_8f88c : fetch_word Plain.M.loaded_segments (0x8f8e4 : word) = Some W_8f88c.
Proof. vm_refl. Qed.
Lemma D_8f88c : decode_any W_8f88c = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f890 : bv 32 := 0x05613023.
Lemma F_8f890 : fetch_word Plain.M.loaded_segments (0x8f8e8 : word) = Some W_8f890.
Proof. vm_refl. Qed.
Lemma D_8f890 : decode_any W_8f890 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f894 : bv 32 := 0x03713c23.
Lemma F_8f894 : fetch_word Plain.M.loaded_segments (0x8f8ec : word) = Some W_8f894.
Proof. vm_refl. Qed.
Lemma D_8f894 : decode_any W_8f894 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f898 : bv 32 := 0x00060493.
Lemma F_8f898 : fetch_word Plain.M.loaded_segments (0x8f8f0 : word) = Some W_8f898.
Proof. vm_refl. Qed.
Lemma D_8f898 : decode_any W_8f898 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f89c : bv 32 := 0x00058913.
Lemma F_8f89c : fetch_word Plain.M.loaded_segments (0x8f8f4 : word) = Some W_8f89c.
Proof. vm_refl. Qed.
Lemma D_8f89c : decode_any W_8f89c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8a0 : bv 32 := 0x00810693.
Lemma F_8f8a0 : fetch_word Plain.M.loaded_segments (0x8f8f8 : word) = Some W_8f8a0.
Proof. vm_refl. Qed.
Lemma D_8f8a0 : decode_any W_8f8a0 = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8a4 : bv 32 := 0xdd9ff0ef.
Lemma F_8f8a4 : fetch_word Plain.M.loaded_segments (0x8f8fc : word) = Some W_8f8a4.
Proof. vm_refl. Qed.
Lemma D_8f8a4 : decode_any W_8f8a4 = Some (Jal 1 2096600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8a8 : bv 32 := 0x1c050263.
Lemma F_8f8a8 : fetch_word Plain.M.loaded_segments (0x8f900 : word) = Some W_8f8a8.
Proof. vm_refl. Qed.
Lemma D_8f8a8 : decode_any W_8f8a8 = Some (Branch BC_EQ 10 0 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8ac : bv 32 := 0x00050413.
Lemma F_8f8ac : fetch_word Plain.M.loaded_segments (0x8f904 : word) = Some W_8f8ac.
Proof. vm_refl. Qed.
Lemma D_8f8ac : decode_any W_8f8ac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8b0 : bv 32 := 0x03410593.
Lemma F_8f8b0 : fetch_word Plain.M.loaded_segments (0x8f908 : word) = Some W_8f8b0.
Proof. vm_refl. Qed.
Lemma D_8f8b0 : decode_any W_8f8b0 = Some (OpImm ALU_ADD 11 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8b4 : bv 32 := 0x03010613.
Lemma F_8f8b4 : fetch_word Plain.M.loaded_segments (0x8f90c : word) = Some W_8f8b4.
Proof. vm_refl. Qed.
Lemma D_8f8b4 : decode_any W_8f8b4 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8b8 : bv 32 := 0x00090513.
Lemma F_8f8b8 : fetch_word Plain.M.loaded_segments (0x8f910 : word) = Some W_8f8b8.
Proof. vm_refl. Qed.
Lemma D_8f8b8 : decode_any W_8f8b8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8bc : bv 32 := 0x00000693.
Lemma F_8f8bc : fetch_word Plain.M.loaded_segments (0x8f914 : word) = Some W_8f8bc.
Proof. vm_refl. Qed.
Lemma D_8f8bc : decode_any W_8f8bc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8c0 : bv 32 := 0xce0dd0ef.
Lemma F_8f8c0 : fetch_word Plain.M.loaded_segments (0x8f918 : word) = Some W_8f8c0.
Proof. vm_refl. Qed.
Lemma D_8f8c0 : decode_any W_8f8c0 = Some (Jal 1 1955040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8c4 : bv 32 := 0x02810593.
Lemma F_8f8c4 : fetch_word Plain.M.loaded_segments (0x8f91c : word) = Some W_8f8c4.
Proof. vm_refl. Qed.
Lemma D_8f8c4 : decode_any W_8f8c4 = Some (OpImm ALU_ADD 11 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8c8 : bv 32 := 0x02c10613.
Lemma F_8f8c8 : fetch_word Plain.M.loaded_segments (0x8f920 : word) = Some W_8f8c8.
Proof. vm_refl. Qed.
Lemma D_8f8c8 : decode_any W_8f8c8 = Some (OpImm ALU_ADD 12 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8cc : bv 32 := 0x02010693.
Lemma F_8f8cc : fetch_word Plain.M.loaded_segments (0x8f924 : word) = Some W_8f8cc.
Proof. vm_refl. Qed.
Lemma D_8f8cc : decode_any W_8f8cc = Some (OpImm ALU_ADD 13 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8d0 : bv 32 := 0x02410713.
Lemma F_8f8d0 : fetch_word Plain.M.loaded_segments (0x8f928 : word) = Some W_8f8d0.
Proof. vm_refl. Qed.
Lemma D_8f8d0 : decode_any W_8f8d0 = Some (OpImm ALU_ADD 14 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8d4 : bv 32 := 0x00048513.
Lemma F_8f8d4 : fetch_word Plain.M.loaded_segments (0x8f92c : word) = Some W_8f8d4.
Proof. vm_refl. Qed.
Lemma D_8f8d4 : decode_any W_8f8d4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8d8 : bv 32 := 0x519020ef.
Lemma F_8f8d8 : fetch_word Plain.M.loaded_segments (0x8f930 : word) = Some W_8f8d8.
Proof. vm_refl. Qed.
Lemma D_8f8d8 : decode_any W_8f8d8 = Some (Jal 1 11544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8dc : bv 32 := 0x00040513.
Lemma F_8f8dc : fetch_word Plain.M.loaded_segments (0x8f934 : word) = Some W_8f8dc.
Proof. vm_refl. Qed.
Lemma D_8f8dc : decode_any W_8f8dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8e0 : bv 32 := 0xbe9de0ef.
Lemma F_8f8e0 : fetch_word Plain.M.loaded_segments (0x8f938 : word) = Some W_8f8e0.
Proof. vm_refl. Qed.
Lemma D_8f8e0 : decode_any W_8f8e0 = Some (Jal 1 1960936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8e4 : bv 32 := 0x02812583.
Lemma F_8f8e4 : fetch_word Plain.M.loaded_segments (0x8f93c : word) = Some W_8f8e4.
Proof. vm_refl. Qed.
Lemma D_8f8e4 : decode_any W_8f8e4 = Some (Load SZ4 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8e8 : bv 32 := 0x08b05c63.
Lemma F_8f8e8 : fetch_word Plain.M.loaded_segments (0x8f940 : word) = Some W_8f8e8.
Proof. vm_refl. Qed.
Lemma D_8f8e8 : decode_any W_8f8e8 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8ec : bv 32 := 0x00000913.
Lemma F_8f8ec : fetch_word Plain.M.loaded_segments (0x8f944 : word) = Some W_8f8ec.
Proof. vm_refl. Qed.
Lemma D_8f8ec : decode_any W_8f8ec = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8f0 : bv 32 := 0x02c12503.
Lemma F_8f8f0 : fetch_word Plain.M.loaded_segments (0x8f948 : word) = Some W_8f8f0.
Proof. vm_refl. Qed.
Lemma D_8f8f0 : decode_any W_8f8f0 = Some (Load SZ4 true 10 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8f4 : bv 32 := 0x00100993.
Lemma F_8f8f4 : fetch_word Plain.M.loaded_segments (0x8f94c : word) = Some W_8f8f4.
Proof. vm_refl. Qed.
Lemma D_8f8f4 : decode_any W_8f8f4 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8f8 : bv 32 := 0x0100006f.
Lemma F_8f8f8 : fetch_word Plain.M.loaded_segments (0x8f950 : word) = Some W_8f8f8.
Proof. vm_refl. Qed.
Lemma D_8f8f8 : decode_any W_8f8f8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f8fc : bv 32 := 0x02812583.
Lemma F_8f8fc : fetch_word Plain.M.loaded_segments (0x8f954 : word) = Some W_8f8fc.
Proof. vm_refl. Qed.
Lemma D_8f8fc : decode_any W_8f8fc = Some (Load SZ4 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f900 : bv 32 := 0x00190913.
Lemma F_8f900 : fetch_word Plain.M.loaded_segments (0x8f958 : word) = Some W_8f900.
Proof. vm_refl. Qed.
Lemma D_8f900 : decode_any W_8f900 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f904 : bv 32 := 0x06b95e63.
Lemma F_8f904 : fetch_word Plain.M.loaded_segments (0x8f95c : word) = Some W_8f904.
Proof. vm_refl. Qed.
Lemma D_8f904 : decode_any W_8f904 = Some (Branch BC_GE 18 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f908 : bv 32 := 0xfea05ce3.
Lemma F_8f908 : fetch_word Plain.M.loaded_segments (0x8f960 : word) = Some W_8f908.
Proof. vm_refl. Qed.
Lemma D_8f908 : decode_any W_8f908 = Some (Branch BC_GE 0 10 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f90c : bv 32 := 0x00000a13.
Lemma F_8f90c : fetch_word Plain.M.loaded_segments (0x8f964 : word) = Some W_8f90c.
Proof. vm_refl. Qed.
Lemma D_8f90c : decode_any W_8f90c = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f910 : bv 32 := 0x00000a93.
Lemma F_8f910 : fetch_word Plain.M.loaded_segments (0x8f968 : word) = Some W_8f910.
Proof. vm_refl. Qed.
Lemma D_8f910 : decode_any W_8f910 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f914 : bv 32 := 0x00000b13.
Lemma F_8f914 : fetch_word Plain.M.loaded_segments (0x8f96c : word) = Some W_8f914.
Proof. vm_refl. Qed.
Lemma D_8f914 : decode_any W_8f914 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f918 : bv 32 := 0x00391b93.
Lemma F_8f918 : fetch_word Plain.M.loaded_segments (0x8f970 : word) = Some W_8f918.
Proof. vm_refl. Qed.
Lemma D_8f918 : decode_any W_8f918 = Some (ShiftImm ALU_SLL 23 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f91c : bv 32 := 0x0140006f.
Lemma F_8f91c : fetch_word Plain.M.loaded_segments (0x8f974 : word) = Some W_8f91c.
Proof. vm_refl. Qed.
Lemma D_8f91c : decode_any W_8f91c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f920 : bv 32 := 0x001b0b13.
Lemma F_8f920 : fetch_word Plain.M.loaded_segments (0x8f978 : word) = Some W_8f920.
Proof. vm_refl. Qed.
Lemma D_8f920 : decode_any W_8f920 = Some (OpImm ALU_ADD 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f924 : bv 32 := 0xfffa8a93.
Lemma F_8f924 : fetch_word Plain.M.loaded_segments (0x8f97c : word) = Some W_8f924.
Proof. vm_refl. Qed.
Lemma D_8f924 : decode_any W_8f924 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f928 : bv 32 := 0x004a0a13.
Lemma F_8f928 : fetch_word Plain.M.loaded_segments (0x8f980 : word) = Some W_8f928.
Proof. vm_refl. Qed.
Lemma D_8f928 : decode_any W_8f928 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f92c : bv 32 := 0xfcab58e3.
Lemma F_8f92c : fetch_word Plain.M.loaded_segments (0x8f984 : word) = Some W_8f92c.
Proof. vm_refl. Qed.
Lemma D_8f92c : decode_any W_8f92c = Some (Branch BC_GE 22 10 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f930 : bv 32 := 0x0104b583.
Lemma F_8f930 : fetch_word Plain.M.loaded_segments (0x8f988 : word) = Some W_8f930.
Proof. vm_refl. Qed.
Lemma D_8f930 : decode_any W_8f930 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f934 : bv 32 := 0x017585b3.
Lemma F_8f934 : fetch_word Plain.M.loaded_segments (0x8f98c : word) = Some W_8f934.
Proof. vm_refl. Qed.
Lemma D_8f934 : decode_any W_8f934 = Some (Op ALU_ADD 11 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f938 : bv 32 := 0x0005b583.
Lemma F_8f938 : fetch_word Plain.M.loaded_segments (0x8f990 : word) = Some W_8f938.
Proof. vm_refl. Qed.
Lemma D_8f938 : decode_any W_8f938 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f93c : bv 32 := 0x014585b3.
Lemma F_8f93c : fetch_word Plain.M.loaded_segments (0x8f994 : word) = Some W_8f93c.
Proof. vm_refl. Qed.
Lemma D_8f93c : decode_any W_8f93c = Some (Op ALU_ADD 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f940 : bv 32 := 0x0005a583.
Lemma F_8f940 : fetch_word Plain.M.loaded_segments (0x8f998 : word) = Some W_8f940.
Proof. vm_refl. Qed.
Lemma D_8f940 : decode_any W_8f940 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f944 : bv 32 := 0xfd359ee3.
Lemma F_8f944 : fetch_word Plain.M.loaded_segments (0x8f99c : word) = Some W_8f944.
Proof. vm_refl. Qed.
Lemma D_8f944 : decode_any W_8f944 = Some (Branch BC_NE 11 19 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f948 : bv 32 := 0x02412503.
Lemma F_8f948 : fetch_word Plain.M.loaded_segments (0x8f9a0 : word) = Some W_8f948.
Proof. vm_refl. Qed.
Lemma D_8f948 : decode_any W_8f948 = Some (Load SZ4 true 10 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f94c : bv 32 := 0x02012603.
Lemma F_8f94c : fetch_word Plain.M.loaded_segments (0x8f9a4 : word) = Some W_8f94c.
Proof. vm_refl. Qed.
Lemma D_8f94c : decode_any W_8f94c = Some (Load SZ4 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f950 : bv 32 := 0x03412683.
Lemma F_8f950 : fetch_word Plain.M.loaded_segments (0x8f9a8 : word) = Some W_8f950.
Proof. vm_refl. Qed.
Lemma D_8f950 : decode_any W_8f950 = Some (Load SZ4 true 13 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f954 : bv 32 := 0x03012703.
Lemma F_8f954 : fetch_word Plain.M.loaded_segments (0x8f9ac : word) = Some W_8f954.
Proof. vm_refl. Qed.
Lemma D_8f954 : decode_any W_8f954 = Some (Load SZ4 true 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f958 : bv 32 := 0x00813803.
Lemma F_8f958 : fetch_word Plain.M.loaded_segments (0x8f9b0 : word) = Some W_8f958.
Proof. vm_refl. Qed.
Lemma D_8f958 : decode_any W_8f958 = Some (Load SZ8 true 16 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f95c : bv 32 := 0x00aa85bb.
Lemma F_8f95c : fetch_word Plain.M.loaded_segments (0x8f9b4 : word) = Some W_8f95c.
Proof. vm_refl. Qed.
Lemma D_8f95c : decode_any W_8f95c = Some (Op32 ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f960 : bv 32 := 0x4126063b.
Lemma F_8f960 : fetch_word Plain.M.loaded_segments (0x8f9b8 : word) = Some W_8f960.
Proof. vm_refl. Qed.
Lemma D_8f960 : decode_any W_8f960 = Some (Op32 ALU_SUB 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f964 : bv 32 := 0x00800793.
Lemma F_8f964 : fetch_word Plain.M.loaded_segments (0x8f9bc : word) = Some W_8f964.
Proof. vm_refl. Qed.
Lemma D_8f964 : decode_any W_8f964 = Some (OpImm ALU_ADD 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f968 : bv 32 := 0x00013023.
Lemma F_8f968 : fetch_word Plain.M.loaded_segments (0x8f9c0 : word) = Some W_8f968.
Proof. vm_refl. Qed.
Lemma D_8f968 : decode_any W_8f968 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f96c : bv 32 := 0x00040513.
Lemma F_8f96c : fetch_word Plain.M.loaded_segments (0x8f9c4 : word) = Some W_8f96c.
Proof. vm_refl. Qed.
Lemma D_8f96c : decode_any W_8f96c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f970 : bv 32 := 0x00000893.
Lemma F_8f970 : fetch_word Plain.M.loaded_segments (0x8f9c8 : word) = Some W_8f970.
Proof. vm_refl. Qed.
Lemma D_8f970 : decode_any W_8f970 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f974 : bv 32 := 0xde1e90ef.
Lemma F_8f974 : fetch_word Plain.M.loaded_segments (0x8f9cc : word) = Some W_8f974.
Proof. vm_refl. Qed.
Lemma D_8f974 : decode_any W_8f974 = Some (Jal 1 2006496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f978 : bv 32 := 0x02c12503.
Lemma F_8f978 : fetch_word Plain.M.loaded_segments (0x8f9d0 : word) = Some W_8f978.
Proof. vm_refl. Qed.
Lemma D_8f978 : decode_any W_8f978 = Some (Load SZ4 true 10 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f97c : bv 32 := 0xfa5ff06f.
Lemma F_8f97c : fetch_word Plain.M.loaded_segments (0x8f9d4 : word) = Some W_8f97c.
Proof. vm_refl. Qed.
Lemma D_8f97c : decode_any W_8f97c = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f980 : bv 32 := 0x00084517.
Lemma F_8f980 : fetch_word Plain.M.loaded_segments (0x8f9d8 : word) = Some W_8f980.
Proof. vm_refl. Qed.
Lemma D_8f980 : decode_any W_8f980 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f984 : bv 32 := 0xe1052503.
Lemma F_8f984 : fetch_word Plain.M.loaded_segments (0x8f9dc : word) = Some W_8f984.
Proof. vm_refl. Qed.
Lemma D_8f984 : decode_any W_8f984 = Some (Load SZ4 true 10 10 3600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f988 : bv 32 := 0x00100593.
Lemma F_8f988 : fetch_word Plain.M.loaded_segments (0x8f9e0 : word) = Some W_8f988.
Proof. vm_refl. Qed.
Lemma D_8f988 : decode_any W_8f988 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f98c : bv 32 := 0x0cb51a63.
Lemma F_8f98c : fetch_word Plain.M.loaded_segments (0x8f9e4 : word) = Some W_8f98c.
Proof. vm_refl. Qed.
Lemma D_8f98c : decode_any W_8f98c = Some (Branch BC_NE 10 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f990 : bv 32 := 0x01c10593.
Lemma F_8f990 : fetch_word Plain.M.loaded_segments (0x8f9e8 : word) = Some W_8f990.
Proof. vm_refl. Qed.
Lemma D_8f990 : decode_any W_8f990 = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f994 : bv 32 := 0x01810613.
Lemma F_8f994 : fetch_word Plain.M.loaded_segments (0x8f9ec : word) = Some W_8f994.
Proof. vm_refl. Qed.
Lemma D_8f994 : decode_any W_8f994 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f998 : bv 32 := 0x01410693.
Lemma F_8f998 : fetch_word Plain.M.loaded_segments (0x8f9f0 : word) = Some W_8f998.
Proof. vm_refl. Qed.
Lemma D_8f998 : decode_any W_8f998 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f99c : bv 32 := 0x01010713.
Lemma F_8f99c : fetch_word Plain.M.loaded_segments (0x8f9f4 : word) = Some W_8f99c.
Proof. vm_refl. Qed.
Lemma D_8f99c : decode_any W_8f99c = Some (OpImm ALU_ADD 14 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9a0 : bv 32 := 0x00048513.
Lemma F_8f9a0 : fetch_word Plain.M.loaded_segments (0x8f9f8 : word) = Some W_8f9a0.
Proof. vm_refl. Qed.
Lemma D_8f9a0 : decode_any W_8f9a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9a4 : bv 32 := 0x1b0030ef.
Lemma F_8f9a4 : fetch_word Plain.M.loaded_segments (0x8f9fc : word) = Some W_8f9a4.
Proof. vm_refl. Qed.
Lemma D_8f9a4 : decode_any W_8f9a4 = Some (Jal 1 12720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9a8 : bv 32 := 0x01c12683.
Lemma F_8f9a8 : fetch_word Plain.M.loaded_segments (0x8fa00 : word) = Some W_8f9a8.
Proof. vm_refl. Qed.
Lemma D_8f9a8 : decode_any W_8f9a8 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9ac : bv 32 := 0x02d05463.
Lemma F_8f9ac : fetch_word Plain.M.loaded_segments (0x8fa04 : word) = Some W_8f9ac.
Proof. vm_refl. Qed.
Lemma D_8f9ac : decode_any W_8f9ac = Some (Branch BC_GE 0 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9b0 : bv 32 := 0x03012703.
Lemma F_8f9b0 : fetch_word Plain.M.loaded_segments (0x8fa08 : word) = Some W_8f9b0.
Proof. vm_refl. Qed.
Lemma D_8f9b0 : decode_any W_8f9b0 = Some (Load SZ4 true 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9b4 : bv 32 := 0x00013023.
Lemma F_8f9b4 : fetch_word Plain.M.loaded_segments (0x8fa0c : word) = Some W_8f9b4.
Proof. vm_refl. Qed.
Lemma D_8f9b4 : decode_any W_8f9b4 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9b8 : bv 32 := 0x00040513.
Lemma F_8f9b8 : fetch_word Plain.M.loaded_segments (0x8fa10 : word) = Some W_8f9b8.
Proof. vm_refl. Qed.
Lemma D_8f9b8 : decode_any W_8f9b8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9bc : bv 32 := 0x00000593.
Lemma F_8f9bc : fetch_word Plain.M.loaded_segments (0x8fa14 : word) = Some W_8f9bc.
Proof. vm_refl. Qed.
Lemma D_8f9bc : decode_any W_8f9bc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9c0 : bv 32 := 0x00000613.
Lemma F_8f9c0 : fetch_word Plain.M.loaded_segments (0x8fa18 : word) = Some W_8f9c0.
Proof. vm_refl. Qed.
Lemma D_8f9c0 : decode_any W_8f9c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9c4 : bv 32 := 0x00000793.
Lemma F_8f9c4 : fetch_word Plain.M.loaded_segments (0x8fa1c : word) = Some W_8f9c4.
Proof. vm_refl. Qed.
Lemma D_8f9c4 : decode_any W_8f9c4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9c8 : bv 32 := 0x00000813.
Lemma F_8f9c8 : fetch_word Plain.M.loaded_segments (0x8fa20 : word) = Some W_8f9c8.
Proof. vm_refl. Qed.
Lemma D_8f9c8 : decode_any W_8f9c8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9cc : bv 32 := 0x00000893.
Lemma F_8f9cc : fetch_word Plain.M.loaded_segments (0x8fa24 : word) = Some W_8f9cc.
Proof. vm_refl. Qed.
Lemma D_8f9cc : decode_any W_8f9cc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9d0 : bv 32 := 0xd85e90ef.
Lemma F_8f9d0 : fetch_word Plain.M.loaded_segments (0x8fa28 : word) = Some W_8f9d0.
Proof. vm_refl. Qed.
Lemma D_8f9d0 : decode_any W_8f9d0 = Some (Jal 1 2006404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9d4 : bv 32 := 0x01412683.
Lemma F_8f9d4 : fetch_word Plain.M.loaded_segments (0x8fa2c : word) = Some W_8f9d4.
Proof. vm_refl. Qed.
Lemma D_8f9d4 : decode_any W_8f9d4 = Some (Load SZ4 true 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9d8 : bv 32 := 0x02d05663.
Lemma F_8f9d8 : fetch_word Plain.M.loaded_segments (0x8fa30 : word) = Some W_8f9d8.
Proof. vm_refl. Qed.
Lemma D_8f9d8 : decode_any W_8f9d8 = Some (Branch BC_GE 0 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9dc : bv 32 := 0x03412583.
Lemma F_8f9dc : fetch_word Plain.M.loaded_segments (0x8fa34 : word) = Some W_8f9dc.
Proof. vm_refl. Qed.
Lemma D_8f9dc : decode_any W_8f9dc = Some (Load SZ4 true 11 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9e0 : bv 32 := 0x03012703.
Lemma F_8f9e0 : fetch_word Plain.M.loaded_segments (0x8fa38 : word) = Some W_8f9e0.
Proof. vm_refl. Qed.
Lemma D_8f9e0 : decode_any W_8f9e0 = Some (Load SZ4 true 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9e4 : bv 32 := 0x40d585bb.
Lemma F_8f9e4 : fetch_word Plain.M.loaded_segments (0x8fa3c : word) = Some W_8f9e4.
Proof. vm_refl. Qed.
Lemma D_8f9e4 : decode_any W_8f9e4 = Some (Op32 ALU_SUB 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9e8 : bv 32 := 0x00013023.
Lemma F_8f9e8 : fetch_word Plain.M.loaded_segments (0x8fa40 : word) = Some W_8f9e8.
Proof. vm_refl. Qed.
Lemma D_8f9e8 : decode_any W_8f9e8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9ec : bv 32 := 0x00040513.
Lemma F_8f9ec : fetch_word Plain.M.loaded_segments (0x8fa44 : word) = Some W_8f9ec.
Proof. vm_refl. Qed.
Lemma D_8f9ec : decode_any W_8f9ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9f0 : bv 32 := 0x00000613.
Lemma F_8f9f0 : fetch_word Plain.M.loaded_segments (0x8fa48 : word) = Some W_8f9f0.
Proof. vm_refl. Qed.
Lemma D_8f9f0 : decode_any W_8f9f0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9f4 : bv 32 := 0x00000793.
Lemma F_8f9f4 : fetch_word Plain.M.loaded_segments (0x8fa4c : word) = Some W_8f9f4.
Proof. vm_refl. Qed.
Lemma D_8f9f4 : decode_any W_8f9f4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9f8 : bv 32 := 0x00000813.
Lemma F_8f9f8 : fetch_word Plain.M.loaded_segments (0x8fa50 : word) = Some W_8f9f8.
Proof. vm_refl. Qed.
Lemma D_8f9f8 : decode_any W_8f9f8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f9fc : bv 32 := 0x00000893.
Lemma F_8f9fc : fetch_word Plain.M.loaded_segments (0x8fa54 : word) = Some W_8f9fc.
Proof. vm_refl. Qed.
Lemma D_8f9fc : decode_any W_8f9fc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa00 : bv 32 := 0xd55e90ef.
Lemma F_8fa00 : fetch_word Plain.M.loaded_segments (0x8fa58 : word) = Some W_8fa00.
Proof. vm_refl. Qed.
Lemma D_8fa00 : decode_any W_8fa00 = Some (Jal 1 2006356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa04 : bv 32 := 0x01812703.
Lemma F_8fa04 : fetch_word Plain.M.loaded_segments (0x8fa5c : word) = Some W_8fa04.
Proof. vm_refl. Qed.
Lemma D_8fa04 : decode_any W_8fa04 = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa08 : bv 32 := 0x02e05463.
Lemma F_8fa08 : fetch_word Plain.M.loaded_segments (0x8fa60 : word) = Some W_8fa08.
Proof. vm_refl. Qed.
Lemma D_8fa08 : decode_any W_8fa08 = Some (Branch BC_GE 0 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa0c : bv 32 := 0x03412683.
Lemma F_8fa0c : fetch_word Plain.M.loaded_segments (0x8fa64 : word) = Some W_8fa0c.
Proof. vm_refl. Qed.
Lemma D_8fa0c : decode_any W_8fa0c = Some (Load SZ4 true 13 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa10 : bv 32 := 0x00013023.
Lemma F_8fa10 : fetch_word Plain.M.loaded_segments (0x8fa68 : word) = Some W_8fa10.
Proof. vm_refl. Qed.
Lemma D_8fa10 : decode_any W_8fa10 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa14 : bv 32 := 0x00040513.
Lemma F_8fa14 : fetch_word Plain.M.loaded_segments (0x8fa6c : word) = Some W_8fa14.
Proof. vm_refl. Qed.
Lemma D_8fa14 : decode_any W_8fa14 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa18 : bv 32 := 0x00000593.
Lemma F_8fa18 : fetch_word Plain.M.loaded_segments (0x8fa70 : word) = Some W_8fa18.
Proof. vm_refl. Qed.
Lemma D_8fa18 : decode_any W_8fa18 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa1c : bv 32 := 0x00000613.
Lemma F_8fa1c : fetch_word Plain.M.loaded_segments (0x8fa74 : word) = Some W_8fa1c.
Proof. vm_refl. Qed.
Lemma D_8fa1c : decode_any W_8fa1c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa20 : bv 32 := 0x00000793.
Lemma F_8fa20 : fetch_word Plain.M.loaded_segments (0x8fa78 : word) = Some W_8fa20.
Proof. vm_refl. Qed.
Lemma D_8fa20 : decode_any W_8fa20 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa24 : bv 32 := 0x00000813.
Lemma F_8fa24 : fetch_word Plain.M.loaded_segments (0x8fa7c : word) = Some W_8fa24.
Proof. vm_refl. Qed.
Lemma D_8fa24 : decode_any W_8fa24 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa28 : bv 32 := 0x00000893.
Lemma F_8fa28 : fetch_word Plain.M.loaded_segments (0x8fa80 : word) = Some W_8fa28.
Proof. vm_refl. Qed.
Lemma D_8fa28 : decode_any W_8fa28 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa2c : bv 32 := 0xd29e90ef.
Lemma F_8fa2c : fetch_word Plain.M.loaded_segments (0x8fa84 : word) = Some W_8fa2c.
Proof. vm_refl. Qed.
Lemma D_8fa2c : decode_any W_8fa2c = Some (Jal 1 2006312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa30 : bv 32 := 0x01012703.
Lemma F_8fa30 : fetch_word Plain.M.loaded_segments (0x8fa88 : word) = Some W_8fa30.
Proof. vm_refl. Qed.
Lemma D_8fa30 : decode_any W_8fa30 = Some (Load SZ4 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa34 : bv 32 := 0x02e05663.
Lemma F_8fa34 : fetch_word Plain.M.loaded_segments (0x8fa8c : word) = Some W_8fa34.
Proof. vm_refl. Qed.
Lemma D_8fa34 : decode_any W_8fa34 = Some (Branch BC_GE 0 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa38 : bv 32 := 0x03012603.
Lemma F_8fa38 : fetch_word Plain.M.loaded_segments (0x8fa90 : word) = Some W_8fa38.
Proof. vm_refl. Qed.
Lemma D_8fa38 : decode_any W_8fa38 = Some (Load SZ4 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa3c : bv 32 := 0x03412683.
Lemma F_8fa3c : fetch_word Plain.M.loaded_segments (0x8fa94 : word) = Some W_8fa3c.
Proof. vm_refl. Qed.
Lemma D_8fa3c : decode_any W_8fa3c = Some (Load SZ4 true 13 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa40 : bv 32 := 0x40e6063b.
Lemma F_8fa40 : fetch_word Plain.M.loaded_segments (0x8fa98 : word) = Some W_8fa40.
Proof. vm_refl. Qed.
Lemma D_8fa40 : decode_any W_8fa40 = Some (Op32 ALU_SUB 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa44 : bv 32 := 0x00013023.
Lemma F_8fa44 : fetch_word Plain.M.loaded_segments (0x8fa9c : word) = Some W_8fa44.
Proof. vm_refl. Qed.
Lemma D_8fa44 : decode_any W_8fa44 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa48 : bv 32 := 0x00040513.
Lemma F_8fa48 : fetch_word Plain.M.loaded_segments (0x8faa0 : word) = Some W_8fa48.
Proof. vm_refl. Qed.
Lemma D_8fa48 : decode_any W_8fa48 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa4c : bv 32 := 0x00000593.
Lemma F_8fa4c : fetch_word Plain.M.loaded_segments (0x8faa4 : word) = Some W_8fa4c.
Proof. vm_refl. Qed.
Lemma D_8fa4c : decode_any W_8fa4c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa50 : bv 32 := 0x00000793.
Lemma F_8fa50 : fetch_word Plain.M.loaded_segments (0x8faa8 : word) = Some W_8fa50.
Proof. vm_refl. Qed.
Lemma D_8fa50 : decode_any W_8fa50 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa54 : bv 32 := 0x00000813.
Lemma F_8fa54 : fetch_word Plain.M.loaded_segments (0x8faac : word) = Some W_8fa54.
Proof. vm_refl. Qed.
Lemma D_8fa54 : decode_any W_8fa54 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa58 : bv 32 := 0x00000893.
Lemma F_8fa58 : fetch_word Plain.M.loaded_segments (0x8fab0 : word) = Some W_8fa58.
Proof. vm_refl. Qed.
Lemma D_8fa58 : decode_any W_8fa58 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa5c : bv 32 := 0xcf9e90ef.
Lemma F_8fa5c : fetch_word Plain.M.loaded_segments (0x8fab4 : word) = Some W_8fa5c.
Proof. vm_refl. Qed.
Lemma D_8fa5c : decode_any W_8fa5c = Some (Jal 1 2006264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa60 : bv 32 := 0x00810513.
Lemma F_8fa60 : fetch_word Plain.M.loaded_segments (0x8fab8 : word) = Some W_8fa60.
Proof. vm_refl. Qed.
Lemma D_8fa60 : decode_any W_8fa60 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa64 : bv 32 := 0x880dd0ef.
Lemma F_8fa64 : fetch_word Plain.M.loaded_segments (0x8fabc : word) = Some W_8fa64.
Proof. vm_refl. Qed.
Lemma D_8fa64 : decode_any W_8fa64 = Some (Jal 1 1953920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa68 : bv 32 := 0x05c0006f.
Lemma F_8fa68 : fetch_word Plain.M.loaded_segments (0x8fac0 : word) = Some W_8fa68.
Proof. vm_refl. Qed.
Lemma D_8fa68 : decode_any W_8fa68 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa6c : bv 32 := 0x00083517.
Lemma F_8fa6c : fetch_word Plain.M.loaded_segments (0x8fac4 : word) = Some W_8fa6c.
Proof. vm_refl. Qed.
Lemma D_8fa6c : decode_any W_8fa6c = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa70 : bv 32 := 0xb0453503.
Lemma F_8fa70 : fetch_word Plain.M.loaded_segments (0x8fac8 : word) = Some W_8fa70.
Proof. vm_refl. Qed.
Lemma D_8fa70 : decode_any W_8fa70 = Some (Load SZ8 true 10 10 2820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa74 : bv 32 := 0x00052503.
Lemma F_8fa74 : fetch_word Plain.M.loaded_segments (0x8facc : word) = Some W_8fa74.
Proof. vm_refl. Qed.
Lemma D_8fa74 : decode_any W_8fa74 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa78 : bv 32 := 0x00500593.
Lemma F_8fa78 : fetch_word Plain.M.loaded_segments (0x8fad0 : word) = Some W_8fa78.
Proof. vm_refl. Qed.
Lemma D_8fa78 : decode_any W_8fa78 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa7c : bv 32 := 0x04a5c263.
Lemma F_8fa7c : fetch_word Plain.M.loaded_segments (0x8fad4 : word) = Some W_8fa7c.
Proof. vm_refl. Qed.
Lemma D_8fa7c : decode_any W_8fa7c = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa80 : bv 32 := 0xfff87517.
Lemma F_8fa80 : fetch_word Plain.M.loaded_segments (0x8fad8 : word) = Some W_8fa80.
Proof. vm_refl. Qed.
Lemma D_8fa80 : decode_any W_8fa80 = Some (Auipc 10 1048455, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa84 : bv 32 := 0xfff8e597.
Lemma F_8fa84 : fetch_word Plain.M.loaded_segments (0x8fadc : word) = Some W_8fa84.
Proof. vm_refl. Qed.
Lemma D_8fa84 : decode_any W_8fa84 = Some (Auipc 11 1048462, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa88 : bv 32 := 0xff550513.
Lemma F_8fa88 : fetch_word Plain.M.loaded_segments (0x8fae0 : word) = Some W_8fa88.
Proof. vm_refl. Qed.
Lemma D_8fa88 : decode_any W_8fa88 = Some (OpImm ALU_ADD 10 10 4085, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa8c : bv 32 := 0x34758593.
Lemma F_8fa8c : fetch_word Plain.M.loaded_segments (0x8fae4 : word) = Some W_8fa8c.
Proof. vm_refl. Qed.
Lemma D_8fa8c : decode_any W_8fa8c = Some (OpImm ALU_ADD 11 11 839, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa90 : bv 32 := 0x00000613.
Lemma F_8fa90 : fetch_word Plain.M.loaded_segments (0x8fae8 : word) = Some W_8fa90.
Proof. vm_refl. Qed.
Lemma D_8fa90 : decode_any W_8fa90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa94 : bv 32 := 0x07813083.
Lemma F_8fa94 : fetch_word Plain.M.loaded_segments (0x8faec : word) = Some W_8fa94.
Proof. vm_refl. Qed.
Lemma D_8fa94 : decode_any W_8fa94 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa98 : bv 32 := 0x07013403.
Lemma F_8fa98 : fetch_word Plain.M.loaded_segments (0x8faf0 : word) = Some W_8fa98.
Proof. vm_refl. Qed.
Lemma D_8fa98 : decode_any W_8fa98 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fa9c : bv 32 := 0x06813483.
Lemma F_8fa9c : fetch_word Plain.M.loaded_segments (0x8faf4 : word) = Some W_8fa9c.
Proof. vm_refl. Qed.
Lemma D_8fa9c : decode_any W_8fa9c = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faa0 : bv 32 := 0x06013903.
Lemma F_8faa0 : fetch_word Plain.M.loaded_segments (0x8faf8 : word) = Some W_8faa0.
Proof. vm_refl. Qed.
Lemma D_8faa0 : decode_any W_8faa0 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faa4 : bv 32 := 0x05813983.
Lemma F_8faa4 : fetch_word Plain.M.loaded_segments (0x8fafc : word) = Some W_8faa4.
Proof. vm_refl. Qed.
Lemma D_8faa4 : decode_any W_8faa4 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faa8 : bv 32 := 0x05013a03.
Lemma F_8faa8 : fetch_word Plain.M.loaded_segments (0x8fb00 : word) = Some W_8faa8.
Proof. vm_refl. Qed.
Lemma D_8faa8 : decode_any W_8faa8 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faac : bv 32 := 0x04813a83.
Lemma F_8faac : fetch_word Plain.M.loaded_segments (0x8fb04 : word) = Some W_8faac.
Proof. vm_refl. Qed.
Lemma D_8faac : decode_any W_8faac = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fab0 : bv 32 := 0x04013b03.
Lemma F_8fab0 : fetch_word Plain.M.loaded_segments (0x8fb08 : word) = Some W_8fab0.
Proof. vm_refl. Qed.
Lemma D_8fab0 : decode_any W_8fab0 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fab4 : bv 32 := 0x03813b83.
Lemma F_8fab4 : fetch_word Plain.M.loaded_segments (0x8fb0c : word) = Some W_8fab4.
Proof. vm_refl. Qed.
Lemma D_8fab4 : decode_any W_8fab4 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fab8 : bv 32 := 0x08010113.
Lemma F_8fab8 : fetch_word Plain.M.loaded_segments (0x8fb10 : word) = Some W_8fab8.
Proof. vm_refl. Qed.
Lemma D_8fab8 : decode_any W_8fab8 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fabc : bv 32 := 0xe08d306f.
Lemma F_8fabc : fetch_word Plain.M.loaded_segments (0x8fb14 : word) = Some W_8fabc.
Proof. vm_refl. Qed.
Lemma D_8fabc : decode_any W_8fabc = Some (Jal 0 1914376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fac4 : bv 32 := 0x00040513.
Lemma F_8fac4 : fetch_word Plain.M.loaded_segments (0x8fb1c : word) = Some W_8fac4.
Proof. vm_refl. Qed.
Lemma D_8fac4 : decode_any W_8fac4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fac8 : bv 32 := 0x07813083.
Lemma F_8fac8 : fetch_word Plain.M.loaded_segments (0x8fb20 : word) = Some W_8fac8.
Proof. vm_refl. Qed.
Lemma D_8fac8 : decode_any W_8fac8 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8facc : bv 32 := 0x07013403.
Lemma F_8facc : fetch_word Plain.M.loaded_segments (0x8fb24 : word) = Some W_8facc.
Proof. vm_refl. Qed.
Lemma D_8facc : decode_any W_8facc = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fad0 : bv 32 := 0x06813483.
Lemma F_8fad0 : fetch_word Plain.M.loaded_segments (0x8fb28 : word) = Some W_8fad0.
Proof. vm_refl. Qed.
Lemma D_8fad0 : decode_any W_8fad0 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fad4 : bv 32 := 0x06013903.
Lemma F_8fad4 : fetch_word Plain.M.loaded_segments (0x8fb2c : word) = Some W_8fad4.
Proof. vm_refl. Qed.
Lemma D_8fad4 : decode_any W_8fad4 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fad8 : bv 32 := 0x05813983.
Lemma F_8fad8 : fetch_word Plain.M.loaded_segments (0x8fb30 : word) = Some W_8fad8.
Proof. vm_refl. Qed.
Lemma D_8fad8 : decode_any W_8fad8 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fadc : bv 32 := 0x05013a03.
Lemma F_8fadc : fetch_word Plain.M.loaded_segments (0x8fb34 : word) = Some W_8fadc.
Proof. vm_refl. Qed.
Lemma D_8fadc : decode_any W_8fadc = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fae0 : bv 32 := 0x04813a83.
Lemma F_8fae0 : fetch_word Plain.M.loaded_segments (0x8fb38 : word) = Some W_8fae0.
Proof. vm_refl. Qed.
Lemma D_8fae0 : decode_any W_8fae0 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fae4 : bv 32 := 0x04013b03.
Lemma F_8fae4 : fetch_word Plain.M.loaded_segments (0x8fb3c : word) = Some W_8fae4.
Proof. vm_refl. Qed.
Lemma D_8fae4 : decode_any W_8fae4 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fae8 : bv 32 := 0x03813b83.
Lemma F_8fae8 : fetch_word Plain.M.loaded_segments (0x8fb40 : word) = Some W_8fae8.
Proof. vm_refl. Qed.
Lemma D_8fae8 : decode_any W_8fae8 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faec : bv 32 := 0x08010113.
Lemma F_8faec : fetch_word Plain.M.loaded_segments (0x8fb44 : word) = Some W_8faec.
Proof. vm_refl. Qed.
Lemma D_8faec : decode_any W_8faec = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faf0 : bv 32 := 0x00008067.
Lemma F_8faf0 : fetch_word Plain.M.loaded_segments (0x8fb48 : word) = Some W_8faf0.
Proof. vm_refl. Qed.
Lemma D_8faf0 : decode_any W_8faf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
