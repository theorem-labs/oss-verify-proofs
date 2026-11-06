(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7596c : bv 32 := 0x00757593.
Lemma F_7596c : fetch_word Plain.M.loaded_segments (0x7596c : word) = Some W_7596c.
Proof. vm_refl. Qed.
Lemma D_7596c : decode_any W_7596c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75970 : bv 32 := 0x00050613.
Lemma F_75970 : fetch_word Plain.M.loaded_segments (0x75970 : word) = Some W_75970.
Proof. vm_refl. Qed.
Lemma D_75970 : decode_any W_75970 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75974 : bv 32 := 0x02058a63.
Lemma F_75974 : fetch_word Plain.M.loaded_segments (0x75974 : word) = Some W_75974.
Proof. vm_refl. Qed.
Lemma D_75974 : decode_any W_75974 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75978 : bv 32 := 0x00054583.
Lemma F_75978 : fetch_word Plain.M.loaded_segments (0x75978 : word) = Some W_75978.
Proof. vm_refl. Qed.
Lemma D_75978 : decode_any W_75978 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7597c : bv 32 := 0x06058c63.
Lemma F_7597c : fetch_word Plain.M.loaded_segments (0x7597c : word) = Some W_7597c.
Proof. vm_refl. Qed.
Lemma D_7597c : decode_any W_7597c = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75980 : bv 32 := 0x00150613.
Lemma F_75980 : fetch_word Plain.M.loaded_segments (0x75980 : word) = Some W_75980.
Proof. vm_refl. Qed.
Lemma D_75980 : decode_any W_75980 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75984 : bv 32 := 0x00050593.
Lemma F_75984 : fetch_word Plain.M.loaded_segments (0x75984 : word) = Some W_75984.
Proof. vm_refl. Qed.
Lemma D_75984 : decode_any W_75984 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75988 : bv 32 := 0x00158693.
Lemma F_75988 : fetch_word Plain.M.loaded_segments (0x75988 : word) = Some W_75988.
Proof. vm_refl. Qed.
Lemma D_75988 : decode_any W_75988 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7598c : bv 32 := 0x0076f693.
Lemma F_7598c : fetch_word Plain.M.loaded_segments (0x7598c : word) = Some W_7598c.
Proof. vm_refl. Qed.
Lemma D_7598c : decode_any W_7598c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75990 : bv 32 := 0x00068c63.
Lemma F_75990 : fetch_word Plain.M.loaded_segments (0x75990 : word) = Some W_75990.
Proof. vm_refl. Qed.
Lemma D_75990 : decode_any W_75990 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75994 : bv 32 := 0x00064683.
Lemma F_75994 : fetch_word Plain.M.loaded_segments (0x75994 : word) = Some W_75994.
Proof. vm_refl. Qed.
Lemma D_75994 : decode_any W_75994 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75998 : bv 32 := 0x00160613.
Lemma F_75998 : fetch_word Plain.M.loaded_segments (0x75998 : word) = Some W_75998.
Proof. vm_refl. Qed.
Lemma D_75998 : decode_any W_75998 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7599c : bv 32 := 0x00158593.
Lemma F_7599c : fetch_word Plain.M.loaded_segments (0x7599c : word) = Some W_7599c.
Proof. vm_refl. Qed.
Lemma D_7599c : decode_any W_7599c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759a0 : bv 32 := 0xfe0694e3.
Lemma F_759a0 : fetch_word Plain.M.loaded_segments (0x759a0 : word) = Some W_759a0.
Proof. vm_refl. Qed.
Lemma D_759a0 : decode_any W_759a0 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759a4 : bv 32 := 0x0480006f.
Lemma F_759a4 : fetch_word Plain.M.loaded_segments (0x759a4 : word) = Some W_759a4.
Proof. vm_refl. Qed.
Lemma D_759a4 : decode_any W_759a4 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759a8 : bv 32 := 0xfff9f597.
Lemma F_759a8 : fetch_word Plain.M.loaded_segments (0x759a8 : word) = Some W_759a8.
Proof. vm_refl. Qed.
Lemma D_759a8 : decode_any W_759a8 = Some (Auipc 11 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759ac : bv 32 := 0xfff9f717.
Lemma F_759ac : fetch_word Plain.M.loaded_segments (0x759ac : word) = Some W_759ac.
Proof. vm_refl. Qed.
Lemma D_759ac : decode_any W_759ac = Some (Auipc 14 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759b0 : bv 32 := 0x4a05b683.
Lemma F_759b0 : fetch_word Plain.M.loaded_segments (0x759b0 : word) = Some W_759b0.
Proof. vm_refl. Qed.
Lemma D_759b0 : decode_any W_759b0 = Some (Load SZ8 true 13 11 1184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759b4 : bv 32 := 0x48473703.
Lemma F_759b4 : fetch_word Plain.M.loaded_segments (0x759b4 : word) = Some W_759b4.
Proof. vm_refl. Qed.
Lemma D_759b4 : decode_any W_759b4 = Some (Load SZ8 true 14 14 1156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759b8 : bv 32 := 0xff760593.
Lemma F_759b8 : fetch_word Plain.M.loaded_segments (0x759b8 : word) = Some W_759b8.
Proof. vm_refl. Qed.
Lemma D_759b8 : decode_any W_759b8 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759bc : bv 32 := 0xff860613.
Lemma F_759bc : fetch_word Plain.M.loaded_segments (0x759bc : word) = Some W_759bc.
Proof. vm_refl. Qed.
Lemma D_759bc : decode_any W_759bc = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759c0 : bv 32 := 0x00863783.
Lemma F_759c0 : fetch_word Plain.M.loaded_segments (0x759c0 : word) = Some W_759c0.
Proof. vm_refl. Qed.
Lemma D_759c0 : decode_any W_759c0 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759c4 : bv 32 := 0x00860613.
Lemma F_759c4 : fetch_word Plain.M.loaded_segments (0x759c4 : word) = Some W_759c4.
Proof. vm_refl. Qed.
Lemma D_759c4 : decode_any W_759c4 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759c8 : bv 32 := 0x40f68833.
Lemma F_759c8 : fetch_word Plain.M.loaded_segments (0x759c8 : word) = Some W_759c8.
Proof. vm_refl. Qed.
Lemma D_759c8 : decode_any W_759c8 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759cc : bv 32 := 0x00f867b3.
Lemma F_759cc : fetch_word Plain.M.loaded_segments (0x759cc : word) = Some W_759cc.
Proof. vm_refl. Qed.
Lemma D_759cc : decode_any W_759cc = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759d0 : bv 32 := 0x00e7f7b3.
Lemma F_759d0 : fetch_word Plain.M.loaded_segments (0x759d0 : word) = Some W_759d0.
Proof. vm_refl. Qed.
Lemma D_759d0 : decode_any W_759d0 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759d4 : bv 32 := 0x00858593.
Lemma F_759d4 : fetch_word Plain.M.loaded_segments (0x759d4 : word) = Some W_759d4.
Proof. vm_refl. Qed.
Lemma D_759d4 : decode_any W_759d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759d8 : bv 32 := 0xfee784e3.
Lemma F_759d8 : fetch_word Plain.M.loaded_segments (0x759d8 : word) = Some W_759d8.
Proof. vm_refl. Qed.
Lemma D_759d8 : decode_any W_759d8 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759dc : bv 32 := 0x00064683.
Lemma F_759dc : fetch_word Plain.M.loaded_segments (0x759dc : word) = Some W_759dc.
Proof. vm_refl. Qed.
Lemma D_759dc : decode_any W_759dc = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759e0 : bv 32 := 0x00160613.
Lemma F_759e0 : fetch_word Plain.M.loaded_segments (0x759e0 : word) = Some W_759e0.
Proof. vm_refl. Qed.
Lemma D_759e0 : decode_any W_759e0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759e4 : bv 32 := 0x00158593.
Lemma F_759e4 : fetch_word Plain.M.loaded_segments (0x759e4 : word) = Some W_759e4.
Proof. vm_refl. Qed.
Lemma D_759e4 : decode_any W_759e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759e8 : bv 32 := 0xfe069ae3.
Lemma F_759e8 : fetch_word Plain.M.loaded_segments (0x759e8 : word) = Some W_759e8.
Proof. vm_refl. Qed.
Lemma D_759e8 : decode_any W_759e8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759ec : bv 32 := 0x40a58533.
Lemma F_759ec : fetch_word Plain.M.loaded_segments (0x759ec : word) = Some W_759ec.
Proof. vm_refl. Qed.
Lemma D_759ec : decode_any W_759ec = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759f0 : bv 32 := 0x00008067.
Lemma F_759f0 : fetch_word Plain.M.loaded_segments (0x759f0 : word) = Some W_759f0.
Proof. vm_refl. Qed.
Lemma D_759f0 : decode_any W_759f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759f4 : bv 32 := 0x40a50533.
Lemma F_759f4 : fetch_word Plain.M.loaded_segments (0x759f4 : word) = Some W_759f4.
Proof. vm_refl. Qed.
Lemma D_759f4 : decode_any W_759f4 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759f8 : bv 32 := 0x00008067.
Lemma F_759f8 : fetch_word Plain.M.loaded_segments (0x759f8 : word) = Some W_759f8.
Proof. vm_refl. Qed.
Lemma D_759f8 : decode_any W_759f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_759fc : bv 32 := 0xff010113.
Lemma F_759fc : fetch_word Plain.M.loaded_segments (0x759fc : word) = Some W_759fc.
Proof. vm_refl. Qed.
Lemma D_759fc : decode_any W_759fc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a00 : bv 32 := 0x00113423.
Lemma F_75a00 : fetch_word Plain.M.loaded_segments (0x75a00 : word) = Some W_75a00.
Proof. vm_refl. Qed.
Lemma D_75a00 : decode_any W_75a00 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a04 : bv 32 := 0x00813023.
Lemma F_75a04 : fetch_word Plain.M.loaded_segments (0x75a04 : word) = Some W_75a04.
Proof. vm_refl. Qed.
Lemma D_75a04 : decode_any W_75a04 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a08 : bv 32 := 0x00050413.
Lemma F_75a08 : fetch_word Plain.M.loaded_segments (0x75a08 : word) = Some W_75a08.
Proof. vm_refl. Qed.
Lemma D_75a08 : decode_any W_75a08 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a0c : bv 32 := 0x018000ef.
Lemma F_75a0c : fetch_word Plain.M.loaded_segments (0x75a0c : word) = Some W_75a0c.
Proof. vm_refl. Qed.
Lemma D_75a0c : decode_any W_75a0c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a10 : bv 32 := 0x00040513.
Lemma F_75a10 : fetch_word Plain.M.loaded_segments (0x75a10 : word) = Some W_75a10.
Proof. vm_refl. Qed.
Lemma D_75a10 : decode_any W_75a10 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a14 : bv 32 := 0x00813083.
Lemma F_75a14 : fetch_word Plain.M.loaded_segments (0x75a14 : word) = Some W_75a14.
Proof. vm_refl. Qed.
Lemma D_75a14 : decode_any W_75a14 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a18 : bv 32 := 0x00013403.
Lemma F_75a18 : fetch_word Plain.M.loaded_segments (0x75a18 : word) = Some W_75a18.
Proof. vm_refl. Qed.
Lemma D_75a18 : decode_any W_75a18 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a1c : bv 32 := 0x01010113.
Lemma F_75a1c : fetch_word Plain.M.loaded_segments (0x75a1c : word) = Some W_75a1c.
Proof. vm_refl. Qed.
Lemma D_75a1c : decode_any W_75a1c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a20 : bv 32 := 0x00008067.
Lemma F_75a20 : fetch_word Plain.M.loaded_segments (0x75a20 : word) = Some W_75a20.
Proof. vm_refl. Qed.
Lemma D_75a20 : decode_any W_75a20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a24 : bv 32 := 0xff010113.
Lemma F_75a24 : fetch_word Plain.M.loaded_segments (0x75a24 : word) = Some W_75a24.
Proof. vm_refl. Qed.
Lemma D_75a24 : decode_any W_75a24 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a28 : bv 32 := 0x00113423.
Lemma F_75a28 : fetch_word Plain.M.loaded_segments (0x75a28 : word) = Some W_75a28.
Proof. vm_refl. Qed.
Lemma D_75a28 : decode_any W_75a28 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a2c : bv 32 := 0x00813023.
Lemma F_75a2c : fetch_word Plain.M.loaded_segments (0x75a2c : word) = Some W_75a2c.
Proof. vm_refl. Qed.
Lemma D_75a2c : decode_any W_75a2c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a30 : bv 32 := 0x00050413.
Lemma F_75a30 : fetch_word Plain.M.loaded_segments (0x75a30 : word) = Some W_75a30.
Proof. vm_refl. Qed.
Lemma D_75a30 : decode_any W_75a30 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a34 : bv 32 := 0x00a5c6b3.
Lemma F_75a34 : fetch_word Plain.M.loaded_segments (0x75a34 : word) = Some W_75a34.
Proof. vm_refl. Qed.
Lemma D_75a34 : decode_any W_75a34 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a38 : bv 32 := 0x0076f693.
Lemma F_75a38 : fetch_word Plain.M.loaded_segments (0x75a38 : word) = Some W_75a38.
Proof. vm_refl. Qed.
Lemma D_75a38 : decode_any W_75a38 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a3c : bv 32 := 0x02068663.
Lemma F_75a3c : fetch_word Plain.M.loaded_segments (0x75a3c : word) = Some W_75a3c.
Proof. vm_refl. Qed.
Lemma D_75a3c : decode_any W_75a3c = Some (Branch BC_EQ 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a40 : bv 32 := 0x0c060263.
Lemma F_75a40 : fetch_word Plain.M.loaded_segments (0x75a40 : word) = Some W_75a40.
Proof. vm_refl. Qed.
Lemma D_75a40 : decode_any W_75a40 = Some (Branch BC_EQ 12 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a44 : bv 32 := 0x00060693.
Lemma F_75a44 : fetch_word Plain.M.loaded_segments (0x75a44 : word) = Some W_75a44.
Proof. vm_refl. Qed.
Lemma D_75a44 : decode_any W_75a44 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a48 : bv 32 := 0x0005c603.
Lemma F_75a48 : fetch_word Plain.M.loaded_segments (0x75a48 : word) = Some W_75a48.
Proof. vm_refl. Qed.
Lemma D_75a48 : decode_any W_75a48 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a4c : bv 32 := 0x00c40023.
Lemma F_75a4c : fetch_word Plain.M.loaded_segments (0x75a4c : word) = Some W_75a4c.
Proof. vm_refl. Qed.
Lemma D_75a4c : decode_any W_75a4c = Some (Store SZ1 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a50 : bv 32 := 0x0a060c63.
Lemma F_75a50 : fetch_word Plain.M.loaded_segments (0x75a50 : word) = Some W_75a50.
Proof. vm_refl. Qed.
Lemma D_75a50 : decode_any W_75a50 = Some (Branch BC_EQ 12 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a54 : bv 32 := 0xfff68693.
Lemma F_75a54 : fetch_word Plain.M.loaded_segments (0x75a54 : word) = Some W_75a54.
Proof. vm_refl. Qed.
Lemma D_75a54 : decode_any W_75a54 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a58 : bv 32 := 0x00158593.
Lemma F_75a58 : fetch_word Plain.M.loaded_segments (0x75a58 : word) = Some W_75a58.
Proof. vm_refl. Qed.
Lemma D_75a58 : decode_any W_75a58 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a5c : bv 32 := 0x00140413.
Lemma F_75a5c : fetch_word Plain.M.loaded_segments (0x75a5c : word) = Some W_75a5c.
Proof. vm_refl. Qed.
Lemma D_75a5c : decode_any W_75a5c = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a60 : bv 32 := 0xfe0694e3.
Lemma F_75a60 : fetch_word Plain.M.loaded_segments (0x75a60 : word) = Some W_75a60.
Proof. vm_refl. Qed.
Lemma D_75a60 : decode_any W_75a60 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a64 : bv 32 := 0x0a40006f.
Lemma F_75a64 : fetch_word Plain.M.loaded_segments (0x75a64 : word) = Some W_75a64.
Proof. vm_refl. Qed.
Lemma D_75a64 : decode_any W_75a64 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a68 : bv 32 := 0x0075f693.
Lemma F_75a68 : fetch_word Plain.M.loaded_segments (0x75a68 : word) = Some W_75a68.
Proof. vm_refl. Qed.
Lemma D_75a68 : decode_any W_75a68 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a6c : bv 32 := 0x00c03733.
Lemma F_75a6c : fetch_word Plain.M.loaded_segments (0x75a6c : word) = Some W_75a6c.
Proof. vm_refl. Qed.
Lemma D_75a6c : decode_any W_75a6c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a70 : bv 32 := 0x04068063.
Lemma F_75a70 : fetch_word Plain.M.loaded_segments (0x75a70 : word) = Some W_75a70.
Proof. vm_refl. Qed.
Lemma D_75a70 : decode_any W_75a70 = Some (Branch BC_EQ 13 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a74 : bv 32 := 0x02060e63.
Lemma F_75a74 : fetch_word Plain.M.loaded_segments (0x75a74 : word) = Some W_75a74.
Proof. vm_refl. Qed.
Lemma D_75a74 : decode_any W_75a74 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a78 : bv 32 := 0x00158793.
Lemma F_75a78 : fetch_word Plain.M.loaded_segments (0x75a78 : word) = Some W_75a78.
Proof. vm_refl. Qed.
Lemma D_75a78 : decode_any W_75a78 = Some (OpImm ALU_ADD 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a7c : bv 32 := 0x00100813.
Lemma F_75a7c : fetch_word Plain.M.loaded_segments (0x75a7c : word) = Some W_75a7c.
Proof. vm_refl. Qed.
Lemma D_75a7c : decode_any W_75a7c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a80 : bv 32 := 0x0005c703.
Lemma F_75a80 : fetch_word Plain.M.loaded_segments (0x75a80 : word) = Some W_75a80.
Proof. vm_refl. Qed.
Lemma D_75a80 : decode_any W_75a80 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a84 : bv 32 := 0x00060693.
Lemma F_75a84 : fetch_word Plain.M.loaded_segments (0x75a84 : word) = Some W_75a84.
Proof. vm_refl. Qed.
Lemma D_75a84 : decode_any W_75a84 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a88 : bv 32 := 0x00e40023.
Lemma F_75a88 : fetch_word Plain.M.loaded_segments (0x75a88 : word) = Some W_75a88.
Proof. vm_refl. Qed.
Lemma D_75a88 : decode_any W_75a88 = Some (Store SZ1 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a8c : bv 32 := 0x06070e63.
Lemma F_75a8c : fetch_word Plain.M.loaded_segments (0x75a8c : word) = Some W_75a8c.
Proof. vm_refl. Qed.
Lemma D_75a8c : decode_any W_75a8c = Some (Branch BC_EQ 14 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a90 : bv 32 := 0xfff68613.
Lemma F_75a90 : fetch_word Plain.M.loaded_segments (0x75a90 : word) = Some W_75a90.
Proof. vm_refl. Qed.
Lemma D_75a90 : decode_any W_75a90 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a94 : bv 32 := 0x00158593.
Lemma F_75a94 : fetch_word Plain.M.loaded_segments (0x75a94 : word) = Some W_75a94.
Proof. vm_refl. Qed.
Lemma D_75a94 : decode_any W_75a94 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a98 : bv 32 := 0x00140413.
Lemma F_75a98 : fetch_word Plain.M.loaded_segments (0x75a98 : word) = Some W_75a98.
Proof. vm_refl. Qed.
Lemma D_75a98 : decode_any W_75a98 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a9c : bv 32 := 0x0077f893.
Lemma F_75a9c : fetch_word Plain.M.loaded_segments (0x75a9c : word) = Some W_75a9c.
Proof. vm_refl. Qed.
Lemma D_75a9c : decode_any W_75a9c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aa0 : bv 32 := 0x00c03733.
Lemma F_75aa0 : fetch_word Plain.M.loaded_segments (0x75aa0 : word) = Some W_75aa0.
Proof. vm_refl. Qed.
Lemma D_75aa0 : decode_any W_75aa0 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aa4 : bv 32 := 0x00088663.
Lemma F_75aa4 : fetch_word Plain.M.loaded_segments (0x75aa4 : word) = Some W_75aa4.
Proof. vm_refl. Qed.
Lemma D_75aa4 : decode_any W_75aa4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aa8 : bv 32 := 0x00178793.
Lemma F_75aa8 : fetch_word Plain.M.loaded_segments (0x75aa8 : word) = Some W_75aa8.
Proof. vm_refl. Qed.
Lemma D_75aa8 : decode_any W_75aa8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aac : bv 32 := 0xfd069ae3.
Lemma F_75aac : fetch_word Plain.M.loaded_segments (0x75aac : word) = Some W_75aac.
Proof. vm_refl. Qed.
Lemma D_75aac : decode_any W_75aac = Some (Branch BC_NE 13 16 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ab0 : bv 32 := 0x04070a63.
Lemma F_75ab0 : fetch_word Plain.M.loaded_segments (0x75ab0 : word) = Some W_75ab0.
Proof. vm_refl. Qed.
Lemma D_75ab0 : decode_any W_75ab0 = Some (Branch BC_EQ 14 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ab4 : bv 32 := 0x0005c683.
Lemma F_75ab4 : fetch_word Plain.M.loaded_segments (0x75ab4 : word) = Some W_75ab4.
Proof. vm_refl. Qed.
Lemma D_75ab4 : decode_any W_75ab4 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ab8 : bv 32 := 0x06068a63.
Lemma F_75ab8 : fetch_word Plain.M.loaded_segments (0x75ab8 : word) = Some W_75ab8.
Proof. vm_refl. Qed.
Lemma D_75ab8 : decode_any W_75ab8 = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75abc : bv 32 := 0x00800693.
Lemma F_75abc : fetch_word Plain.M.loaded_segments (0x75abc : word) = Some W_75abc.
Proof. vm_refl. Qed.
Lemma D_75abc : decode_any W_75abc = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ac0 : bv 32 := 0xf8d660e3.
Lemma F_75ac0 : fetch_word Plain.M.loaded_segments (0x75ac0 : word) = Some W_75ac0.
Proof. vm_refl. Qed.
Lemma D_75ac0 : decode_any W_75ac0 = Some (Branch BC_LTU 12 13 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ac4 : bv 32 := 0xfff9f697.
Lemma F_75ac4 : fetch_word Plain.M.loaded_segments (0x75ac4 : word) = Some W_75ac4.
Proof. vm_refl. Qed.
Lemma D_75ac4 : decode_any W_75ac4 = Some (Auipc 13 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ac8 : bv 32 := 0xfff9f717.
Lemma F_75ac8 : fetch_word Plain.M.loaded_segments (0x75ac8 : word) = Some W_75ac8.
Proof. vm_refl. Qed.
Lemma D_75ac8 : decode_any W_75ac8 = Some (Auipc 14 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75acc : bv 32 := 0x3846b683.
Lemma F_75acc : fetch_word Plain.M.loaded_segments (0x75acc : word) = Some W_75acc.
Proof. vm_refl. Qed.
Lemma D_75acc : decode_any W_75acc = Some (Load SZ8 true 13 13 900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ad0 : bv 32 := 0x36873703.
Lemma F_75ad0 : fetch_word Plain.M.loaded_segments (0x75ad0 : word) = Some W_75ad0.
Proof. vm_refl. Qed.
Lemma D_75ad0 : decode_any W_75ad0 = Some (Load SZ8 true 14 14 872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ad4 : bv 32 := 0x00700793.
Lemma F_75ad4 : fetch_word Plain.M.loaded_segments (0x75ad4 : word) = Some W_75ad4.
Proof. vm_refl. Qed.
Lemma D_75ad4 : decode_any W_75ad4 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ad8 : bv 32 := 0x0005b803.
Lemma F_75ad8 : fetch_word Plain.M.loaded_segments (0x75ad8 : word) = Some W_75ad8.
Proof. vm_refl. Qed.
Lemma D_75ad8 : decode_any W_75ad8 = Some (Load SZ8 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75adc : bv 32 := 0x410688b3.
Lemma F_75adc : fetch_word Plain.M.loaded_segments (0x75adc : word) = Some W_75adc.
Proof. vm_refl. Qed.
Lemma D_75adc : decode_any W_75adc = Some (Op ALU_SUB 17 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ae0 : bv 32 := 0x0108e8b3.
Lemma F_75ae0 : fetch_word Plain.M.loaded_segments (0x75ae0 : word) = Some W_75ae0.
Proof. vm_refl. Qed.
Lemma D_75ae0 : decode_any W_75ae0 = Some (Op ALU_OR 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ae4 : bv 32 := 0x00e8f8b3.
Lemma F_75ae4 : fetch_word Plain.M.loaded_segments (0x75ae4 : word) = Some W_75ae4.
Proof. vm_refl. Qed.
Lemma D_75ae4 : decode_any W_75ae4 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ae8 : bv 32 := 0xf4e89ee3.
Lemma F_75ae8 : fetch_word Plain.M.loaded_segments (0x75ae8 : word) = Some W_75ae8.
Proof. vm_refl. Qed.
Lemma D_75ae8 : decode_any W_75ae8 = Some (Branch BC_NE 17 14 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aec : bv 32 := 0x01043023.
Lemma F_75aec : fetch_word Plain.M.loaded_segments (0x75aec : word) = Some W_75aec.
Proof. vm_refl. Qed.
Lemma D_75aec : decode_any W_75aec = Some (Store SZ8 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75af0 : bv 32 := 0xff860613.
Lemma F_75af0 : fetch_word Plain.M.loaded_segments (0x75af0 : word) = Some W_75af0.
Proof. vm_refl. Qed.
Lemma D_75af0 : decode_any W_75af0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75af4 : bv 32 := 0x00858593.
Lemma F_75af4 : fetch_word Plain.M.loaded_segments (0x75af4 : word) = Some W_75af4.
Proof. vm_refl. Qed.
Lemma D_75af4 : decode_any W_75af4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75af8 : bv 32 := 0x00840413.
Lemma F_75af8 : fetch_word Plain.M.loaded_segments (0x75af8 : word) = Some W_75af8.
Proof. vm_refl. Qed.
Lemma D_75af8 : decode_any W_75af8 = Some (OpImm ALU_ADD 8 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75afc : bv 32 := 0xfcc7eee3.
Lemma F_75afc : fetch_word Plain.M.loaded_segments (0x75afc : word) = Some W_75afc.
Proof. vm_refl. Qed.
Lemma D_75afc : decode_any W_75afc = Some (Branch BC_LTU 15 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b00 : bv 32 := 0xf41ff06f.
Lemma F_75b00 : fetch_word Plain.M.loaded_segments (0x75b00 : word) = Some W_75b00.
Proof. vm_refl. Qed.
Lemma D_75b00 : decode_any W_75b00 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b04 : bv 32 := 0x00000693.
Lemma F_75b04 : fetch_word Plain.M.loaded_segments (0x75b04 : word) = Some W_75b04.
Proof. vm_refl. Qed.
Lemma D_75b04 : decode_any W_75b04 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b08 : bv 32 := 0x00040513.
Lemma F_75b08 : fetch_word Plain.M.loaded_segments (0x75b08 : word) = Some W_75b08.
Proof. vm_refl. Qed.
Lemma D_75b08 : decode_any W_75b08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b0c : bv 32 := 0x00000593.
Lemma F_75b0c : fetch_word Plain.M.loaded_segments (0x75b0c : word) = Some W_75b0c.
Proof. vm_refl. Qed.
Lemma D_75b0c : decode_any W_75b0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b10 : bv 32 := 0x00068613.
Lemma F_75b10 : fetch_word Plain.M.loaded_segments (0x75b10 : word) = Some W_75b10.
Proof. vm_refl. Qed.
Lemma D_75b10 : decode_any W_75b10 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b14 : bv 32 := 0xc91ff0ef.
Lemma F_75b14 : fetch_word Plain.M.loaded_segments (0x75b14 : word) = Some W_75b14.
Proof. vm_refl. Qed.
Lemma D_75b14 : decode_any W_75b14 = Some (Jal 1 2096272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b18 : bv 32 := 0x00040513.
Lemma F_75b18 : fetch_word Plain.M.loaded_segments (0x75b18 : word) = Some W_75b18.
Proof. vm_refl. Qed.
Lemma D_75b18 : decode_any W_75b18 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b1c : bv 32 := 0x00813083.
Lemma F_75b1c : fetch_word Plain.M.loaded_segments (0x75b1c : word) = Some W_75b1c.
Proof. vm_refl. Qed.
Lemma D_75b1c : decode_any W_75b1c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b20 : bv 32 := 0x00013403.
Lemma F_75b20 : fetch_word Plain.M.loaded_segments (0x75b20 : word) = Some W_75b20.
Proof. vm_refl. Qed.
Lemma D_75b20 : decode_any W_75b20 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b24 : bv 32 := 0x01010113.
Lemma F_75b24 : fetch_word Plain.M.loaded_segments (0x75b24 : word) = Some W_75b24.
Proof. vm_refl. Qed.
Lemma D_75b24 : decode_any W_75b24 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b28 : bv 32 := 0x00008067.
Lemma F_75b28 : fetch_word Plain.M.loaded_segments (0x75b28 : word) = Some W_75b28.
Proof. vm_refl. Qed.
Lemma D_75b28 : decode_any W_75b28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b2c : bv 32 := 0x00060693.
Lemma F_75b2c : fetch_word Plain.M.loaded_segments (0x75b2c : word) = Some W_75b2c.
Proof. vm_refl. Qed.
Lemma D_75b2c : decode_any W_75b2c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b30 : bv 32 := 0xfd9ff06f.
Lemma F_75b30 : fetch_word Plain.M.loaded_segments (0x75b30 : word) = Some W_75b30.
Proof. vm_refl. Qed.
Lemma D_75b30 : decode_any W_75b30 = Some (Jal 0 2097112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b34 : bv 32 := 0xfe010113.
Lemma F_75b34 : fetch_word Plain.M.loaded_segments (0x75b34 : word) = Some W_75b34.
Proof. vm_refl. Qed.
Lemma D_75b34 : decode_any W_75b34 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b38 : bv 32 := 0x00113c23.
Lemma F_75b38 : fetch_word Plain.M.loaded_segments (0x75b38 : word) = Some W_75b38.
Proof. vm_refl. Qed.
Lemma D_75b38 : decode_any W_75b38 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b3c : bv 32 := 0x00813823.
Lemma F_75b3c : fetch_word Plain.M.loaded_segments (0x75b3c : word) = Some W_75b3c.
Proof. vm_refl. Qed.
Lemma D_75b3c : decode_any W_75b3c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b40 : bv 32 := 0x00913423.
Lemma F_75b40 : fetch_word Plain.M.loaded_segments (0x75b40 : word) = Some W_75b40.
Proof. vm_refl. Qed.
Lemma D_75b40 : decode_any W_75b40 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b44 : bv 32 := 0x00058413.
Lemma F_75b44 : fetch_word Plain.M.loaded_segments (0x75b44 : word) = Some W_75b44.
Proof. vm_refl. Qed.
Lemma D_75b44 : decode_any W_75b44 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b48 : bv 32 := 0x00050493.
Lemma F_75b48 : fetch_word Plain.M.loaded_segments (0x75b48 : word) = Some W_75b48.
Proof. vm_refl. Qed.
Lemma D_75b48 : decode_any W_75b48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b4c : bv 32 := 0x00000593.
Lemma F_75b4c : fetch_word Plain.M.loaded_segments (0x75b4c : word) = Some W_75b4c.
Proof. vm_refl. Qed.
Lemma D_75b4c : decode_any W_75b4c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b50 : bv 32 := 0x00040613.
Lemma F_75b50 : fetch_word Plain.M.loaded_segments (0x75b50 : word) = Some W_75b50.
Proof. vm_refl. Qed.
Lemma D_75b50 : decode_any W_75b50 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b54 : bv 32 := 0xdd4ff0ef.
Lemma F_75b54 : fetch_word Plain.M.loaded_segments (0x75b54 : word) = Some W_75b54.
Proof. vm_refl. Qed.
Lemma D_75b54 : decode_any W_75b54 = Some (Jal 1 2094548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b58 : bv 32 := 0x00050463.
Lemma F_75b58 : fetch_word Plain.M.loaded_segments (0x75b58 : word) = Some W_75b58.
Proof. vm_refl. Qed.
Lemma D_75b58 : decode_any W_75b58 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b5c : bv 32 := 0x40950433.
Lemma F_75b5c : fetch_word Plain.M.loaded_segments (0x75b5c : word) = Some W_75b5c.
Proof. vm_refl. Qed.
Lemma D_75b5c : decode_any W_75b5c = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b60 : bv 32 := 0x00040513.
Lemma F_75b60 : fetch_word Plain.M.loaded_segments (0x75b60 : word) = Some W_75b60.
Proof. vm_refl. Qed.
Lemma D_75b60 : decode_any W_75b60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b64 : bv 32 := 0x01813083.
Lemma F_75b64 : fetch_word Plain.M.loaded_segments (0x75b64 : word) = Some W_75b64.
Proof. vm_refl. Qed.
Lemma D_75b64 : decode_any W_75b64 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b68 : bv 32 := 0x01013403.
Lemma F_75b68 : fetch_word Plain.M.loaded_segments (0x75b68 : word) = Some W_75b68.
Proof. vm_refl. Qed.
Lemma D_75b68 : decode_any W_75b68 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b6c : bv 32 := 0x00813483.
Lemma F_75b6c : fetch_word Plain.M.loaded_segments (0x75b6c : word) = Some W_75b6c.
Proof. vm_refl. Qed.
Lemma D_75b6c : decode_any W_75b6c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b70 : bv 32 := 0x02010113.
Lemma F_75b70 : fetch_word Plain.M.loaded_segments (0x75b70 : word) = Some W_75b70.
Proof. vm_refl. Qed.
Lemma D_75b70 : decode_any W_75b70 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b74 : bv 32 := 0x00008067.
Lemma F_75b74 : fetch_word Plain.M.loaded_segments (0x75b74 : word) = Some W_75b74.
Proof. vm_refl. Qed.
Lemma D_75b74 : decode_any W_75b74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
