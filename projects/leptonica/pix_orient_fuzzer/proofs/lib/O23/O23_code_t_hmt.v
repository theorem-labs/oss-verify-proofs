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
Definition W_8faf4 : bv 32 := 0xf7010113.
Lemma F_8faf4 : fetch_word Plain.M.loaded_segments (0x8fb4c : word) = Some W_8faf4.
Proof. vm_refl. Qed.
Lemma D_8faf4 : decode_any W_8faf4 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8faf8 : bv 32 := 0x08113423.
Lemma F_8faf8 : fetch_word Plain.M.loaded_segments (0x8fb50 : word) = Some W_8faf8.
Proof. vm_refl. Qed.
Lemma D_8faf8 : decode_any W_8faf8 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fafc : bv 32 := 0x08813023.
Lemma F_8fafc : fetch_word Plain.M.loaded_segments (0x8fb54 : word) = Some W_8fafc.
Proof. vm_refl. Qed.
Lemma D_8fafc : decode_any W_8fafc = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb00 : bv 32 := 0x06913c23.
Lemma F_8fb00 : fetch_word Plain.M.loaded_segments (0x8fb58 : word) = Some W_8fb00.
Proof. vm_refl. Qed.
Lemma D_8fb00 : decode_any W_8fb00 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb04 : bv 32 := 0x07213823.
Lemma F_8fb04 : fetch_word Plain.M.loaded_segments (0x8fb5c : word) = Some W_8fb04.
Proof. vm_refl. Qed.
Lemma D_8fb04 : decode_any W_8fb04 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb08 : bv 32 := 0x07313423.
Lemma F_8fb08 : fetch_word Plain.M.loaded_segments (0x8fb60 : word) = Some W_8fb08.
Proof. vm_refl. Qed.
Lemma D_8fb08 : decode_any W_8fb08 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb0c : bv 32 := 0x07413023.
Lemma F_8fb0c : fetch_word Plain.M.loaded_segments (0x8fb64 : word) = Some W_8fb0c.
Proof. vm_refl. Qed.
Lemma D_8fb0c : decode_any W_8fb0c = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb10 : bv 32 := 0x05513c23.
Lemma F_8fb10 : fetch_word Plain.M.loaded_segments (0x8fb68 : word) = Some W_8fb10.
Proof. vm_refl. Qed.
Lemma D_8fb10 : decode_any W_8fb10 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb14 : bv 32 := 0x05613823.
Lemma F_8fb14 : fetch_word Plain.M.loaded_segments (0x8fb6c : word) = Some W_8fb14.
Proof. vm_refl. Qed.
Lemma D_8fb14 : decode_any W_8fb14 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb18 : bv 32 := 0x05713423.
Lemma F_8fb18 : fetch_word Plain.M.loaded_segments (0x8fb70 : word) = Some W_8fb18.
Proof. vm_refl. Qed.
Lemma D_8fb18 : decode_any W_8fb18 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb1c : bv 32 := 0x05813023.
Lemma F_8fb1c : fetch_word Plain.M.loaded_segments (0x8fb74 : word) = Some W_8fb1c.
Proof. vm_refl. Qed.
Lemma D_8fb1c : decode_any W_8fb1c = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb20 : bv 32 := 0x00060493.
Lemma F_8fb20 : fetch_word Plain.M.loaded_segments (0x8fb78 : word) = Some W_8fb20.
Proof. vm_refl. Qed.
Lemma D_8fb20 : decode_any W_8fb20 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb24 : bv 32 := 0x00058913.
Lemma F_8fb24 : fetch_word Plain.M.loaded_segments (0x8fb7c : word) = Some W_8fb24.
Proof. vm_refl. Qed.
Lemma D_8fb24 : decode_any W_8fb24 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb28 : bv 32 := 0x01010693.
Lemma F_8fb28 : fetch_word Plain.M.loaded_segments (0x8fb80 : word) = Some W_8fb28.
Proof. vm_refl. Qed.
Lemma D_8fb28 : decode_any W_8fb28 = Some (OpImm ALU_ADD 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb2c : bv 32 := 0xb51ff0ef.
Lemma F_8fb2c : fetch_word Plain.M.loaded_segments (0x8fb84 : word) = Some W_8fb2c.
Proof. vm_refl. Qed.
Lemma D_8fb2c : decode_any W_8fb2c = Some (Jal 1 2095952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb30 : bv 32 := 0x1e050463.
Lemma F_8fb30 : fetch_word Plain.M.loaded_segments (0x8fb88 : word) = Some W_8fb30.
Proof. vm_refl. Qed.
Lemma D_8fb30 : decode_any W_8fb30 = Some (Branch BC_EQ 10 0 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb34 : bv 32 := 0x00050413.
Lemma F_8fb34 : fetch_word Plain.M.loaded_segments (0x8fb8c : word) = Some W_8fb34.
Proof. vm_refl. Qed.
Lemma D_8fb34 : decode_any W_8fb34 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb38 : bv 32 := 0x03c10593.
Lemma F_8fb38 : fetch_word Plain.M.loaded_segments (0x8fb90 : word) = Some W_8fb38.
Proof. vm_refl. Qed.
Lemma D_8fb38 : decode_any W_8fb38 = Some (OpImm ALU_ADD 11 2 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb3c : bv 32 := 0x03810613.
Lemma F_8fb3c : fetch_word Plain.M.loaded_segments (0x8fb94 : word) = Some W_8fb3c.
Proof. vm_refl. Qed.
Lemma D_8fb3c : decode_any W_8fb3c = Some (OpImm ALU_ADD 12 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb40 : bv 32 := 0x00090513.
Lemma F_8fb40 : fetch_word Plain.M.loaded_segments (0x8fb98 : word) = Some W_8fb40.
Proof. vm_refl. Qed.
Lemma D_8fb40 : decode_any W_8fb40 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb44 : bv 32 := 0x00000693.
Lemma F_8fb44 : fetch_word Plain.M.loaded_segments (0x8fb9c : word) = Some W_8fb44.
Proof. vm_refl. Qed.
Lemma D_8fb44 : decode_any W_8fb44 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb48 : bv 32 := 0xa58dd0ef.
Lemma F_8fb48 : fetch_word Plain.M.loaded_segments (0x8fba0 : word) = Some W_8fb48.
Proof. vm_refl. Qed.
Lemma D_8fb48 : decode_any W_8fb48 = Some (Jal 1 1954392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb4c : bv 32 := 0x03010593.
Lemma F_8fb4c : fetch_word Plain.M.loaded_segments (0x8fba4 : word) = Some W_8fb4c.
Proof. vm_refl. Qed.
Lemma D_8fb4c : decode_any W_8fb4c = Some (OpImm ALU_ADD 11 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb50 : bv 32 := 0x03410613.
Lemma F_8fb50 : fetch_word Plain.M.loaded_segments (0x8fba8 : word) = Some W_8fb50.
Proof. vm_refl. Qed.
Lemma D_8fb50 : decode_any W_8fb50 = Some (OpImm ALU_ADD 12 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb54 : bv 32 := 0x02810693.
Lemma F_8fb54 : fetch_word Plain.M.loaded_segments (0x8fbac : word) = Some W_8fb54.
Proof. vm_refl. Qed.
Lemma D_8fb54 : decode_any W_8fb54 = Some (OpImm ALU_ADD 13 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb58 : bv 32 := 0x02c10713.
Lemma F_8fb58 : fetch_word Plain.M.loaded_segments (0x8fbb0 : word) = Some W_8fb58.
Proof. vm_refl. Qed.
Lemma D_8fb58 : decode_any W_8fb58 = Some (OpImm ALU_ADD 14 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb5c : bv 32 := 0x00048513.
Lemma F_8fb5c : fetch_word Plain.M.loaded_segments (0x8fbb4 : word) = Some W_8fb5c.
Proof. vm_refl. Qed.
Lemma D_8fb5c : decode_any W_8fb5c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb60 : bv 32 := 0x291020ef.
Lemma F_8fb60 : fetch_word Plain.M.loaded_segments (0x8fbb8 : word) = Some W_8fb60.
Proof. vm_refl. Qed.
Lemma D_8fb60 : decode_any W_8fb60 = Some (Jal 1 10896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb64 : bv 32 := 0x03012603.
Lemma F_8fb64 : fetch_word Plain.M.loaded_segments (0x8fbbc : word) = Some W_8fb64.
Proof. vm_refl. Qed.
Lemma D_8fb64 : decode_any W_8fb64 = Some (Load SZ4 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb68 : bv 32 := 0x0cc05a63.
Lemma F_8fb68 : fetch_word Plain.M.loaded_segments (0x8fbc0 : word) = Some W_8fb68.
Proof. vm_refl. Qed.
Lemma D_8fb68 : decode_any W_8fb68 = Some (Branch BC_GE 0 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb6c : bv 32 := 0x00000913.
Lemma F_8fb6c : fetch_word Plain.M.loaded_segments (0x8fbc4 : word) = Some W_8fb6c.
Proof. vm_refl. Qed.
Lemma D_8fb6c : decode_any W_8fb6c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb70 : bv 32 := 0x03412583.
Lemma F_8fb70 : fetch_word Plain.M.loaded_segments (0x8fbc8 : word) = Some W_8fb70.
Proof. vm_refl. Qed.
Lemma D_8fb70 : decode_any W_8fb70 = Some (Load SZ4 true 11 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb74 : bv 32 := 0x00100993.
Lemma F_8fb74 : fetch_word Plain.M.loaded_segments (0x8fbcc : word) = Some W_8fb74.
Proof. vm_refl. Qed.
Lemma D_8fb74 : decode_any W_8fb74 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb78 : bv 32 := 0x00200a13.
Lemma F_8fb78 : fetch_word Plain.M.loaded_segments (0x8fbd0 : word) = Some W_8fb78.
Proof. vm_refl. Qed.
Lemma D_8fb78 : decode_any W_8fb78 = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb7c : bv 32 := 0x00100513.
Lemma F_8fb7c : fetch_word Plain.M.loaded_segments (0x8fbd4 : word) = Some W_8fb7c.
Proof. vm_refl. Qed.
Lemma D_8fb7c : decode_any W_8fb7c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb80 : bv 32 := 0x0100006f.
Lemma F_8fb80 : fetch_word Plain.M.loaded_segments (0x8fbd8 : word) = Some W_8fb80.
Proof. vm_refl. Qed.
Lemma D_8fb80 : decode_any W_8fb80 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb84 : bv 32 := 0x03012603.
Lemma F_8fb84 : fetch_word Plain.M.loaded_segments (0x8fbdc : word) = Some W_8fb84.
Proof. vm_refl. Qed.
Lemma D_8fb84 : decode_any W_8fb84 = Some (Load SZ4 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb88 : bv 32 := 0x00190913.
Lemma F_8fb88 : fetch_word Plain.M.loaded_segments (0x8fbe0 : word) = Some W_8fb88.
Proof. vm_refl. Qed.
Lemma D_8fb88 : decode_any W_8fb88 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb8c : bv 32 := 0x0ac95863.
Lemma F_8fb8c : fetch_word Plain.M.loaded_segments (0x8fbe4 : word) = Some W_8fb8c.
Proof. vm_refl. Qed.
Lemma D_8fb8c : decode_any W_8fb8c = Some (Branch BC_GE 18 12 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb90 : bv 32 := 0xfeb05ce3.
Lemma F_8fb90 : fetch_word Plain.M.loaded_segments (0x8fbe8 : word) = Some W_8fb90.
Proof. vm_refl. Qed.
Lemma D_8fb90 : decode_any W_8fb90 = Some (Branch BC_GE 0 11 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb94 : bv 32 := 0x00000a93.
Lemma F_8fb94 : fetch_word Plain.M.loaded_segments (0x8fbec : word) = Some W_8fb94.
Proof. vm_refl. Qed.
Lemma D_8fb94 : decode_any W_8fb94 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb98 : bv 32 := 0x00000b13.
Lemma F_8fb98 : fetch_word Plain.M.loaded_segments (0x8fbf0 : word) = Some W_8fb98.
Proof. vm_refl. Qed.
Lemma D_8fb98 : decode_any W_8fb98 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fb9c : bv 32 := 0x00000b93.
Lemma F_8fb9c : fetch_word Plain.M.loaded_segments (0x8fbf4 : word) = Some W_8fb9c.
Proof. vm_refl. Qed.
Lemma D_8fb9c : decode_any W_8fb9c = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fba0 : bv 32 := 0x00391c13.
Lemma F_8fba0 : fetch_word Plain.M.loaded_segments (0x8fbf8 : word) = Some W_8fba0.
Proof. vm_refl. Qed.
Lemma D_8fba0 : decode_any W_8fba0 = Some (ShiftImm ALU_SLL 24 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fba4 : bv 32 := 0x0540006f.
Lemma F_8fba4 : fetch_word Plain.M.loaded_segments (0x8fbfc : word) = Some W_8fba4.
Proof. vm_refl. Qed.
Lemma D_8fba4 : decode_any W_8fba4 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fba8 : bv 32 := 0x00040513.
Lemma F_8fba8 : fetch_word Plain.M.loaded_segments (0x8fc00 : word) = Some W_8fba8.
Proof. vm_refl. Qed.
Lemma D_8fba8 : decode_any W_8fba8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbac : bv 32 := 0x8b1de0ef.
Lemma F_8fbac : fetch_word Plain.M.loaded_segments (0x8fc04 : word) = Some W_8fbac.
Proof. vm_refl. Qed.
Lemma D_8fbac : decode_any W_8fbac = Some (Jal 1 1960112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbb0 : bv 32 := 0x00c00793.
Lemma F_8fbb0 : fetch_word Plain.M.loaded_segments (0x8fc08 : word) = Some W_8fbb0.
Proof. vm_refl. Qed.
Lemma D_8fbb0 : decode_any W_8fbb0 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbb4 : bv 32 := 0x02c12503.
Lemma F_8fbb4 : fetch_word Plain.M.loaded_segments (0x8fc0c : word) = Some W_8fbb4.
Proof. vm_refl. Qed.
Lemma D_8fbb4 : decode_any W_8fbb4 = Some (Load SZ4 true 10 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbb8 : bv 32 := 0x02812603.
Lemma F_8fbb8 : fetch_word Plain.M.loaded_segments (0x8fc10 : word) = Some W_8fbb8.
Proof. vm_refl. Qed.
Lemma D_8fbb8 : decode_any W_8fbb8 = Some (Load SZ4 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbbc : bv 32 := 0x03c12683.
Lemma F_8fbbc : fetch_word Plain.M.loaded_segments (0x8fc14 : word) = Some W_8fbbc.
Proof. vm_refl. Qed.
Lemma D_8fbbc : decode_any W_8fbbc = Some (Load SZ4 true 13 2 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbc0 : bv 32 := 0x03812703.
Lemma F_8fbc0 : fetch_word Plain.M.loaded_segments (0x8fc18 : word) = Some W_8fbc0.
Proof. vm_refl. Qed.
Lemma D_8fbc0 : decode_any W_8fbc0 = Some (Load SZ4 true 14 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbc4 : bv 32 := 0x01013803.
Lemma F_8fbc4 : fetch_word Plain.M.loaded_segments (0x8fc1c : word) = Some W_8fbc4.
Proof. vm_refl. Qed.
Lemma D_8fbc4 : decode_any W_8fbc4 = Some (Load SZ8 true 16 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbc8 : bv 32 := 0x00ab05bb.
Lemma F_8fbc8 : fetch_word Plain.M.loaded_segments (0x8fc20 : word) = Some W_8fbc8.
Proof. vm_refl. Qed.
Lemma D_8fbc8 : decode_any W_8fbc8 = Some (Op32 ALU_ADD 11 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbcc : bv 32 := 0x4126063b.
Lemma F_8fbcc : fetch_word Plain.M.loaded_segments (0x8fc24 : word) = Some W_8fbcc.
Proof. vm_refl. Qed.
Lemma D_8fbcc : decode_any W_8fbcc = Some (Op32 ALU_SUB 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbd0 : bv 32 := 0x00013023.
Lemma F_8fbd0 : fetch_word Plain.M.loaded_segments (0x8fc28 : word) = Some W_8fbd0.
Proof. vm_refl. Qed.
Lemma D_8fbd0 : decode_any W_8fbd0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbd4 : bv 32 := 0x00040513.
Lemma F_8fbd4 : fetch_word Plain.M.loaded_segments (0x8fc2c : word) = Some W_8fbd4.
Proof. vm_refl. Qed.
Lemma D_8fbd4 : decode_any W_8fbd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbd8 : bv 32 := 0x00000893.
Lemma F_8fbd8 : fetch_word Plain.M.loaded_segments (0x8fc30 : word) = Some W_8fbd8.
Proof. vm_refl. Qed.
Lemma D_8fbd8 : decode_any W_8fbd8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbdc : bv 32 := 0xb79e90ef.
Lemma F_8fbdc : fetch_word Plain.M.loaded_segments (0x8fc34 : word) = Some W_8fbdc.
Proof. vm_refl. Qed.
Lemma D_8fbdc : decode_any W_8fbdc = Some (Jal 1 2005880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbe0 : bv 32 := 0x00000513.
Lemma F_8fbe0 : fetch_word Plain.M.loaded_segments (0x8fc38 : word) = Some W_8fbe0.
Proof. vm_refl. Qed.
Lemma D_8fbe0 : decode_any W_8fbe0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbe4 : bv 32 := 0x03412583.
Lemma F_8fbe4 : fetch_word Plain.M.loaded_segments (0x8fc3c : word) = Some W_8fbe4.
Proof. vm_refl. Qed.
Lemma D_8fbe4 : decode_any W_8fbe4 = Some (Load SZ4 true 11 2 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbe8 : bv 32 := 0x001b8b93.
Lemma F_8fbe8 : fetch_word Plain.M.loaded_segments (0x8fc40 : word) = Some W_8fbe8.
Proof. vm_refl. Qed.
Lemma D_8fbe8 : decode_any W_8fbe8 = Some (OpImm ALU_ADD 23 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbec : bv 32 := 0xfffb0b13.
Lemma F_8fbec : fetch_word Plain.M.loaded_segments (0x8fc44 : word) = Some W_8fbec.
Proof. vm_refl. Qed.
Lemma D_8fbec : decode_any W_8fbec = Some (OpImm ALU_ADD 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbf0 : bv 32 := 0x004a8a93.
Lemma F_8fbf0 : fetch_word Plain.M.loaded_segments (0x8fc48 : word) = Some W_8fbf0.
Proof. vm_refl. Qed.
Lemma D_8fbf0 : decode_any W_8fbf0 = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbf4 : bv 32 := 0xf8bbd8e3.
Lemma F_8fbf4 : fetch_word Plain.M.loaded_segments (0x8fc4c : word) = Some W_8fbf4.
Proof. vm_refl. Qed.
Lemma D_8fbf4 : decode_any W_8fbf4 = Some (Branch BC_GE 23 11 8080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbf8 : bv 32 := 0x0104b583.
Lemma F_8fbf8 : fetch_word Plain.M.loaded_segments (0x8fc50 : word) = Some W_8fbf8.
Proof. vm_refl. Qed.
Lemma D_8fbf8 : decode_any W_8fbf8 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fbfc : bv 32 := 0x018585b3.
Lemma F_8fbfc : fetch_word Plain.M.loaded_segments (0x8fc54 : word) = Some W_8fbfc.
Proof. vm_refl. Qed.
Lemma D_8fbfc : decode_any W_8fbfc = Some (Op ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc00 : bv 32 := 0x0005b583.
Lemma F_8fc00 : fetch_word Plain.M.loaded_segments (0x8fc58 : word) = Some W_8fc00.
Proof. vm_refl. Qed.
Lemma D_8fc00 : decode_any W_8fc00 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc04 : bv 32 := 0x015585b3.
Lemma F_8fc04 : fetch_word Plain.M.loaded_segments (0x8fc5c : word) = Some W_8fc04.
Proof. vm_refl. Qed.
Lemma D_8fc04 : decode_any W_8fc04 = Some (Op ALU_ADD 11 11 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc08 : bv 32 := 0x0005a583.
Lemma F_8fc08 : fetch_word Plain.M.loaded_segments (0x8fc60 : word) = Some W_8fc08.
Proof. vm_refl. Qed.
Lemma D_8fc08 : decode_any W_8fc08 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc0c : bv 32 := 0x01458a63.
Lemma F_8fc0c : fetch_word Plain.M.loaded_segments (0x8fc64 : word) = Some W_8fc0c.
Proof. vm_refl. Qed.
Lemma D_8fc0c : decode_any W_8fc0c = Some (Branch BC_EQ 11 20 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc10 : bv 32 := 0xfd359ae3.
Lemma F_8fc10 : fetch_word Plain.M.loaded_segments (0x8fc68 : word) = Some W_8fc10.
Proof. vm_refl. Qed.
Lemma D_8fc10 : decode_any W_8fc10 = Some (Branch BC_NE 11 19 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc14 : bv 32 := 0xf9350ae3.
Lemma F_8fc14 : fetch_word Plain.M.loaded_segments (0x8fc6c : word) = Some W_8fc14.
Proof. vm_refl. Qed.
Lemma D_8fc14 : decode_any W_8fc14 = Some (Branch BC_EQ 10 19 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc18 : bv 32 := 0x00800793.
Lemma F_8fc18 : fetch_word Plain.M.loaded_segments (0x8fc70 : word) = Some W_8fc18.
Proof. vm_refl. Qed.
Lemma D_8fc18 : decode_any W_8fc18 = Some (OpImm ALU_ADD 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc1c : bv 32 := 0xf99ff06f.
Lemma F_8fc1c : fetch_word Plain.M.loaded_segments (0x8fc74 : word) = Some W_8fc1c.
Proof. vm_refl. Qed.
Lemma D_8fc1c : decode_any W_8fc1c = Some (Jal 0 2097048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc20 : bv 32 := 0x01351a63.
Lemma F_8fc20 : fetch_word Plain.M.loaded_segments (0x8fc78 : word) = Some W_8fc20.
Proof. vm_refl. Qed.
Lemma D_8fc20 : decode_any W_8fc20 = Some (Branch BC_NE 10 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc24 : bv 32 := 0x00040513.
Lemma F_8fc24 : fetch_word Plain.M.loaded_segments (0x8fc7c : word) = Some W_8fc24.
Proof. vm_refl. Qed.
Lemma D_8fc24 : decode_any W_8fc24 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc28 : bv 32 := 0x8a1de0ef.
Lemma F_8fc28 : fetch_word Plain.M.loaded_segments (0x8fc80 : word) = Some W_8fc28.
Proof. vm_refl. Qed.
Lemma D_8fc28 : decode_any W_8fc28 = Some (Jal 1 1960096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc2c : bv 32 := 0x00300793.
Lemma F_8fc2c : fetch_word Plain.M.loaded_segments (0x8fc84 : word) = Some W_8fc2c.
Proof. vm_refl. Qed.
Lemma D_8fc2c : decode_any W_8fc2c = Some (OpImm ALU_ADD 15 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc30 : bv 32 := 0xf85ff06f.
Lemma F_8fc30 : fetch_word Plain.M.loaded_segments (0x8fc88 : word) = Some W_8fc30.
Proof. vm_refl. Qed.
Lemma D_8fc30 : decode_any W_8fc30 = Some (Jal 0 2097028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc34 : bv 32 := 0x00200793.
Lemma F_8fc34 : fetch_word Plain.M.loaded_segments (0x8fc8c : word) = Some W_8fc34.
Proof. vm_refl. Qed.
Lemma D_8fc34 : decode_any W_8fc34 = Some (OpImm ALU_ADD 15 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc38 : bv 32 := 0xf7dff06f.
Lemma F_8fc38 : fetch_word Plain.M.loaded_segments (0x8fc90 : word) = Some W_8fc38.
Proof. vm_refl. Qed.
Lemma D_8fc38 : decode_any W_8fc38 = Some (Jal 0 2097020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc3c : bv 32 := 0x02410593.
Lemma F_8fc3c : fetch_word Plain.M.loaded_segments (0x8fc94 : word) = Some W_8fc3c.
Proof. vm_refl. Qed.
Lemma D_8fc3c : decode_any W_8fc3c = Some (OpImm ALU_ADD 11 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc40 : bv 32 := 0x02010613.
Lemma F_8fc40 : fetch_word Plain.M.loaded_segments (0x8fc98 : word) = Some W_8fc40.
Proof. vm_refl. Qed.
Lemma D_8fc40 : decode_any W_8fc40 = Some (OpImm ALU_ADD 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc44 : bv 32 := 0x01c10693.
Lemma F_8fc44 : fetch_word Plain.M.loaded_segments (0x8fc9c : word) = Some W_8fc44.
Proof. vm_refl. Qed.
Lemma D_8fc44 : decode_any W_8fc44 = Some (OpImm ALU_ADD 13 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc48 : bv 32 := 0x01810713.
Lemma F_8fc48 : fetch_word Plain.M.loaded_segments (0x8fca0 : word) = Some W_8fc48.
Proof. vm_refl. Qed.
Lemma D_8fc48 : decode_any W_8fc48 = Some (OpImm ALU_ADD 14 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc4c : bv 32 := 0x00048513.
Lemma F_8fc4c : fetch_word Plain.M.loaded_segments (0x8fca4 : word) = Some W_8fc4c.
Proof. vm_refl. Qed.
Lemma D_8fc4c : decode_any W_8fc4c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc50 : bv 32 := 0x705020ef.
Lemma F_8fc50 : fetch_word Plain.M.loaded_segments (0x8fca8 : word) = Some W_8fc50.
Proof. vm_refl. Qed.
Lemma D_8fc50 : decode_any W_8fc50 = Some (Jal 1 12036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc54 : bv 32 := 0x02412683.
Lemma F_8fc54 : fetch_word Plain.M.loaded_segments (0x8fcac : word) = Some W_8fc54.
Proof. vm_refl. Qed.
Lemma D_8fc54 : decode_any W_8fc54 = Some (Load SZ4 true 13 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc58 : bv 32 := 0x02d05463.
Lemma F_8fc58 : fetch_word Plain.M.loaded_segments (0x8fcb0 : word) = Some W_8fc58.
Proof. vm_refl. Qed.
Lemma D_8fc58 : decode_any W_8fc58 = Some (Branch BC_GE 0 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc5c : bv 32 := 0x03812703.
Lemma F_8fc5c : fetch_word Plain.M.loaded_segments (0x8fcb4 : word) = Some W_8fc5c.
Proof. vm_refl. Qed.
Lemma D_8fc5c : decode_any W_8fc5c = Some (Load SZ4 true 14 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc60 : bv 32 := 0x00013023.
Lemma F_8fc60 : fetch_word Plain.M.loaded_segments (0x8fcb8 : word) = Some W_8fc60.
Proof. vm_refl. Qed.
Lemma D_8fc60 : decode_any W_8fc60 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc64 : bv 32 := 0x00040513.
Lemma F_8fc64 : fetch_word Plain.M.loaded_segments (0x8fcbc : word) = Some W_8fc64.
Proof. vm_refl. Qed.
Lemma D_8fc64 : decode_any W_8fc64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc68 : bv 32 := 0x00000593.
Lemma F_8fc68 : fetch_word Plain.M.loaded_segments (0x8fcc0 : word) = Some W_8fc68.
Proof. vm_refl. Qed.
Lemma D_8fc68 : decode_any W_8fc68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc6c : bv 32 := 0x00000613.
Lemma F_8fc6c : fetch_word Plain.M.loaded_segments (0x8fcc4 : word) = Some W_8fc6c.
Proof. vm_refl. Qed.
Lemma D_8fc6c : decode_any W_8fc6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc70 : bv 32 := 0x00000793.
Lemma F_8fc70 : fetch_word Plain.M.loaded_segments (0x8fcc8 : word) = Some W_8fc70.
Proof. vm_refl. Qed.
Lemma D_8fc70 : decode_any W_8fc70 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc74 : bv 32 := 0x00000813.
Lemma F_8fc74 : fetch_word Plain.M.loaded_segments (0x8fccc : word) = Some W_8fc74.
Proof. vm_refl. Qed.
Lemma D_8fc74 : decode_any W_8fc74 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc78 : bv 32 := 0x00000893.
Lemma F_8fc78 : fetch_word Plain.M.loaded_segments (0x8fcd0 : word) = Some W_8fc78.
Proof. vm_refl. Qed.
Lemma D_8fc78 : decode_any W_8fc78 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc7c : bv 32 := 0xad9e90ef.
Lemma F_8fc7c : fetch_word Plain.M.loaded_segments (0x8fcd4 : word) = Some W_8fc7c.
Proof. vm_refl. Qed.
Lemma D_8fc7c : decode_any W_8fc7c = Some (Jal 1 2005720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc80 : bv 32 := 0x01c12683.
Lemma F_8fc80 : fetch_word Plain.M.loaded_segments (0x8fcd8 : word) = Some W_8fc80.
Proof. vm_refl. Qed.
Lemma D_8fc80 : decode_any W_8fc80 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc84 : bv 32 := 0x02d05663.
Lemma F_8fc84 : fetch_word Plain.M.loaded_segments (0x8fcdc : word) = Some W_8fc84.
Proof. vm_refl. Qed.
Lemma D_8fc84 : decode_any W_8fc84 = Some (Branch BC_GE 0 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc88 : bv 32 := 0x03c12583.
Lemma F_8fc88 : fetch_word Plain.M.loaded_segments (0x8fce0 : word) = Some W_8fc88.
Proof. vm_refl. Qed.
Lemma D_8fc88 : decode_any W_8fc88 = Some (Load SZ4 true 11 2 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc8c : bv 32 := 0x03812703.
Lemma F_8fc8c : fetch_word Plain.M.loaded_segments (0x8fce4 : word) = Some W_8fc8c.
Proof. vm_refl. Qed.
Lemma D_8fc8c : decode_any W_8fc8c = Some (Load SZ4 true 14 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc90 : bv 32 := 0x40d585bb.
Lemma F_8fc90 : fetch_word Plain.M.loaded_segments (0x8fce8 : word) = Some W_8fc90.
Proof. vm_refl. Qed.
Lemma D_8fc90 : decode_any W_8fc90 = Some (Op32 ALU_SUB 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc94 : bv 32 := 0x00013023.
Lemma F_8fc94 : fetch_word Plain.M.loaded_segments (0x8fcec : word) = Some W_8fc94.
Proof. vm_refl. Qed.
Lemma D_8fc94 : decode_any W_8fc94 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc98 : bv 32 := 0x00040513.
Lemma F_8fc98 : fetch_word Plain.M.loaded_segments (0x8fcf0 : word) = Some W_8fc98.
Proof. vm_refl. Qed.
Lemma D_8fc98 : decode_any W_8fc98 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc9c : bv 32 := 0x00000613.
Lemma F_8fc9c : fetch_word Plain.M.loaded_segments (0x8fcf4 : word) = Some W_8fc9c.
Proof. vm_refl. Qed.
Lemma D_8fc9c : decode_any W_8fc9c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fca0 : bv 32 := 0x00000793.
Lemma F_8fca0 : fetch_word Plain.M.loaded_segments (0x8fcf8 : word) = Some W_8fca0.
Proof. vm_refl. Qed.
Lemma D_8fca0 : decode_any W_8fca0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fca4 : bv 32 := 0x00000813.
Lemma F_8fca4 : fetch_word Plain.M.loaded_segments (0x8fcfc : word) = Some W_8fca4.
Proof. vm_refl. Qed.
Lemma D_8fca4 : decode_any W_8fca4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fca8 : bv 32 := 0x00000893.
Lemma F_8fca8 : fetch_word Plain.M.loaded_segments (0x8fd00 : word) = Some W_8fca8.
Proof. vm_refl. Qed.
Lemma D_8fca8 : decode_any W_8fca8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcac : bv 32 := 0xaa9e90ef.
Lemma F_8fcac : fetch_word Plain.M.loaded_segments (0x8fd04 : word) = Some W_8fcac.
Proof. vm_refl. Qed.
Lemma D_8fcac : decode_any W_8fcac = Some (Jal 1 2005672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcb0 : bv 32 := 0x02012703.
Lemma F_8fcb0 : fetch_word Plain.M.loaded_segments (0x8fd08 : word) = Some W_8fcb0.
Proof. vm_refl. Qed.
Lemma D_8fcb0 : decode_any W_8fcb0 = Some (Load SZ4 true 14 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcb4 : bv 32 := 0x02e05463.
Lemma F_8fcb4 : fetch_word Plain.M.loaded_segments (0x8fd0c : word) = Some W_8fcb4.
Proof. vm_refl. Qed.
Lemma D_8fcb4 : decode_any W_8fcb4 = Some (Branch BC_GE 0 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcb8 : bv 32 := 0x03c12683.
Lemma F_8fcb8 : fetch_word Plain.M.loaded_segments (0x8fd10 : word) = Some W_8fcb8.
Proof. vm_refl. Qed.
Lemma D_8fcb8 : decode_any W_8fcb8 = Some (Load SZ4 true 13 2 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcbc : bv 32 := 0x00013023.
Lemma F_8fcbc : fetch_word Plain.M.loaded_segments (0x8fd14 : word) = Some W_8fcbc.
Proof. vm_refl. Qed.
Lemma D_8fcbc : decode_any W_8fcbc = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcc0 : bv 32 := 0x00040513.
Lemma F_8fcc0 : fetch_word Plain.M.loaded_segments (0x8fd18 : word) = Some W_8fcc0.
Proof. vm_refl. Qed.
Lemma D_8fcc0 : decode_any W_8fcc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcc4 : bv 32 := 0x00000593.
Lemma F_8fcc4 : fetch_word Plain.M.loaded_segments (0x8fd1c : word) = Some W_8fcc4.
Proof. vm_refl. Qed.
Lemma D_8fcc4 : decode_any W_8fcc4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcc8 : bv 32 := 0x00000613.
Lemma F_8fcc8 : fetch_word Plain.M.loaded_segments (0x8fd20 : word) = Some W_8fcc8.
Proof. vm_refl. Qed.
Lemma D_8fcc8 : decode_any W_8fcc8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fccc : bv 32 := 0x00000793.
Lemma F_8fccc : fetch_word Plain.M.loaded_segments (0x8fd24 : word) = Some W_8fccc.
Proof. vm_refl. Qed.
Lemma D_8fccc : decode_any W_8fccc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcd0 : bv 32 := 0x00000813.
Lemma F_8fcd0 : fetch_word Plain.M.loaded_segments (0x8fd28 : word) = Some W_8fcd0.
Proof. vm_refl. Qed.
Lemma D_8fcd0 : decode_any W_8fcd0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcd4 : bv 32 := 0x00000893.
Lemma F_8fcd4 : fetch_word Plain.M.loaded_segments (0x8fd2c : word) = Some W_8fcd4.
Proof. vm_refl. Qed.
Lemma D_8fcd4 : decode_any W_8fcd4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcd8 : bv 32 := 0xa7de90ef.
Lemma F_8fcd8 : fetch_word Plain.M.loaded_segments (0x8fd30 : word) = Some W_8fcd8.
Proof. vm_refl. Qed.
Lemma D_8fcd8 : decode_any W_8fcd8 = Some (Jal 1 2005628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcdc : bv 32 := 0x01812703.
Lemma F_8fcdc : fetch_word Plain.M.loaded_segments (0x8fd34 : word) = Some W_8fcdc.
Proof. vm_refl. Qed.
Lemma D_8fcdc : decode_any W_8fcdc = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fce0 : bv 32 := 0x02e05663.
Lemma F_8fce0 : fetch_word Plain.M.loaded_segments (0x8fd38 : word) = Some W_8fce0.
Proof. vm_refl. Qed.
Lemma D_8fce0 : decode_any W_8fce0 = Some (Branch BC_GE 0 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fce4 : bv 32 := 0x03812603.
Lemma F_8fce4 : fetch_word Plain.M.loaded_segments (0x8fd3c : word) = Some W_8fce4.
Proof. vm_refl. Qed.
Lemma D_8fce4 : decode_any W_8fce4 = Some (Load SZ4 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fce8 : bv 32 := 0x03c12683.
Lemma F_8fce8 : fetch_word Plain.M.loaded_segments (0x8fd40 : word) = Some W_8fce8.
Proof. vm_refl. Qed.
Lemma D_8fce8 : decode_any W_8fce8 = Some (Load SZ4 true 13 2 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcec : bv 32 := 0x40e6063b.
Lemma F_8fcec : fetch_word Plain.M.loaded_segments (0x8fd44 : word) = Some W_8fcec.
Proof. vm_refl. Qed.
Lemma D_8fcec : decode_any W_8fcec = Some (Op32 ALU_SUB 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcf0 : bv 32 := 0x00013023.
Lemma F_8fcf0 : fetch_word Plain.M.loaded_segments (0x8fd48 : word) = Some W_8fcf0.
Proof. vm_refl. Qed.
Lemma D_8fcf0 : decode_any W_8fcf0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcf4 : bv 32 := 0x00040513.
Lemma F_8fcf4 : fetch_word Plain.M.loaded_segments (0x8fd4c : word) = Some W_8fcf4.
Proof. vm_refl. Qed.
Lemma D_8fcf4 : decode_any W_8fcf4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcf8 : bv 32 := 0x00000593.
Lemma F_8fcf8 : fetch_word Plain.M.loaded_segments (0x8fd50 : word) = Some W_8fcf8.
Proof. vm_refl. Qed.
Lemma D_8fcf8 : decode_any W_8fcf8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcfc : bv 32 := 0x00000793.
Lemma F_8fcfc : fetch_word Plain.M.loaded_segments (0x8fd54 : word) = Some W_8fcfc.
Proof. vm_refl. Qed.
Lemma D_8fcfc : decode_any W_8fcfc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd00 : bv 32 := 0x00000813.
Lemma F_8fd00 : fetch_word Plain.M.loaded_segments (0x8fd58 : word) = Some W_8fd00.
Proof. vm_refl. Qed.
Lemma D_8fd00 : decode_any W_8fd00 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd04 : bv 32 := 0x00000893.
Lemma F_8fd04 : fetch_word Plain.M.loaded_segments (0x8fd5c : word) = Some W_8fd04.
Proof. vm_refl. Qed.
Lemma D_8fd04 : decode_any W_8fd04 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd08 : bv 32 := 0xa4de90ef.
Lemma F_8fd08 : fetch_word Plain.M.loaded_segments (0x8fd60 : word) = Some W_8fd08.
Proof. vm_refl. Qed.
Lemma D_8fd08 : decode_any W_8fd08 = Some (Jal 1 2005580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd0c : bv 32 := 0x01010513.
Lemma F_8fd0c : fetch_word Plain.M.loaded_segments (0x8fd64 : word) = Some W_8fd0c.
Proof. vm_refl. Qed.
Lemma D_8fd0c : decode_any W_8fd0c = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd10 : bv 32 := 0xdd5dc0ef.
Lemma F_8fd10 : fetch_word Plain.M.loaded_segments (0x8fd68 : word) = Some W_8fd10.
Proof. vm_refl. Qed.
Lemma D_8fd10 : decode_any W_8fd10 = Some (Jal 1 1953236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd14 : bv 32 := 0x0600006f.
Lemma F_8fd14 : fetch_word Plain.M.loaded_segments (0x8fd6c : word) = Some W_8fd14.
Proof. vm_refl. Qed.
Lemma D_8fd14 : decode_any W_8fd14 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd18 : bv 32 := 0x00083517.
Lemma F_8fd18 : fetch_word Plain.M.loaded_segments (0x8fd70 : word) = Some W_8fd18.
Proof. vm_refl. Qed.
Lemma D_8fd18 : decode_any W_8fd18 = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd1c : bv 32 := 0x85853503.
Lemma F_8fd1c : fetch_word Plain.M.loaded_segments (0x8fd74 : word) = Some W_8fd1c.
Proof. vm_refl. Qed.
Lemma D_8fd1c : decode_any W_8fd1c = Some (Load SZ8 true 10 10 2136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd20 : bv 32 := 0x00052503.
Lemma F_8fd20 : fetch_word Plain.M.loaded_segments (0x8fd78 : word) = Some W_8fd20.
Proof. vm_refl. Qed.
Lemma D_8fd20 : decode_any W_8fd20 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd24 : bv 32 := 0x00500593.
Lemma F_8fd24 : fetch_word Plain.M.loaded_segments (0x8fd7c : word) = Some W_8fd24.
Proof. vm_refl. Qed.
Lemma D_8fd24 : decode_any W_8fd24 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd28 : bv 32 := 0x04a5c463.
Lemma F_8fd28 : fetch_word Plain.M.loaded_segments (0x8fd80 : word) = Some W_8fd28.
Proof. vm_refl. Qed.
Lemma D_8fd28 : decode_any W_8fd28 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd2c : bv 32 := 0xfff87517.
Lemma F_8fd2c : fetch_word Plain.M.loaded_segments (0x8fd84 : word) = Some W_8fd2c.
Proof. vm_refl. Qed.
Lemma D_8fd2c : decode_any W_8fd2c = Some (Auipc 10 1048455, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd30 : bv 32 := 0xfff86597.
Lemma F_8fd30 : fetch_word Plain.M.loaded_segments (0x8fd88 : word) = Some W_8fd30.
Proof. vm_refl. Qed.
Lemma D_8fd30 : decode_any W_8fd30 = Some (Auipc 11 1048454, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd34 : bv 32 := 0xd4950513.
Lemma F_8fd34 : fetch_word Plain.M.loaded_segments (0x8fd8c : word) = Some W_8fd34.
Proof. vm_refl. Qed.
Lemma D_8fd34 : decode_any W_8fd34 = Some (OpImm ALU_ADD 10 10 3401, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd38 : bv 32 := 0x5a458593.
Lemma F_8fd38 : fetch_word Plain.M.loaded_segments (0x8fd90 : word) = Some W_8fd38.
Proof. vm_refl. Qed.
Lemma D_8fd38 : decode_any W_8fd38 = Some (OpImm ALU_ADD 11 11 1444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd3c : bv 32 := 0x00000613.
Lemma F_8fd3c : fetch_word Plain.M.loaded_segments (0x8fd94 : word) = Some W_8fd3c.
Proof. vm_refl. Qed.
Lemma D_8fd3c : decode_any W_8fd3c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd40 : bv 32 := 0x08813083.
Lemma F_8fd40 : fetch_word Plain.M.loaded_segments (0x8fd98 : word) = Some W_8fd40.
Proof. vm_refl. Qed.
Lemma D_8fd40 : decode_any W_8fd40 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd44 : bv 32 := 0x08013403.
Lemma F_8fd44 : fetch_word Plain.M.loaded_segments (0x8fd9c : word) = Some W_8fd44.
Proof. vm_refl. Qed.
Lemma D_8fd44 : decode_any W_8fd44 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd48 : bv 32 := 0x07813483.
Lemma F_8fd48 : fetch_word Plain.M.loaded_segments (0x8fda0 : word) = Some W_8fd48.
Proof. vm_refl. Qed.
Lemma D_8fd48 : decode_any W_8fd48 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd4c : bv 32 := 0x07013903.
Lemma F_8fd4c : fetch_word Plain.M.loaded_segments (0x8fda4 : word) = Some W_8fd4c.
Proof. vm_refl. Qed.
Lemma D_8fd4c : decode_any W_8fd4c = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd50 : bv 32 := 0x06813983.
Lemma F_8fd50 : fetch_word Plain.M.loaded_segments (0x8fda8 : word) = Some W_8fd50.
Proof. vm_refl. Qed.
Lemma D_8fd50 : decode_any W_8fd50 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd54 : bv 32 := 0x06013a03.
Lemma F_8fd54 : fetch_word Plain.M.loaded_segments (0x8fdac : word) = Some W_8fd54.
Proof. vm_refl. Qed.
Lemma D_8fd54 : decode_any W_8fd54 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd58 : bv 32 := 0x05813a83.
Lemma F_8fd58 : fetch_word Plain.M.loaded_segments (0x8fdb0 : word) = Some W_8fd58.
Proof. vm_refl. Qed.
Lemma D_8fd58 : decode_any W_8fd58 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd5c : bv 32 := 0x05013b03.
Lemma F_8fd5c : fetch_word Plain.M.loaded_segments (0x8fdb4 : word) = Some W_8fd5c.
Proof. vm_refl. Qed.
Lemma D_8fd5c : decode_any W_8fd5c = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd60 : bv 32 := 0x04813b83.
Lemma F_8fd60 : fetch_word Plain.M.loaded_segments (0x8fdb8 : word) = Some W_8fd60.
Proof. vm_refl. Qed.
Lemma D_8fd60 : decode_any W_8fd60 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd64 : bv 32 := 0x04013c03.
Lemma F_8fd64 : fetch_word Plain.M.loaded_segments (0x8fdbc : word) = Some W_8fd64.
Proof. vm_refl. Qed.
Lemma D_8fd64 : decode_any W_8fd64 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd68 : bv 32 := 0x09010113.
Lemma F_8fd68 : fetch_word Plain.M.loaded_segments (0x8fdc0 : word) = Some W_8fd68.
Proof. vm_refl. Qed.
Lemma D_8fd68 : decode_any W_8fd68 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd6c : bv 32 := 0xb58d306f.
Lemma F_8fd6c : fetch_word Plain.M.loaded_segments (0x8fdc4 : word) = Some W_8fd6c.
Proof. vm_refl. Qed.
Lemma D_8fd6c : decode_any W_8fd6c = Some (Jal 0 1913688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd74 : bv 32 := 0x00040513.
Lemma F_8fd74 : fetch_word Plain.M.loaded_segments (0x8fdcc : word) = Some W_8fd74.
Proof. vm_refl. Qed.
Lemma D_8fd74 : decode_any W_8fd74 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd78 : bv 32 := 0x08813083.
Lemma F_8fd78 : fetch_word Plain.M.loaded_segments (0x8fdd0 : word) = Some W_8fd78.
Proof. vm_refl. Qed.
Lemma D_8fd78 : decode_any W_8fd78 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd7c : bv 32 := 0x08013403.
Lemma F_8fd7c : fetch_word Plain.M.loaded_segments (0x8fdd4 : word) = Some W_8fd7c.
Proof. vm_refl. Qed.
Lemma D_8fd7c : decode_any W_8fd7c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd80 : bv 32 := 0x07813483.
Lemma F_8fd80 : fetch_word Plain.M.loaded_segments (0x8fdd8 : word) = Some W_8fd80.
Proof. vm_refl. Qed.
Lemma D_8fd80 : decode_any W_8fd80 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd84 : bv 32 := 0x07013903.
Lemma F_8fd84 : fetch_word Plain.M.loaded_segments (0x8fddc : word) = Some W_8fd84.
Proof. vm_refl. Qed.
Lemma D_8fd84 : decode_any W_8fd84 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd88 : bv 32 := 0x06813983.
Lemma F_8fd88 : fetch_word Plain.M.loaded_segments (0x8fde0 : word) = Some W_8fd88.
Proof. vm_refl. Qed.
Lemma D_8fd88 : decode_any W_8fd88 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd8c : bv 32 := 0x06013a03.
Lemma F_8fd8c : fetch_word Plain.M.loaded_segments (0x8fde4 : word) = Some W_8fd8c.
Proof. vm_refl. Qed.
Lemma D_8fd8c : decode_any W_8fd8c = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd90 : bv 32 := 0x05813a83.
Lemma F_8fd90 : fetch_word Plain.M.loaded_segments (0x8fde8 : word) = Some W_8fd90.
Proof. vm_refl. Qed.
Lemma D_8fd90 : decode_any W_8fd90 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd94 : bv 32 := 0x05013b03.
Lemma F_8fd94 : fetch_word Plain.M.loaded_segments (0x8fdec : word) = Some W_8fd94.
Proof. vm_refl. Qed.
Lemma D_8fd94 : decode_any W_8fd94 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd98 : bv 32 := 0x04813b83.
Lemma F_8fd98 : fetch_word Plain.M.loaded_segments (0x8fdf0 : word) = Some W_8fd98.
Proof. vm_refl. Qed.
Lemma D_8fd98 : decode_any W_8fd98 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd9c : bv 32 := 0x04013c03.
Lemma F_8fd9c : fetch_word Plain.M.loaded_segments (0x8fdf4 : word) = Some W_8fd9c.
Proof. vm_refl. Qed.
Lemma D_8fd9c : decode_any W_8fd9c = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fda0 : bv 32 := 0x09010113.
Lemma F_8fda0 : fetch_word Plain.M.loaded_segments (0x8fdf8 : word) = Some W_8fda0.
Proof. vm_refl. Qed.
Lemma D_8fda0 : decode_any W_8fda0 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fda4 : bv 32 := 0x00008067.
Lemma F_8fda4 : fetch_word Plain.M.loaded_segments (0x8fdfc : word) = Some W_8fda4.
Proof. vm_refl. Qed.
Lemma D_8fda4 : decode_any W_8fda4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
