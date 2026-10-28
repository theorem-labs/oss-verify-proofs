(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18fa0 : bv 32 := 0xfa010113.
Lemma F_18fa0 : fetch_word Ubsan.M.loaded_segments (0x18fa0 : word) = Some W_18fa0.
Proof. vm_refl. Qed.
Lemma D_18fa0 : decode_any W_18fa0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa4 : bv 32 := 0x04113c23.
Lemma F_18fa4 : fetch_word Ubsan.M.loaded_segments (0x18fa4 : word) = Some W_18fa4.
Proof. vm_refl. Qed.
Lemma D_18fa4 : decode_any W_18fa4 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa8 : bv 32 := 0x04813823.
Lemma F_18fa8 : fetch_word Ubsan.M.loaded_segments (0x18fa8 : word) = Some W_18fa8.
Proof. vm_refl. Qed.
Lemma D_18fa8 : decode_any W_18fa8 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fac : bv 32 := 0x04913423.
Lemma F_18fac : fetch_word Ubsan.M.loaded_segments (0x18fac : word) = Some W_18fac.
Proof. vm_refl. Qed.
Lemma D_18fac : decode_any W_18fac = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb0 : bv 32 := 0x05213023.
Lemma F_18fb0 : fetch_word Ubsan.M.loaded_segments (0x18fb0 : word) = Some W_18fb0.
Proof. vm_refl. Qed.
Lemma D_18fb0 : decode_any W_18fb0 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb4 : bv 32 := 0x03313c23.
Lemma F_18fb4 : fetch_word Ubsan.M.loaded_segments (0x18fb4 : word) = Some W_18fb4.
Proof. vm_refl. Qed.
Lemma D_18fb4 : decode_any W_18fb4 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb8 : bv 32 := 0x03413823.
Lemma F_18fb8 : fetch_word Ubsan.M.loaded_segments (0x18fb8 : word) = Some W_18fb8.
Proof. vm_refl. Qed.
Lemma D_18fb8 : decode_any W_18fb8 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fbc : bv 32 := 0x03513423.
Lemma F_18fbc : fetch_word Ubsan.M.loaded_segments (0x18fbc : word) = Some W_18fbc.
Proof. vm_refl. Qed.
Lemma D_18fbc : decode_any W_18fbc = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fc0 : bv 32 := 0x03613023.
Lemma F_18fc0 : fetch_word Ubsan.M.loaded_segments (0x18fc0 : word) = Some W_18fc0.
Proof. vm_refl. Qed.
Lemma D_18fc0 : decode_any W_18fc0 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fc4 : bv 32 := 0x01713c23.
Lemma F_18fc4 : fetch_word Ubsan.M.loaded_segments (0x18fc4 : word) = Some W_18fc4.
Proof. vm_refl. Qed.
Lemma D_18fc4 : decode_any W_18fc4 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fc8 : bv 32 := 0x01813823.
Lemma F_18fc8 : fetch_word Ubsan.M.loaded_segments (0x18fc8 : word) = Some W_18fc8.
Proof. vm_refl. Qed.
Lemma D_18fc8 : decode_any W_18fc8 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fcc : bv 32 := 0x01913423.
Lemma F_18fcc : fetch_word Ubsan.M.loaded_segments (0x18fcc : word) = Some W_18fcc.
Proof. vm_refl. Qed.
Lemma D_18fcc : decode_any W_18fcc = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fd0 : bv 32 := 0x01a13023.
Lemma F_18fd0 : fetch_word Ubsan.M.loaded_segments (0x18fd0 : word) = Some W_18fd0.
Proof. vm_refl. Qed.
Lemma D_18fd0 : decode_any W_18fd0 = Some (Store SZ8 2 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fd4 : bv 32 := 0x0e050463.
Lemma F_18fd4 : fetch_word Ubsan.M.loaded_segments (0x18fd4 : word) = Some W_18fd4.
Proof. vm_refl. Qed.
Lemma D_18fd4 : decode_any W_18fd4 = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fd8 : bv 32 := 0x00757593.
Lemma F_18fd8 : fetch_word Ubsan.M.loaded_segments (0x18fd8 : word) = Some W_18fd8.
Proof. vm_refl. Qed.
Lemma D_18fd8 : decode_any W_18fd8 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fdc : bv 32 := 0x18059663.
Lemma F_18fdc : fetch_word Ubsan.M.loaded_segments (0x18fdc : word) = Some W_18fdc.
Proof. vm_refl. Qed.
Lemma D_18fdc : decode_any W_18fdc = Some (Branch BC_NE 11 0 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fe0 : bv 32 := 0x00053403.
Lemma F_18fe0 : fetch_word Ubsan.M.loaded_segments (0x18fe0 : word) = Some W_18fe0.
Proof. vm_refl. Qed.
Lemma D_18fe0 : decode_any W_18fe0 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fe4 : bv 32 := 0x14040663.
Lemma F_18fe4 : fetch_word Ubsan.M.loaded_segments (0x18fe4 : word) = Some W_18fe4.
Proof. vm_refl. Qed.
Lemma D_18fe4 : decode_any W_18fe4 = Some (Branch BC_EQ 8 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fe8 : bv 32 := 0x00747593.
Lemma F_18fe8 : fetch_word Ubsan.M.loaded_segments (0x18fe8 : word) = Some W_18fe8.
Proof. vm_refl. Qed.
Lemma D_18fe8 : decode_any W_18fe8 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fec : bv 32 := 0x16059e63.
Lemma F_18fec : fetch_word Ubsan.M.loaded_segments (0x18fec : word) = Some W_18fec.
Proof. vm_refl. Qed.
Lemma D_18fec : decode_any W_18fec = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff0 : bv 32 := 0x00840593.
Lemma F_18ff0 : fetch_word Ubsan.M.loaded_segments (0x18ff0 : word) = Some W_18ff0.
Proof. vm_refl. Qed.
Lemma D_18ff0 : decode_any W_18ff0 = Some (OpImm ALU_ADD 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff4 : bv 32 := 0xfff00613.
Lemma F_18ff4 : fetch_word Ubsan.M.loaded_segments (0x18ff4 : word) = Some W_18ff4.
Proof. vm_refl. Qed.
Lemma D_18ff4 : decode_any W_18ff4 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff8 : bv 32 := 0x06c5a5af.
Lemma F_18ff8 : fetch_word Ubsan.M.loaded_segments (0x18ff8 : word) = Some W_18ff8.
Proof. vm_refl. Qed.
Lemma D_18ff8 : decode_any W_18ff8 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ffc : bv 32 := 0x00100613.
Lemma F_18ffc : fetch_word Ubsan.M.loaded_segments (0x18ffc : word) = Some W_18ffc.
Proof. vm_refl. Qed.
Lemma D_18ffc : decode_any W_18ffc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19000 : bv 32 := 0x12c59663.
Lemma F_19000 : fetch_word Ubsan.M.loaded_segments (0x19000 : word) = Some W_19000.
Proof. vm_refl. Qed.
Lemma D_19000 : decode_any W_19000 = Some (Branch BC_NE 11 12 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_19004 : bv 32 := 0x00050993.
Lemma F_19004 : fetch_word Ubsan.M.loaded_segments (0x19004 : word) = Some W_19004.
Proof. vm_refl. Qed.
Lemma D_19004 : decode_any W_19004 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19008 : bv 32 := 0x00042503.
Lemma F_19008 : fetch_word Ubsan.M.loaded_segments (0x19008 : word) = Some W_19008.
Proof. vm_refl. Qed.
Lemma D_19008 : decode_any W_19008 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1900c : bv 32 := 0x10a05663.
Lemma F_1900c : fetch_word Ubsan.M.loaded_segments (0x1900c : word) = Some W_1900c.
Proof. vm_refl. Qed.
Lemma D_1900c : decode_any W_1900c = Some (Branch BC_GE 0 10 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_19010 : bv 32 := 0x00000a13.
Lemma F_19010 : fetch_word Ubsan.M.loaded_segments (0x19010 : word) = Some W_19010.
Proof. vm_refl. Qed.
Lemma D_19010 : decode_any W_19010 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19014 : bv 32 := 0x00000a93.
Lemma F_19014 : fetch_word Ubsan.M.loaded_segments (0x19014 : word) = Some W_19014.
Proof. vm_refl. Qed.
Lemma D_19014 : decode_any W_19014 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19018 : bv 32 := 0x0002c517.
Lemma F_19018 : fetch_word Ubsan.M.loaded_segments (0x19018 : word) = Some W_19018.
Proof. vm_refl. Qed.
Lemma D_19018 : decode_any W_19018 = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1901c : bv 32 := 0x00400b13.
Lemma F_1901c : fetch_word Ubsan.M.loaded_segments (0x1901c : word) = Some W_1901c.
Proof. vm_refl. Qed.
Lemma D_1901c : decode_any W_1901c = Some (OpImm ALU_ADD 22 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19020 : bv 32 := 0xffff9597.
Lemma F_19020 : fetch_word Ubsan.M.loaded_segments (0x19020 : word) = Some W_19020.
Proof. vm_refl. Qed.
Lemma D_19020 : decode_any W_19020 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_19024 : bv 32 := 0xe8053b83.
Lemma F_19024 : fetch_word Ubsan.M.loaded_segments (0x19024 : word) = Some W_19024.
Proof. vm_refl. Qed.
Lemma D_19024 : decode_any W_19024 = Some (Load SZ8 true 23 10 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_19028 : bv 32 := 0x0ec58493.
Lemma F_19028 : fetch_word Ubsan.M.loaded_segments (0x19028 : word) = Some W_19028.
Proof. vm_refl. Qed.
Lemma D_19028 : decode_any W_19028 = Some (OpImm ALU_ADD 9 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_1902c : bv 32 := 0xffff8517.
Lemma F_1902c : fetch_word Ubsan.M.loaded_segments (0x1902c : word) = Some W_1902c.
Proof. vm_refl. Qed.
Lemma D_1902c : decode_any W_1902c = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19030 : bv 32 := 0xfc650913.
Lemma F_19030 : fetch_word Ubsan.M.loaded_segments (0x19030 : word) = Some W_19030.
Proof. vm_refl. Qed.
Lemma D_19030 : decode_any W_19030 = Some (OpImm ALU_ADD 18 10 4038, 4%Z).
Proof. vm_refl. Qed.

Definition W_19034 : bv 32 := 0xfff00c13.
Lemma F_19034 : fetch_word Ubsan.M.loaded_segments (0x19034 : word) = Some W_19034.
Proof. vm_refl. Qed.
Lemma D_19034 : decode_any W_19034 = Some (OpImm ALU_ADD 24 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_19038 : bv 32 := 0x00100c93.
Lemma F_19038 : fetch_word Ubsan.M.loaded_segments (0x19038 : word) = Some W_19038.
Proof. vm_refl. Qed.
Lemma D_19038 : decode_any W_19038 = Some (OpImm ALU_ADD 25 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1903c : bv 32 := 0x0180006f.
Lemma F_1903c : fetch_word Ubsan.M.loaded_segments (0x1903c : word) = Some W_1903c.
Proof. vm_refl. Qed.
Lemma D_1903c : decode_any W_1903c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19040 : bv 32 := 0x000d3023.
Lemma F_19040 : fetch_word Ubsan.M.loaded_segments (0x19040 : word) = Some W_19040.
Proof. vm_refl. Qed.
Lemma D_19040 : decode_any W_19040 = Some (Store SZ8 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19044 : bv 32 := 0x00042503.
Lemma F_19044 : fetch_word Ubsan.M.loaded_segments (0x19044 : word) = Some W_19044.
Proof. vm_refl. Qed.
Lemma D_19044 : decode_any W_19044 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19048 : bv 32 := 0x001a8a93.
Lemma F_19048 : fetch_word Ubsan.M.loaded_segments (0x19048 : word) = Some W_19048.
Proof. vm_refl. Qed.
Lemma D_19048 : decode_any W_19048 = Some (OpImm ALU_ADD 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1904c : bv 32 := 0x008a0a13.
Lemma F_1904c : fetch_word Ubsan.M.loaded_segments (0x1904c : word) = Some W_1904c.
Proof. vm_refl. Qed.
Lemma D_1904c : decode_any W_1904c = Some (OpImm ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19050 : bv 32 := 0x0caad463.
Lemma F_19050 : fetch_word Ubsan.M.loaded_segments (0x19050 : word) = Some W_19050.
Proof. vm_refl. Qed.
Lemma D_19050 : decode_any W_19050 = Some (Branch BC_GE 21 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_19054 : bv 32 := 0x01043503.
Lemma F_19054 : fetch_word Ubsan.M.loaded_segments (0x19054 : word) = Some W_19054.
Proof. vm_refl. Qed.
Lemma D_19054 : decode_any W_19054 = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19058 : bv 32 := 0x00aa0d33.
Lemma F_19058 : fetch_word Ubsan.M.loaded_segments (0x19058 : word) = Some W_19058.
Proof. vm_refl. Qed.
Lemma D_19058 : decode_any W_19058 = Some (Op ALU_ADD 26 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1905c : bv 32 := 0x10ad6663.
Lemma F_1905c : fetch_word Ubsan.M.loaded_segments (0x1905c : word) = Some W_1905c.
Proof. vm_refl. Qed.
Lemma D_1905c : decode_any W_1905c = Some (Branch BC_LTU 26 10 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_19060 : bv 32 := 0x00a035b3.
Lemma F_19060 : fetch_word Ubsan.M.loaded_segments (0x19060 : word) = Some W_19060.
Proof. vm_refl. Qed.
Lemma D_19060 : decode_any W_19060 = Some (Op ALU_SLTU 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19064 : bv 32 := 0x001d3613.
Lemma F_19064 : fetch_word Ubsan.M.loaded_segments (0x19064 : word) = Some W_19064.
Proof. vm_refl. Qed.
Lemma D_19064 : decode_any W_19064 = Some (OpImm ALU_SLTU 12 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19068 : bv 32 := 0x00c5c5b3.
Lemma F_19068 : fetch_word Ubsan.M.loaded_segments (0x19068 : word) = Some W_19068.
Proof. vm_refl. Qed.
Lemma D_19068 : decode_any W_19068 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1906c : bv 32 := 0x0e058e63.
Lemma F_1906c : fetch_word Ubsan.M.loaded_segments (0x1906c : word) = Some W_1906c.
Proof. vm_refl. Qed.
Lemma D_1906c : decode_any W_1906c = Some (Branch BC_EQ 11 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_19070 : bv 32 := 0x02050a63.
Lemma F_19070 : fetch_word Ubsan.M.loaded_segments (0x19070 : word) = Some W_19070.
Proof. vm_refl. Qed.
Lemma D_19070 : decode_any W_19070 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_19074 : bv 32 := 0x00aa0533.
Lemma F_19074 : fetch_word Ubsan.M.loaded_segments (0x19074 : word) = Some W_19074.
Proof. vm_refl. Qed.
Lemma D_19074 : decode_any W_19074 = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19078 : bv 32 := 0x00757513.
Lemma F_19078 : fetch_word Ubsan.M.loaded_segments (0x19078 : word) = Some W_19078.
Proof. vm_refl. Qed.
Lemma D_19078 : decode_any W_19078 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1907c : bv 32 := 0x0e051663.
Lemma F_1907c : fetch_word Ubsan.M.loaded_segments (0x1907c : word) = Some W_1907c.
Proof. vm_refl. Qed.
Lemma D_1907c : decode_any W_1907c = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_19080 : bv 32 := 0x000d3503.
Lemma F_19080 : fetch_word Ubsan.M.loaded_segments (0x19080 : word) = Some W_19080.
Proof. vm_refl. Qed.
Lemma D_19080 : decode_any W_19080 = Some (Load SZ8 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19084 : bv 32 := 0xfc0500e3.
Lemma F_19084 : fetch_word Ubsan.M.loaded_segments (0x19084 : word) = Some W_19084.
Proof. vm_refl. Qed.
Lemma D_19084 : decode_any W_19084 = Some (Branch BC_EQ 10 0 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_19088 : bv 32 := 0x00357593.
Lemma F_19088 : fetch_word Ubsan.M.loaded_segments (0x19088 : word) = Some W_19088.
Proof. vm_refl. Qed.
Lemma D_19088 : decode_any W_19088 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1908c : bv 32 := 0x0c059e63.
Lemma F_1908c : fetch_word Ubsan.M.loaded_segments (0x1908c : word) = Some W_1908c.
Proof. vm_refl. Qed.
Lemma D_1908c : decode_any W_1908c = Some (Branch BC_NE 11 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_19090 : bv 32 := 0x01050593.
Lemma F_19090 : fetch_word Ubsan.M.loaded_segments (0x19090 : word) = Some W_19090.
Proof. vm_refl. Qed.
Lemma D_19090 : decode_any W_19090 = Some (OpImm ALU_ADD 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19094 : bv 32 := 0x0785a5af.
Lemma F_19094 : fetch_word Ubsan.M.loaded_segments (0x19094 : word) = Some W_19094.
Proof. vm_refl. Qed.
Lemma D_19094 : decode_any W_19094 = Some (Amo AMO_ADD AW true true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19098 : bv 32 := 0xfb9594e3.
Lemma F_19098 : fetch_word Ubsan.M.loaded_segments (0x19098 : word) = Some W_19098.
Proof. vm_refl. Qed.
Lemma D_19098 : decode_any W_19098 = Some (Branch BC_NE 11 25 8104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1909c : bv 32 := 0x194230ef.
Lemma F_1909c : fetch_word Ubsan.M.loaded_segments (0x1909c : word) = Some W_1909c.
Proof. vm_refl. Qed.
Lemma D_1909c : decode_any W_1909c = Some (Jal 1 143764, 4%Z).
Proof. vm_refl. Qed.

Definition W_190a0 : bv 32 := 0xfa1ff06f.
Lemma F_190a0 : fetch_word Ubsan.M.loaded_segments (0x190a0 : word) = Some W_190a0.
Proof. vm_refl. Qed.
Lemma D_190a0 : decode_any W_190a0 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_190a4 : bv 32 := 0x000ba503.
Lemma F_190a4 : fetch_word Ubsan.M.loaded_segments (0x190a4 : word) = Some W_190a4.
Proof. vm_refl. Qed.
Lemma D_190a4 : decode_any W_190a4 = Some (Load SZ4 true 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190a8 : bv 32 := 0xf8ab4ee3.
Lemma F_190a8 : fetch_word Ubsan.M.loaded_segments (0x190a8 : word) = Some W_190a8.
Proof. vm_refl. Qed.
Lemma D_190a8 : decode_any W_190a8 = Some (Branch BC_LT 22 10 8092, 4%Z).
Proof. vm_refl. Qed.

Definition W_190ac : bv 32 := 0x00048513.
Lemma F_190ac : fetch_word Ubsan.M.loaded_segments (0x190ac : word) = Some W_190ac.
Proof. vm_refl. Qed.
Lemma D_190ac : decode_any W_190ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190b0 : bv 32 := 0x00090593.
Lemma F_190b0 : fetch_word Ubsan.M.loaded_segments (0x190b0 : word) = Some W_190b0.
Proof. vm_refl. Qed.
Lemma D_190b0 : decode_any W_190b0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190b4 : bv 32 := 0xd75fe0ef.
Lemma F_190b4 : fetch_word Ubsan.M.loaded_segments (0x190b4 : word) = Some W_190b4.
Proof. vm_refl. Qed.
Lemma D_190b4 : decode_any W_190b4 = Some (Jal 1 2092404, 4%Z).
Proof. vm_refl. Qed.

Definition W_190b8 : bv 32 := 0xf8dff06f.
Lemma F_190b8 : fetch_word Ubsan.M.loaded_segments (0x190b8 : word) = Some W_190b8.
Proof. vm_refl. Qed.
Lemma D_190b8 : decode_any W_190b8 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_190bc : bv 32 := 0x0002c517.
Lemma F_190bc : fetch_word Ubsan.M.loaded_segments (0x190bc : word) = Some W_190bc.
Proof. vm_refl. Qed.
Lemma D_190bc : decode_any W_190bc = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_190c0 : bv 32 := 0xddc53503.
Lemma F_190c0 : fetch_word Ubsan.M.loaded_segments (0x190c0 : word) = Some W_190c0.
Proof. vm_refl. Qed.
Lemma D_190c0 : decode_any W_190c0 = Some (Load SZ8 true 10 10 3548, 4%Z).
Proof. vm_refl. Qed.

Definition W_190c4 : bv 32 := 0x00052503.
Lemma F_190c4 : fetch_word Ubsan.M.loaded_segments (0x190c4 : word) = Some W_190c4.
Proof. vm_refl. Qed.
Lemma D_190c4 : decode_any W_190c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_190c8 : bv 32 := 0x00400593.
Lemma F_190c8 : fetch_word Ubsan.M.loaded_segments (0x190c8 : word) = Some W_190c8.
Proof. vm_refl. Qed.
Lemma D_190c8 : decode_any W_190c8 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_190cc : bv 32 := 0x06a5c263.
Lemma F_190cc : fetch_word Ubsan.M.loaded_segments (0x190cc : word) = Some W_190cc.
Proof. vm_refl. Qed.
Lemma D_190cc : decode_any W_190cc = Some (Branch BC_LT 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_190d0 : bv 32 := 0xffff9517.
Lemma F_190d0 : fetch_word Ubsan.M.loaded_segments (0x190d0 : word) = Some W_190d0.
Proof. vm_refl. Qed.
Lemma D_190d0 : decode_any W_190d0 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_190d4 : bv 32 := 0xffff9597.
Lemma F_190d4 : fetch_word Ubsan.M.loaded_segments (0x190d4 : word) = Some W_190d4.
Proof. vm_refl. Qed.
Lemma D_190d4 : decode_any W_190d4 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_190d8 : bv 32 := 0x03c50513.
Lemma F_190d8 : fetch_word Ubsan.M.loaded_segments (0x190d8 : word) = Some W_190d8.
Proof. vm_refl. Qed.
Lemma D_190d8 : decode_any W_190d8 = Some (OpImm ALU_ADD 10 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_190dc : bv 32 := 0x90258593.
Lemma F_190dc : fetch_word Ubsan.M.loaded_segments (0x190dc : word) = Some W_190dc.
Proof. vm_refl. Qed.
Lemma D_190dc : decode_any W_190dc = Some (OpImm ALU_ADD 11 11 2306, 4%Z).
Proof. vm_refl. Qed.

Definition W_190e0 : bv 32 := 0x05813083.
Lemma F_190e0 : fetch_word Ubsan.M.loaded_segments (0x190e0 : word) = Some W_190e0.
Proof. vm_refl. Qed.
Lemma D_190e0 : decode_any W_190e0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_190e4 : bv 32 := 0x05013403.
Lemma F_190e4 : fetch_word Ubsan.M.loaded_segments (0x190e4 : word) = Some W_190e4.
Proof. vm_refl. Qed.
Lemma D_190e4 : decode_any W_190e4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_190e8 : bv 32 := 0x04813483.
Lemma F_190e8 : fetch_word Ubsan.M.loaded_segments (0x190e8 : word) = Some W_190e8.
Proof. vm_refl. Qed.
Lemma D_190e8 : decode_any W_190e8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_190ec : bv 32 := 0x04013903.
Lemma F_190ec : fetch_word Ubsan.M.loaded_segments (0x190ec : word) = Some W_190ec.
Proof. vm_refl. Qed.
Lemma D_190ec : decode_any W_190ec = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_190f0 : bv 32 := 0x03813983.
Lemma F_190f0 : fetch_word Ubsan.M.loaded_segments (0x190f0 : word) = Some W_190f0.
Proof. vm_refl. Qed.
Lemma D_190f0 : decode_any W_190f0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_190f4 : bv 32 := 0x03013a03.
Lemma F_190f4 : fetch_word Ubsan.M.loaded_segments (0x190f4 : word) = Some W_190f4.
Proof. vm_refl. Qed.
Lemma D_190f4 : decode_any W_190f4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_190f8 : bv 32 := 0x02813a83.
Lemma F_190f8 : fetch_word Ubsan.M.loaded_segments (0x190f8 : word) = Some W_190f8.
Proof. vm_refl. Qed.
Lemma D_190f8 : decode_any W_190f8 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_190fc : bv 32 := 0x02013b03.
Lemma F_190fc : fetch_word Ubsan.M.loaded_segments (0x190fc : word) = Some W_190fc.
Proof. vm_refl. Qed.
Lemma D_190fc : decode_any W_190fc = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19100 : bv 32 := 0x01813b83.
Lemma F_19100 : fetch_word Ubsan.M.loaded_segments (0x19100 : word) = Some W_19100.
Proof. vm_refl. Qed.
Lemma D_19100 : decode_any W_19100 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19104 : bv 32 := 0x01013c03.
Lemma F_19104 : fetch_word Ubsan.M.loaded_segments (0x19104 : word) = Some W_19104.
Proof. vm_refl. Qed.
Lemma D_19104 : decode_any W_19104 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19108 : bv 32 := 0x00813c83.
Lemma F_19108 : fetch_word Ubsan.M.loaded_segments (0x19108 : word) = Some W_19108.
Proof. vm_refl. Qed.
Lemma D_19108 : decode_any W_19108 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1910c : bv 32 := 0x00013d03.
Lemma F_1910c : fetch_word Ubsan.M.loaded_segments (0x1910c : word) = Some W_1910c.
Proof. vm_refl. Qed.
Lemma D_1910c : decode_any W_1910c = Some (Load SZ8 true 26 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19110 : bv 32 := 0x06010113.
Lemma F_19110 : fetch_word Ubsan.M.loaded_segments (0x19110 : word) = Some W_19110.
Proof. vm_refl. Qed.
Lemma D_19110 : decode_any W_19110 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19114 : bv 32 := 0xd15fe06f.
Lemma F_19114 : fetch_word Ubsan.M.loaded_segments (0x19114 : word) = Some W_19114.
Proof. vm_refl. Qed.
Lemma D_19114 : decode_any W_19114 = Some (Jal 0 2092308, 4%Z).
Proof. vm_refl. Qed.

Definition W_19118 : bv 32 := 0x01043503.
Lemma F_19118 : fetch_word Ubsan.M.loaded_segments (0x19118 : word) = Some W_19118.
Proof. vm_refl. Qed.
Lemma D_19118 : decode_any W_19118 = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1911c : bv 32 := 0x114230ef.
Lemma F_1911c : fetch_word Ubsan.M.loaded_segments (0x1911c : word) = Some W_1911c.
Proof. vm_refl. Qed.
Lemma D_1911c : decode_any W_1911c = Some (Jal 1 143636, 4%Z).
Proof. vm_refl. Qed.

Definition W_19120 : bv 32 := 0x00040513.
Lemma F_19120 : fetch_word Ubsan.M.loaded_segments (0x19120 : word) = Some W_19120.
Proof. vm_refl. Qed.
Lemma D_19120 : decode_any W_19120 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19124 : bv 32 := 0x10c230ef.
Lemma F_19124 : fetch_word Ubsan.M.loaded_segments (0x19124 : word) = Some W_19124.
Proof. vm_refl. Qed.
Lemma D_19124 : decode_any W_19124 = Some (Jal 1 143628, 4%Z).
Proof. vm_refl. Qed.

Definition W_19128 : bv 32 := 0x00098513.
Lemma F_19128 : fetch_word Ubsan.M.loaded_segments (0x19128 : word) = Some W_19128.
Proof. vm_refl. Qed.
Lemma D_19128 : decode_any W_19128 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1912c : bv 32 := 0x00053023.
Lemma F_1912c : fetch_word Ubsan.M.loaded_segments (0x1912c : word) = Some W_1912c.
Proof. vm_refl. Qed.
Lemma D_1912c : decode_any W_1912c = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19130 : bv 32 := 0x05813083.
Lemma F_19130 : fetch_word Ubsan.M.loaded_segments (0x19130 : word) = Some W_19130.
Proof. vm_refl. Qed.
Lemma D_19130 : decode_any W_19130 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19134 : bv 32 := 0x05013403.
Lemma F_19134 : fetch_word Ubsan.M.loaded_segments (0x19134 : word) = Some W_19134.
Proof. vm_refl. Qed.
Lemma D_19134 : decode_any W_19134 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19138 : bv 32 := 0x04813483.
Lemma F_19138 : fetch_word Ubsan.M.loaded_segments (0x19138 : word) = Some W_19138.
Proof. vm_refl. Qed.
Lemma D_19138 : decode_any W_19138 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1913c : bv 32 := 0x04013903.
Lemma F_1913c : fetch_word Ubsan.M.loaded_segments (0x1913c : word) = Some W_1913c.
Proof. vm_refl. Qed.
Lemma D_1913c : decode_any W_1913c = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_19140 : bv 32 := 0x03813983.
Lemma F_19140 : fetch_word Ubsan.M.loaded_segments (0x19140 : word) = Some W_19140.
Proof. vm_refl. Qed.
Lemma D_19140 : decode_any W_19140 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19144 : bv 32 := 0x03013a03.
Lemma F_19144 : fetch_word Ubsan.M.loaded_segments (0x19144 : word) = Some W_19144.
Proof. vm_refl. Qed.
Lemma D_19144 : decode_any W_19144 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19148 : bv 32 := 0x02813a83.
Lemma F_19148 : fetch_word Ubsan.M.loaded_segments (0x19148 : word) = Some W_19148.
Proof. vm_refl. Qed.
Lemma D_19148 : decode_any W_19148 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1914c : bv 32 := 0x02013b03.
Lemma F_1914c : fetch_word Ubsan.M.loaded_segments (0x1914c : word) = Some W_1914c.
Proof. vm_refl. Qed.
Lemma D_1914c : decode_any W_1914c = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19150 : bv 32 := 0x01813b83.
Lemma F_19150 : fetch_word Ubsan.M.loaded_segments (0x19150 : word) = Some W_19150.
Proof. vm_refl. Qed.
Lemma D_19150 : decode_any W_19150 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19154 : bv 32 := 0x01013c03.
Lemma F_19154 : fetch_word Ubsan.M.loaded_segments (0x19154 : word) = Some W_19154.
Proof. vm_refl. Qed.
Lemma D_19154 : decode_any W_19154 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19158 : bv 32 := 0x00813c83.
Lemma F_19158 : fetch_word Ubsan.M.loaded_segments (0x19158 : word) = Some W_19158.
Proof. vm_refl. Qed.
Lemma D_19158 : decode_any W_19158 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1915c : bv 32 := 0x00013d03.
Lemma F_1915c : fetch_word Ubsan.M.loaded_segments (0x1915c : word) = Some W_1915c.
Proof. vm_refl. Qed.
Lemma D_1915c : decode_any W_1915c = Some (Load SZ8 true 26 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19160 : bv 32 := 0x06010113.
Lemma F_19160 : fetch_word Ubsan.M.loaded_segments (0x19160 : word) = Some W_19160.
Proof. vm_refl. Qed.
Lemma D_19160 : decode_any W_19160 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19164 : bv 32 := 0x00008067.
Lemma F_19164 : fetch_word Ubsan.M.loaded_segments (0x19164 : word) = Some W_19164.
Proof. vm_refl. Qed.
Lemma D_19164 : decode_any W_19164 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19168 : bv 32 := 0xc0001073.
Lemma F_19168 : fetch_word Ubsan.M.loaded_segments (0x19168 : word) = Some W_19168.
Proof. vm_refl. Qed.
Lemma D_19168 : decode_any W_19168 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
