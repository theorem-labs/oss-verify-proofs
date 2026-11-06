(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_19000 : bv 32 := 0x04b51063.
Lemma F_19000 : fetch_word Plain.M.loaded_segments (0x19058 : word) = Some W_19000.
Proof. vm_refl. Qed.
Lemma D_19000 : decode_any W_19000 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19004 : bv 32 := 0x03843503.
Lemma F_19004 : fetch_word Plain.M.loaded_segments (0x1905c : word) = Some W_19004.
Proof. vm_refl. Qed.
Lemma D_19004 : decode_any W_19004 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19008 : bv 32 := 0x00050663.
Lemma F_19008 : fetch_word Plain.M.loaded_segments (0x19060 : word) = Some W_19008.
Proof. vm_refl. Qed.
Lemma D_19008 : decode_any W_19008 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19014 : bv 32 := 0x02843503.
Lemma F_19014 : fetch_word Plain.M.loaded_segments (0x1906c : word) = Some W_19014.
Proof. vm_refl. Qed.
Lemma D_19014 : decode_any W_19014 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19018 : bv 32 := 0x00050463.
Lemma F_19018 : fetch_word Plain.M.loaded_segments (0x19070 : word) = Some W_19018.
Proof. vm_refl. Qed.
Lemma D_19018 : decode_any W_19018 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19020 : bv 32 := 0x03043503.
Lemma F_19020 : fetch_word Plain.M.loaded_segments (0x19078 : word) = Some W_19020.
Proof. vm_refl. Qed.
Lemma D_19020 : decode_any W_19020 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19024 : bv 32 := 0x00a13423.
Lemma F_19024 : fetch_word Plain.M.loaded_segments (0x1907c : word) = Some W_19024.
Proof. vm_refl. Qed.
Lemma D_19024 : decode_any W_19024 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19028 : bv 32 := 0x00050863.
Lemma F_19028 : fetch_word Plain.M.loaded_segments (0x19080 : word) = Some W_19028.
Proof. vm_refl. Qed.
Lemma D_19028 : decode_any W_19028 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19038 : bv 32 := 0x00040513.
Lemma F_19038 : fetch_word Plain.M.loaded_segments (0x19090 : word) = Some W_19038.
Proof. vm_refl. Qed.
Lemma D_19038 : decode_any W_19038 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1903c : bv 32 := 0x778160ef.
Lemma F_1903c : fetch_word Plain.M.loaded_segments (0x19094 : word) = Some W_1903c.
Proof. vm_refl. Qed.
Lemma D_1903c : decode_any W_1903c = Some (Jal 1 92024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19040 : bv 32 := 0x0001f517.
Lemma F_19040 : fetch_word Plain.M.loaded_segments (0x19098 : word) = Some W_19040.
Proof. vm_refl. Qed.
Lemma D_19040 : decode_any W_19040 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19044 : bv 32 := 0x3d853503.
Lemma F_19044 : fetch_word Plain.M.loaded_segments (0x1909c : word) = Some W_19044.
Proof. vm_refl. Qed.
Lemma D_19044 : decode_any W_19044 = Some (Load SZ8 true 10 10 984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19048 : bv 32 := 0x00052503.
Lemma F_19048 : fetch_word Plain.M.loaded_segments (0x190a0 : word) = Some W_19048.
Proof. vm_refl. Qed.
Lemma D_19048 : decode_any W_19048 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1904c : bv 32 := 0x00500593.
Lemma F_1904c : fetch_word Plain.M.loaded_segments (0x190a4 : word) = Some W_1904c.
Proof. vm_refl. Qed.
Lemma D_1904c : decode_any W_1904c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19050 : bv 32 := 0x02a5c263.
Lemma F_19050 : fetch_word Plain.M.loaded_segments (0x190a8 : word) = Some W_19050.
Proof. vm_refl. Qed.
Lemma D_19050 : decode_any W_19050 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19054 : bv 32 := 0xffff9517.
Lemma F_19054 : fetch_word Plain.M.loaded_segments (0x190ac : word) = Some W_19054.
Proof. vm_refl. Qed.
Lemma D_19054 : decode_any W_19054 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19058 : bv 32 := 0xffff8597.
Lemma F_19058 : fetch_word Plain.M.loaded_segments (0x190b0 : word) = Some W_19058.
Proof. vm_refl. Qed.
Lemma D_19058 : decode_any W_19058 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1905c : bv 32 := 0xc7650513.
Lemma F_1905c : fetch_word Plain.M.loaded_segments (0x190b4 : word) = Some W_1905c.
Proof. vm_refl. Qed.
Lemma D_1905c : decode_any W_1905c = Some (OpImm ALU_ADD 10 10 3190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19060 : bv 32 := 0xa0558593.
Lemma F_19060 : fetch_word Plain.M.loaded_segments (0x190b8 : word) = Some W_19060.
Proof. vm_refl. Qed.
Lemma D_19060 : decode_any W_19060 = Some (OpImm ALU_ADD 11 11 2565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19064 : bv 32 := 0x00000613.
Lemma F_19064 : fetch_word Plain.M.loaded_segments (0x190bc : word) = Some W_19064.
Proof. vm_refl. Qed.
Lemma D_19064 : decode_any W_19064 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19068 : bv 32 := 0xbb5fe0ef.
Lemma F_19068 : fetch_word Plain.M.loaded_segments (0x190c0 : word) = Some W_19068.
Proof. vm_refl. Qed.
Lemma D_19068 : decode_any W_19068 = Some (Jal 1 2091956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1906c : bv 32 := 0x00050413.
Lemma F_1906c : fetch_word Plain.M.loaded_segments (0x190c4 : word) = Some W_1906c.
Proof. vm_refl. Qed.
Lemma D_1906c : decode_any W_1906c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19070 : bv 32 := 0x0080006f.
Lemma F_19070 : fetch_word Plain.M.loaded_segments (0x190c8 : word) = Some W_19070.
Proof. vm_refl. Qed.
Lemma D_19070 : decode_any W_19070 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19078 : bv 32 := 0x00040513.
Lemma F_19078 : fetch_word Plain.M.loaded_segments (0x190d0 : word) = Some W_19078.
Proof. vm_refl. Qed.
Lemma D_19078 : decode_any W_19078 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1907c : bv 32 := 0x02813083.
Lemma F_1907c : fetch_word Plain.M.loaded_segments (0x190d4 : word) = Some W_1907c.
Proof. vm_refl. Qed.
Lemma D_1907c : decode_any W_1907c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19080 : bv 32 := 0x02013403.
Lemma F_19080 : fetch_word Plain.M.loaded_segments (0x190d8 : word) = Some W_19080.
Proof. vm_refl. Qed.
Lemma D_19080 : decode_any W_19080 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19084 : bv 32 := 0x01813483.
Lemma F_19084 : fetch_word Plain.M.loaded_segments (0x190dc : word) = Some W_19084.
Proof. vm_refl. Qed.
Lemma D_19084 : decode_any W_19084 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19088 : bv 32 := 0x01013903.
Lemma F_19088 : fetch_word Plain.M.loaded_segments (0x190e0 : word) = Some W_19088.
Proof. vm_refl. Qed.
Lemma D_19088 : decode_any W_19088 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1908c : bv 32 := 0x03010113.
Lemma F_1908c : fetch_word Plain.M.loaded_segments (0x190e4 : word) = Some W_1908c.
Proof. vm_refl. Qed.
Lemma D_1908c : decode_any W_1908c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19090 : bv 32 := 0x00008067.
Lemma F_19090 : fetch_word Plain.M.loaded_segments (0x190e8 : word) = Some W_19090.
Proof. vm_refl. Qed.
Lemma D_19090 : decode_any W_19090 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19554 : bv 32 := 0xfe010113.
Lemma F_19554 : fetch_word Plain.M.loaded_segments (0x195ac : word) = Some W_19554.
Proof. vm_refl. Qed.
Lemma D_19554 : decode_any W_19554 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19558 : bv 32 := 0x00113c23.
Lemma F_19558 : fetch_word Plain.M.loaded_segments (0x195b0 : word) = Some W_19558.
Proof. vm_refl. Qed.
Lemma D_19558 : decode_any W_19558 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1955c : bv 32 := 0x00813823.
Lemma F_1955c : fetch_word Plain.M.loaded_segments (0x195b4 : word) = Some W_1955c.
Proof. vm_refl. Qed.
Lemma D_1955c : decode_any W_1955c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19560 : bv 32 := 0x00913423.
Lemma F_19560 : fetch_word Plain.M.loaded_segments (0x195b8 : word) = Some W_19560.
Proof. vm_refl. Qed.
Lemma D_19560 : decode_any W_19560 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19564 : bv 32 := 0x02050a63.
Lemma F_19564 : fetch_word Plain.M.loaded_segments (0x195bc : word) = Some W_19564.
Proof. vm_refl. Qed.
Lemma D_19564 : decode_any W_19564 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19568 : bv 32 := 0x00050493.
Lemma F_19568 : fetch_word Plain.M.loaded_segments (0x195c0 : word) = Some W_19568.
Proof. vm_refl. Qed.
Lemma D_19568 : decode_any W_19568 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1956c : bv 32 := 0x00052503.
Lemma F_1956c : fetch_word Plain.M.loaded_segments (0x195c4 : word) = Some W_1956c.
Proof. vm_refl. Qed.
Lemma D_1956c : decode_any W_1956c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19570 : bv 32 := 0x0044a583.
Lemma F_19570 : fetch_word Plain.M.loaded_segments (0x195c8 : word) = Some W_19570.
Proof. vm_refl. Qed.
Lemma D_19570 : decode_any W_19570 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19574 : bv 32 := 0x0084a603.
Lemma F_19574 : fetch_word Plain.M.loaded_segments (0x195cc : word) = Some W_19574.
Proof. vm_refl. Qed.
Lemma D_19574 : decode_any W_19574 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19578 : bv 32 := 0x9e1ff0ef.
Lemma F_19578 : fetch_word Plain.M.loaded_segments (0x195d0 : word) = Some W_19578.
Proof. vm_refl. Qed.
Lemma D_19578 : decode_any W_19578 = Some (Jal 1 2095584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1957c : bv 32 := 0x04050263.
Lemma F_1957c : fetch_word Plain.M.loaded_segments (0x195d4 : word) = Some W_1957c.
Proof. vm_refl. Qed.
Lemma D_1957c : decode_any W_1957c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19580 : bv 32 := 0x00050413.
Lemma F_19580 : fetch_word Plain.M.loaded_segments (0x195d8 : word) = Some W_19580.
Proof. vm_refl. Qed.
Lemma D_19580 : decode_any W_19580 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19584 : bv 32 := 0x08a48063.
Lemma F_19584 : fetch_word Plain.M.loaded_segments (0x195dc : word) = Some W_19584.
Proof. vm_refl. Qed.
Lemma D_19584 : decode_any W_19584 = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19588 : bv 32 := 0x00c4a503.
Lemma F_19588 : fetch_word Plain.M.loaded_segments (0x195e0 : word) = Some W_19588.
Proof. vm_refl. Qed.
Lemma D_19588 : decode_any W_19588 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1958c : bv 32 := 0x08a05463.
Lemma F_1958c : fetch_word Plain.M.loaded_segments (0x195e4 : word) = Some W_1958c.
Proof. vm_refl. Qed.
Lemma D_1958c : decode_any W_1958c = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19590 : bv 32 := 0x00a42623.
Lemma F_19590 : fetch_word Plain.M.loaded_segments (0x195e8 : word) = Some W_19590.
Proof. vm_refl. Qed.
Lemma D_19590 : decode_any W_19590 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19594 : bv 32 := 0x0ac0006f.
Lemma F_19594 : fetch_word Plain.M.loaded_segments (0x195ec : word) = Some W_19594.
Proof. vm_refl. Qed.
Lemma D_19594 : decode_any W_19594 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195c0 : bv 32 := 0x0001f517.
Lemma F_195c0 : fetch_word Plain.M.loaded_segments (0x19618 : word) = Some W_195c0.
Proof. vm_refl. Qed.
Lemma D_195c0 : decode_any W_195c0 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195c4 : bv 32 := 0xe5853503.
Lemma F_195c4 : fetch_word Plain.M.loaded_segments (0x1961c : word) = Some W_195c4.
Proof. vm_refl. Qed.
Lemma D_195c4 : decode_any W_195c4 = Some (Load SZ8 true 10 10 3672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195c8 : bv 32 := 0x00052503.
Lemma F_195c8 : fetch_word Plain.M.loaded_segments (0x19620 : word) = Some W_195c8.
Proof. vm_refl. Qed.
Lemma D_195c8 : decode_any W_195c8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195cc : bv 32 := 0x00500593.
Lemma F_195cc : fetch_word Plain.M.loaded_segments (0x19624 : word) = Some W_195cc.
Proof. vm_refl. Qed.
Lemma D_195cc : decode_any W_195cc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195d0 : bv 32 := 0x02a5c663.
Lemma F_195d0 : fetch_word Plain.M.loaded_segments (0x19628 : word) = Some W_195d0.
Proof. vm_refl. Qed.
Lemma D_195d0 : decode_any W_195d0 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195d4 : bv 32 := 0xffff7517.
Lemma F_195d4 : fetch_word Plain.M.loaded_segments (0x1962c : word) = Some W_195d4.
Proof. vm_refl. Qed.
Lemma D_195d4 : decode_any W_195d4 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195d8 : bv 32 := 0xffff8597.
Lemma F_195d8 : fetch_word Plain.M.loaded_segments (0x19630 : word) = Some W_195d8.
Proof. vm_refl. Qed.
Lemma D_195d8 : decode_any W_195d8 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195dc : bv 32 := 0x12c50513.
Lemma F_195dc : fetch_word Plain.M.loaded_segments (0x19634 : word) = Some W_195dc.
Proof. vm_refl. Qed.
Lemma D_195dc : decode_any W_195dc = Some (OpImm ALU_ADD 10 10 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195e0 : bv 32 := 0x70f58593.
Lemma F_195e0 : fetch_word Plain.M.loaded_segments (0x19638 : word) = Some W_195e0.
Proof. vm_refl. Qed.
Lemma D_195e0 : decode_any W_195e0 = Some (OpImm ALU_ADD 11 11 1807, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195e4 : bv 32 := 0x00000613.
Lemma F_195e4 : fetch_word Plain.M.loaded_segments (0x1963c : word) = Some W_195e4.
Proof. vm_refl. Qed.
Lemma D_195e4 : decode_any W_195e4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195e8 : bv 32 := 0x01813083.
Lemma F_195e8 : fetch_word Plain.M.loaded_segments (0x19640 : word) = Some W_195e8.
Proof. vm_refl. Qed.
Lemma D_195e8 : decode_any W_195e8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195ec : bv 32 := 0x01013403.
Lemma F_195ec : fetch_word Plain.M.loaded_segments (0x19644 : word) = Some W_195ec.
Proof. vm_refl. Qed.
Lemma D_195ec : decode_any W_195ec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195f0 : bv 32 := 0x00813483.
Lemma F_195f0 : fetch_word Plain.M.loaded_segments (0x19648 : word) = Some W_195f0.
Proof. vm_refl. Qed.
Lemma D_195f0 : decode_any W_195f0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195f4 : bv 32 := 0x02010113.
Lemma F_195f4 : fetch_word Plain.M.loaded_segments (0x1964c : word) = Some W_195f4.
Proof. vm_refl. Qed.
Lemma D_195f4 : decode_any W_195f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195f8 : bv 32 := 0xe24fe06f.
Lemma F_195f8 : fetch_word Plain.M.loaded_segments (0x19650 : word) = Some W_195f8.
Proof. vm_refl. Qed.
Lemma D_195f8 : decode_any W_195f8 = Some (Jal 0 2090532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19640 : bv 32 := 0x0184b503.
Lemma F_19640 : fetch_word Plain.M.loaded_segments (0x19698 : word) = Some W_19640.
Proof. vm_refl. Qed.
Lemma D_19640 : decode_any W_19640 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19644 : bv 32 := 0x00a43c23.
Lemma F_19644 : fetch_word Plain.M.loaded_segments (0x1969c : word) = Some W_19644.
Proof. vm_refl. Qed.
Lemma D_19644 : decode_any W_19644 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19648 : bv 32 := 0x00040513.
Lemma F_19648 : fetch_word Plain.M.loaded_segments (0x196a0 : word) = Some W_19648.
Proof. vm_refl. Qed.
Lemma D_19648 : decode_any W_19648 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1964c : bv 32 := 0x00048593.
Lemma F_1964c : fetch_word Plain.M.loaded_segments (0x196a4 : word) = Some W_1964c.
Proof. vm_refl. Qed.
Lemma D_1964c : decode_any W_1964c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19650 : bv 32 := 0x144000ef.
Lemma F_19650 : fetch_word Plain.M.loaded_segments (0x196a8 : word) = Some W_19650.
Proof. vm_refl. Qed.
Lemma D_19650 : decode_any W_19650 = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19654 : bv 32 := 0x0284b583.
Lemma F_19654 : fetch_word Plain.M.loaded_segments (0x196ac : word) = Some W_19654.
Proof. vm_refl. Qed.
Lemma D_19654 : decode_any W_19654 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19658 : bv 32 := 0x02840513.
Lemma F_19658 : fetch_word Plain.M.loaded_segments (0x196b0 : word) = Some W_19658.
Proof. vm_refl. Qed.
Lemma D_19658 : decode_any W_19658 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1965c : bv 32 := 0xf68fe0ef.
Lemma F_1965c : fetch_word Plain.M.loaded_segments (0x196b4 : word) = Some W_1965c.
Proof. vm_refl. Qed.
Lemma D_1965c : decode_any W_1965c = Some (Jal 1 2090856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19660 : bv 32 := 0x0204a503.
Lemma F_19660 : fetch_word Plain.M.loaded_segments (0x196b8 : word) = Some W_19660.
Proof. vm_refl. Qed.
Lemma D_19660 : decode_any W_19660 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19664 : bv 32 := 0x02a42023.
Lemma F_19664 : fetch_word Plain.M.loaded_segments (0x196bc : word) = Some W_19664.
Proof. vm_refl. Qed.
Lemma D_19664 : decode_any W_19664 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19668 : bv 32 := 0x00040513.
Lemma F_19668 : fetch_word Plain.M.loaded_segments (0x196c0 : word) = Some W_19668.
Proof. vm_refl. Qed.
Lemma D_19668 : decode_any W_19668 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1966c : bv 32 := 0x00000593.
Lemma F_1966c : fetch_word Plain.M.loaded_segments (0x196c4 : word) = Some W_1966c.
Proof. vm_refl. Qed.
Lemma D_1966c : decode_any W_1966c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19670 : bv 32 := 0x1f1010ef.
Lemma F_19670 : fetch_word Plain.M.loaded_segments (0x196c8 : word) = Some W_19670.
Proof. vm_refl. Qed.
Lemma D_19670 : decode_any W_19670 = Some (Jal 1 6640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19674 : bv 32 := 0x00040513.
Lemma F_19674 : fetch_word Plain.M.loaded_segments (0x196cc : word) = Some W_19674.
Proof. vm_refl. Qed.
Lemma D_19674 : decode_any W_19674 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19678 : bv 32 := 0x01813083.
Lemma F_19678 : fetch_word Plain.M.loaded_segments (0x196d0 : word) = Some W_19678.
Proof. vm_refl. Qed.
Lemma D_19678 : decode_any W_19678 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1967c : bv 32 := 0x01013403.
Lemma F_1967c : fetch_word Plain.M.loaded_segments (0x196d4 : word) = Some W_1967c.
Proof. vm_refl. Qed.
Lemma D_1967c : decode_any W_1967c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19680 : bv 32 := 0x00813483.
Lemma F_19680 : fetch_word Plain.M.loaded_segments (0x196d8 : word) = Some W_19680.
Proof. vm_refl. Qed.
Lemma D_19680 : decode_any W_19680 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19684 : bv 32 := 0x02010113.
Lemma F_19684 : fetch_word Plain.M.loaded_segments (0x196dc : word) = Some W_19684.
Proof. vm_refl. Qed.
Lemma D_19684 : decode_any W_19684 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19688 : bv 32 := 0x00008067.
Lemma F_19688 : fetch_word Plain.M.loaded_segments (0x196e0 : word) = Some W_19688.
Proof. vm_refl. Qed.
Lemma D_19688 : decode_any W_19688 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1968c : bv 32 := 0x00058463.
Lemma F_1968c : fetch_word Plain.M.loaded_segments (0x196e4 : word) = Some W_1968c.
Proof. vm_refl. Qed.
Lemma D_1968c : decode_any W_1968c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19690 : bv 32 := 0x0005a023.
Lemma F_19690 : fetch_word Plain.M.loaded_segments (0x196e8 : word) = Some W_19690.
Proof. vm_refl. Qed.
Lemma D_19690 : decode_any W_19690 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19694 : bv 32 := 0x00060463.
Lemma F_19694 : fetch_word Plain.M.loaded_segments (0x196ec : word) = Some W_19694.
Proof. vm_refl. Qed.
Lemma D_19694 : decode_any W_19694 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19698 : bv 32 := 0x00062023.
Lemma F_19698 : fetch_word Plain.M.loaded_segments (0x196f0 : word) = Some W_19698.
Proof. vm_refl. Qed.
Lemma D_19698 : decode_any W_19698 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1969c : bv 32 := 0x00068463.
Lemma F_1969c : fetch_word Plain.M.loaded_segments (0x196f4 : word) = Some W_1969c.
Proof. vm_refl. Qed.
Lemma D_1969c : decode_any W_1969c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a0 : bv 32 := 0x0006a023.
Lemma F_196a0 : fetch_word Plain.M.loaded_segments (0x196f8 : word) = Some W_196a0.
Proof. vm_refl. Qed.
Lemma D_196a0 : decode_any W_196a0 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a4 : bv 32 := 0x02050a63.
Lemma F_196a4 : fetch_word Plain.M.loaded_segments (0x196fc : word) = Some W_196a4.
Proof. vm_refl. Qed.
Lemma D_196a4 : decode_any W_196a4 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a8 : bv 32 := 0x00058663.
Lemma F_196a8 : fetch_word Plain.M.loaded_segments (0x19700 : word) = Some W_196a8.
Proof. vm_refl. Qed.
Lemma D_196a8 : decode_any W_196a8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196ac : bv 32 := 0x00052703.
Lemma F_196ac : fetch_word Plain.M.loaded_segments (0x19704 : word) = Some W_196ac.
Proof. vm_refl. Qed.
Lemma D_196ac : decode_any W_196ac = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b0 : bv 32 := 0x00e5a023.
Lemma F_196b0 : fetch_word Plain.M.loaded_segments (0x19708 : word) = Some W_196b0.
Proof. vm_refl. Qed.
Lemma D_196b0 : decode_any W_196b0 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b4 : bv 32 := 0x00060663.
Lemma F_196b4 : fetch_word Plain.M.loaded_segments (0x1970c : word) = Some W_196b4.
Proof. vm_refl. Qed.
Lemma D_196b4 : decode_any W_196b4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b8 : bv 32 := 0x00452583.
Lemma F_196b8 : fetch_word Plain.M.loaded_segments (0x19710 : word) = Some W_196b8.
Proof. vm_refl. Qed.
Lemma D_196b8 : decode_any W_196b8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196bc : bv 32 := 0x00b62023.
Lemma F_196bc : fetch_word Plain.M.loaded_segments (0x19714 : word) = Some W_196bc.
Proof. vm_refl. Qed.
Lemma D_196bc : decode_any W_196bc = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c0 : bv 32 := 0x00000593.
Lemma F_196c0 : fetch_word Plain.M.loaded_segments (0x19718 : word) = Some W_196c0.
Proof. vm_refl. Qed.
Lemma D_196c0 : decode_any W_196c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c4 : bv 32 := 0x00068663.
Lemma F_196c4 : fetch_word Plain.M.loaded_segments (0x1971c : word) = Some W_196c4.
Proof. vm_refl. Qed.
Lemma D_196c4 : decode_any W_196c4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c8 : bv 32 := 0x00852503.
Lemma F_196c8 : fetch_word Plain.M.loaded_segments (0x19720 : word) = Some W_196c8.
Proof. vm_refl. Qed.
Lemma D_196c8 : decode_any W_196c8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196cc : bv 32 := 0x00a6a023.
Lemma F_196cc : fetch_word Plain.M.loaded_segments (0x19724 : word) = Some W_196cc.
Proof. vm_refl. Qed.
Lemma D_196cc : decode_any W_196cc = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d0 : bv 32 := 0x00058513.
Lemma F_196d0 : fetch_word Plain.M.loaded_segments (0x19728 : word) = Some W_196d0.
Proof. vm_refl. Qed.
Lemma D_196d0 : decode_any W_196d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d4 : bv 32 := 0x00008067.
Lemma F_196d4 : fetch_word Plain.M.loaded_segments (0x1972c : word) = Some W_196d4.
Proof. vm_refl. Qed.
Lemma D_196d4 : decode_any W_196d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19794 : bv 32 := 0xfd010113.
Lemma F_19794 : fetch_word Plain.M.loaded_segments (0x197ec : word) = Some W_19794.
Proof. vm_refl. Qed.
Lemma D_19794 : decode_any W_19794 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19798 : bv 32 := 0x02113423.
Lemma F_19798 : fetch_word Plain.M.loaded_segments (0x197f0 : word) = Some W_19798.
Proof. vm_refl. Qed.
Lemma D_19798 : decode_any W_19798 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1979c : bv 32 := 0x02813023.
Lemma F_1979c : fetch_word Plain.M.loaded_segments (0x197f4 : word) = Some W_1979c.
Proof. vm_refl. Qed.
Lemma D_1979c : decode_any W_1979c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197a0 : bv 32 := 0x00913c23.
Lemma F_197a0 : fetch_word Plain.M.loaded_segments (0x197f8 : word) = Some W_197a0.
Proof. vm_refl. Qed.
Lemma D_197a0 : decode_any W_197a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197a4 : bv 32 := 0x0e058063.
Lemma F_197a4 : fetch_word Plain.M.loaded_segments (0x197fc : word) = Some W_197a4.
Proof. vm_refl. Qed.
Lemma D_197a4 : decode_any W_197a4 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197a8 : bv 32 := 0x10050263.
Lemma F_197a8 : fetch_word Plain.M.loaded_segments (0x19800 : word) = Some W_197a8.
Proof. vm_refl. Qed.
Lemma D_197a8 : decode_any W_197a8 = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197ac : bv 32 := 0x0ca58863.
Lemma F_197ac : fetch_word Plain.M.loaded_segments (0x19804 : word) = Some W_197ac.
Proof. vm_refl. Qed.
Lemma D_197ac : decode_any W_197ac = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197b0 : bv 32 := 0x0085a603.
Lemma F_197b0 : fetch_word Plain.M.loaded_segments (0x19808 : word) = Some W_197b0.
Proof. vm_refl. Qed.
Lemma D_197b0 : decode_any W_197b0 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197b4 : bv 32 := 0x00852683.
Lemma F_197b4 : fetch_word Plain.M.loaded_segments (0x1980c : word) = Some W_197b4.
Proof. vm_refl. Qed.
Lemma D_197b4 : decode_any W_197b4 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197b8 : bv 32 := 0x10d61e63.
Lemma F_197b8 : fetch_word Plain.M.loaded_segments (0x19810 : word) = Some W_197b8.
Proof. vm_refl. Qed.
Lemma D_197b8 : decode_any W_197b8 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197bc : bv 32 := 0x03053603.
Lemma F_197bc : fetch_word Plain.M.loaded_segments (0x19814 : word) = Some W_197bc.
Proof. vm_refl. Qed.
Lemma D_197bc : decode_any W_197bc = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197c0 : bv 32 := 0x00c13823.
Lemma F_197c0 : fetch_word Plain.M.loaded_segments (0x19818 : word) = Some W_197c0.
Proof. vm_refl. Qed.
Lemma D_197c0 : decode_any W_197c0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197c4 : bv 32 := 0x02060063.
Lemma F_197c4 : fetch_word Plain.M.loaded_segments (0x1981c : word) = Some W_197c4.
Proof. vm_refl. Qed.
Lemma D_197c4 : decode_any W_197c4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197e4 : bv 32 := 0x0305b403.
Lemma F_197e4 : fetch_word Plain.M.loaded_segments (0x1983c : word) = Some W_197e4.
Proof. vm_refl. Qed.
Lemma D_197e4 : decode_any W_197e4 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197e8 : bv 32 := 0x08040a63.
Lemma F_197e8 : fetch_word Plain.M.loaded_segments (0x19840 : word) = Some W_197e8.
Proof. vm_refl. Qed.
Lemma D_197e8 : decode_any W_197e8 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197ec : bv 32 := 0x00050493.
Lemma F_197ec : fetch_word Plain.M.loaded_segments (0x19844 : word) = Some W_197ec.
Proof. vm_refl. Qed.
Lemma D_197ec : decode_any W_197ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197f0 : bv 32 := 0x00c10613.
Lemma F_197f0 : fetch_word Plain.M.loaded_segments (0x19848 : word) = Some W_197f0.
Proof. vm_refl. Qed.
Lemma D_197f0 : decode_any W_197f0 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197f4 : bv 32 := 0x00040513.
Lemma F_197f4 : fetch_word Plain.M.loaded_segments (0x1984c : word) = Some W_197f4.
Proof. vm_refl. Qed.
Lemma D_197f4 : decode_any W_197f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197f8 : bv 32 := 0x00000593.
Lemma F_197f8 : fetch_word Plain.M.loaded_segments (0x19850 : word) = Some W_197f8.
Proof. vm_refl. Qed.
Lemma D_197f8 : decode_any W_197f8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_197fc : bv 32 := 0x681020ef.
Lemma F_197fc : fetch_word Plain.M.loaded_segments (0x19854 : word) = Some W_197fc.
Proof. vm_refl. Qed.
Lemma D_197fc : decode_any W_197fc = Some (Jal 1 11904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19800 : bv 32 := 0x00c12503.
Lemma F_19800 : fetch_word Plain.M.loaded_segments (0x19858 : word) = Some W_19800.
Proof. vm_refl. Qed.
Lemma D_19800 : decode_any W_19800 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19804 : bv 32 := 0x10050663.
Lemma F_19804 : fetch_word Plain.M.loaded_segments (0x1985c : word) = Some W_19804.
Proof. vm_refl. Qed.
Lemma D_19804 : decode_any W_19804 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19808 : bv 32 := 0x00040513.
Lemma F_19808 : fetch_word Plain.M.loaded_segments (0x19860 : word) = Some W_19808.
Proof. vm_refl. Qed.
Lemma D_19808 : decode_any W_19808 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1980c : bv 32 := 0x575020ef.
Lemma F_1980c : fetch_word Plain.M.loaded_segments (0x19864 : word) = Some W_1980c.
Proof. vm_refl. Qed.
Lemma D_1980c : decode_any W_1980c = Some (Jal 1 11636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19810 : bv 32 := 0x12050463.
Lemma F_19810 : fetch_word Plain.M.loaded_segments (0x19868 : word) = Some W_19810.
Proof. vm_refl. Qed.
Lemma D_19810 : decode_any W_19810 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19814 : bv 32 := 0x00048593.
Lemma F_19814 : fetch_word Plain.M.loaded_segments (0x1986c : word) = Some W_19814.
Proof. vm_refl. Qed.
Lemma D_19814 : decode_any W_19814 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19818 : bv 32 := 0x0304b603.
Lemma F_19818 : fetch_word Plain.M.loaded_segments (0x19870 : word) = Some W_19818.
Proof. vm_refl. Qed.
Lemma D_19818 : decode_any W_19818 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1981c : bv 32 := 0x00c13823.
Lemma F_1981c : fetch_word Plain.M.loaded_segments (0x19874 : word) = Some W_1981c.
Proof. vm_refl. Qed.
Lemma D_1981c : decode_any W_1981c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19820 : bv 32 := 0x00060c63.
Lemma F_19820 : fetch_word Plain.M.loaded_segments (0x19878 : word) = Some W_19820.
Proof. vm_refl. Qed.
Lemma D_19820 : decode_any W_19820 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19838 : bv 32 := 0x02a5b823.
Lemma F_19838 : fetch_word Plain.M.loaded_segments (0x19890 : word) = Some W_19838.
Proof. vm_refl. Qed.
Lemma D_19838 : decode_any W_19838 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1983c : bv 32 := 0x01010613.
Lemma F_1983c : fetch_word Plain.M.loaded_segments (0x19894 : word) = Some W_1983c.
Proof. vm_refl. Qed.
Lemma D_1983c : decode_any W_1983c = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19840 : bv 32 := 0x00000593.
Lemma F_19840 : fetch_word Plain.M.loaded_segments (0x19898 : word) = Some W_19840.
Proof. vm_refl. Qed.
Lemma D_19840 : decode_any W_19840 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19844 : bv 32 := 0x639020ef.
Lemma F_19844 : fetch_word Plain.M.loaded_segments (0x1989c : word) = Some W_19844.
Proof. vm_refl. Qed.
Lemma D_19844 : decode_any W_19844 = Some (Jal 1 11832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19848 : bv 32 := 0x01012503.
Lemma F_19848 : fetch_word Plain.M.loaded_segments (0x198a0 : word) = Some W_19848.
Proof. vm_refl. Qed.
Lemma D_19848 : decode_any W_19848 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1984c : bv 32 := 0x02051863.
Lemma F_1984c : fetch_word Plain.M.loaded_segments (0x198a4 : word) = Some W_1984c.
Proof. vm_refl. Qed.
Lemma D_1984c : decode_any W_1984c = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1987c : bv 32 := 0x00000513.
Lemma F_1987c : fetch_word Plain.M.loaded_segments (0x198d4 : word) = Some W_1987c.
Proof. vm_refl. Qed.
Lemma D_1987c : decode_any W_1987c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19880 : bv 32 := 0x0ec0006f.
Lemma F_19880 : fetch_word Plain.M.loaded_segments (0x198d8 : word) = Some W_19880.
Proof. vm_refl. Qed.
Lemma D_19880 : decode_any W_19880 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19938 : bv 32 := 0x0001f517.
Lemma F_19938 : fetch_word Plain.M.loaded_segments (0x19990 : word) = Some W_19938.
Proof. vm_refl. Qed.
Lemma D_19938 : decode_any W_19938 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1993c : bv 32 := 0xae053503.
Lemma F_1993c : fetch_word Plain.M.loaded_segments (0x19994 : word) = Some W_1993c.
Proof. vm_refl. Qed.
Lemma D_1993c : decode_any W_1993c = Some (Load SZ8 true 10 10 2784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19940 : bv 32 := 0x00052503.
Lemma F_19940 : fetch_word Plain.M.loaded_segments (0x19998 : word) = Some W_19940.
Proof. vm_refl. Qed.
Lemma D_19940 : decode_any W_19940 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19944 : bv 32 := 0x00500593.
Lemma F_19944 : fetch_word Plain.M.loaded_segments (0x1999c : word) = Some W_19944.
Proof. vm_refl. Qed.
Lemma D_19944 : decode_any W_19944 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19948 : bv 32 := 0x02a5c063.
Lemma F_19948 : fetch_word Plain.M.loaded_segments (0x199a0 : word) = Some W_19948.
Proof. vm_refl. Qed.
Lemma D_19948 : decode_any W_19948 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1994c : bv 32 := 0xffff7517.
Lemma F_1994c : fetch_word Plain.M.loaded_segments (0x199a4 : word) = Some W_1994c.
Proof. vm_refl. Qed.
Lemma D_1994c : decode_any W_1994c = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19950 : bv 32 := 0xffff7597.
Lemma F_19950 : fetch_word Plain.M.loaded_segments (0x199a8 : word) = Some W_19950.
Proof. vm_refl. Qed.
Lemma D_19950 : decode_any W_19950 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19954 : bv 32 := 0xdc250513.
Lemma F_19954 : fetch_word Plain.M.loaded_segments (0x199ac : word) = Some W_19954.
Proof. vm_refl. Qed.
Lemma D_19954 : decode_any W_19954 = Some (OpImm ALU_ADD 10 10 3522, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19958 : bv 32 := 0xf2b58593.
Lemma F_19958 : fetch_word Plain.M.loaded_segments (0x199b0 : word) = Some W_19958.
Proof. vm_refl. Qed.
Lemma D_19958 : decode_any W_19958 = Some (OpImm ALU_ADD 11 11 3883, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1995c : bv 32 := 0x00100613.
Lemma F_1995c : fetch_word Plain.M.loaded_segments (0x199b4 : word) = Some W_1995c.
Proof. vm_refl. Qed.
Lemma D_1995c : decode_any W_1995c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19960 : bv 32 := 0x9ecfe0ef.
Lemma F_19960 : fetch_word Plain.M.loaded_segments (0x199b8 : word) = Some W_19960.
Proof. vm_refl. Qed.
Lemma D_19960 : decode_any W_19960 = Some (Jal 1 2089452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19964 : bv 32 := 0x0080006f.
Lemma F_19964 : fetch_word Plain.M.loaded_segments (0x199bc : word) = Some W_19964.
Proof. vm_refl. Qed.
Lemma D_19964 : decode_any W_19964 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1996c : bv 32 := 0x02813083.
Lemma F_1996c : fetch_word Plain.M.loaded_segments (0x199c4 : word) = Some W_1996c.
Proof. vm_refl. Qed.
Lemma D_1996c : decode_any W_1996c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19970 : bv 32 := 0x02013403.
Lemma F_19970 : fetch_word Plain.M.loaded_segments (0x199c8 : word) = Some W_19970.
Proof. vm_refl. Qed.
Lemma D_19970 : decode_any W_19970 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19974 : bv 32 := 0x01813483.
Lemma F_19974 : fetch_word Plain.M.loaded_segments (0x199cc : word) = Some W_19974.
Proof. vm_refl. Qed.
Lemma D_19974 : decode_any W_19974 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19978 : bv 32 := 0x03010113.
Lemma F_19978 : fetch_word Plain.M.loaded_segments (0x199d0 : word) = Some W_19978.
Proof. vm_refl. Qed.
Lemma D_19978 : decode_any W_19978 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1997c : bv 32 := 0x00008067.
Lemma F_1997c : fetch_word Plain.M.loaded_segments (0x199d4 : word) = Some W_1997c.
Proof. vm_refl. Qed.
Lemma D_1997c : decode_any W_1997c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c44 : bv 32 := 0xfd010113.
Lemma F_19c44 : fetch_word Plain.M.loaded_segments (0x19c9c : word) = Some W_19c44.
Proof. vm_refl. Qed.
Lemma D_19c44 : decode_any W_19c44 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c48 : bv 32 := 0x02113423.
Lemma F_19c48 : fetch_word Plain.M.loaded_segments (0x19ca0 : word) = Some W_19c48.
Proof. vm_refl. Qed.
Lemma D_19c48 : decode_any W_19c48 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c4c : bv 32 := 0x02813023.
Lemma F_19c4c : fetch_word Plain.M.loaded_segments (0x19ca4 : word) = Some W_19c4c.
Proof. vm_refl. Qed.
Lemma D_19c4c : decode_any W_19c4c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c50 : bv 32 := 0x00913c23.
Lemma F_19c50 : fetch_word Plain.M.loaded_segments (0x19ca8 : word) = Some W_19c50.
Proof. vm_refl. Qed.
Lemma D_19c50 : decode_any W_19c50 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c54 : bv 32 := 0x01213823.
Lemma F_19c54 : fetch_word Plain.M.loaded_segments (0x19cac : word) = Some W_19c54.
Proof. vm_refl. Qed.
Lemma D_19c54 : decode_any W_19c54 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c58 : bv 32 := 0x01313423.
Lemma F_19c58 : fetch_word Plain.M.loaded_segments (0x19cb0 : word) = Some W_19c58.
Proof. vm_refl. Qed.
Lemma D_19c58 : decode_any W_19c58 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c5c : bv 32 := 0x00050413.
Lemma F_19c5c : fetch_word Plain.M.loaded_segments (0x19cb4 : word) = Some W_19c5c.
Proof. vm_refl. Qed.
Lemma D_19c5c : decode_any W_19c5c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c60 : bv 32 := 0x06058063.
Lemma F_19c60 : fetch_word Plain.M.loaded_segments (0x19cb8 : word) = Some W_19c60.
Proof. vm_refl. Qed.
Lemma D_19c60 : decode_any W_19c60 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c64 : bv 32 := 0x00058493.
Lemma F_19c64 : fetch_word Plain.M.loaded_segments (0x19cbc : word) = Some W_19c64.
Proof. vm_refl. Qed.
Lemma D_19c64 : decode_any W_19c64 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c68 : bv 32 := 0x18858e63.
Lemma F_19c68 : fetch_word Plain.M.loaded_segments (0x19cc0 : word) = Some W_19c68.
Proof. vm_refl. Qed.
Lemma D_19c68 : decode_any W_19c68 = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c6c : bv 32 := 0x0044a503.
Lemma F_19c6c : fetch_word Plain.M.loaded_segments (0x19cc4 : word) = Some W_19c6c.
Proof. vm_refl. Qed.
Lemma D_19c6c : decode_any W_19c6c = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c70 : bv 32 := 0x0104a583.
Lemma F_19c70 : fetch_word Plain.M.loaded_segments (0x19cc8 : word) = Some W_19c70.
Proof. vm_refl. Qed.
Lemma D_19c70 : decode_any W_19c70 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c74 : bv 32 := 0x02a58533.
Lemma F_19c74 : fetch_word Plain.M.loaded_segments (0x19ccc : word) = Some W_19c74.
Proof. vm_refl. Qed.
Lemma D_19c74 : decode_any W_19c74 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c78 : bv 32 := 0x0025191b.
Lemma F_19c78 : fetch_word Plain.M.loaded_segments (0x19cd0 : word) = Some W_19c78.
Proof. vm_refl. Qed.
Lemma D_19c78 : decode_any W_19c78 = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19c7c : bv 32 := 0x08040463.
Lemma F_19c7c : fetch_word Plain.M.loaded_segments (0x19cd4 : word) = Some W_19c7c.
Proof. vm_refl. Qed.
Lemma D_19c7c : decode_any W_19c7c = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cb8 : bv 32 := 0x00000613.
Lemma F_19cb8 : fetch_word Plain.M.loaded_segments (0x19d10 : word) = Some W_19cb8.
Proof. vm_refl. Qed.
Lemma D_19cb8 : decode_any W_19cb8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cbc : bv 32 := 0x02c0006f.
Lemma F_19cbc : fetch_word Plain.M.loaded_segments (0x19d14 : word) = Some W_19cbc.
Proof. vm_refl. Qed.
Lemma D_19cbc : decode_any W_19cbc = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19ce8 : bv 32 := 0x02813083.
Lemma F_19ce8 : fetch_word Plain.M.loaded_segments (0x19d40 : word) = Some W_19ce8.
Proof. vm_refl. Qed.
Lemma D_19ce8 : decode_any W_19ce8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cec : bv 32 := 0x02013403.
Lemma F_19cec : fetch_word Plain.M.loaded_segments (0x19d44 : word) = Some W_19cec.
Proof. vm_refl. Qed.
Lemma D_19cec : decode_any W_19cec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cf0 : bv 32 := 0x01813483.
Lemma F_19cf0 : fetch_word Plain.M.loaded_segments (0x19d48 : word) = Some W_19cf0.
Proof. vm_refl. Qed.
Lemma D_19cf0 : decode_any W_19cf0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cf4 : bv 32 := 0x01013903.
Lemma F_19cf4 : fetch_word Plain.M.loaded_segments (0x19d4c : word) = Some W_19cf4.
Proof. vm_refl. Qed.
Lemma D_19cf4 : decode_any W_19cf4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cf8 : bv 32 := 0x00813983.
Lemma F_19cf8 : fetch_word Plain.M.loaded_segments (0x19d50 : word) = Some W_19cf8.
Proof. vm_refl. Qed.
Lemma D_19cf8 : decode_any W_19cf8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19cfc : bv 32 := 0x03010113.
Lemma F_19cfc : fetch_word Plain.M.loaded_segments (0x19d54 : word) = Some W_19cfc.
Proof. vm_refl. Qed.
Lemma D_19cfc : decode_any W_19cfc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d00 : bv 32 := 0xf1dfd06f.
Lemma F_19d00 : fetch_word Plain.M.loaded_segments (0x19d58 : word) = Some W_19d00.
Proof. vm_refl. Qed.
Lemma D_19d00 : decode_any W_19d00 = Some (Jal 0 2088732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d04 : bv 32 := 0x00048513.
Lemma F_19d04 : fetch_word Plain.M.loaded_segments (0x19d5c : word) = Some W_19d04.
Proof. vm_refl. Qed.
Lemma D_19d04 : decode_any W_19d04 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d08 : bv 32 := 0x84dff0ef.
Lemma F_19d08 : fetch_word Plain.M.loaded_segments (0x19d60 : word) = Some W_19d08.
Proof. vm_refl. Qed.
Lemma D_19d08 : decode_any W_19d08 = Some (Jal 1 2095180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d0c : bv 32 := 0x04050263.
Lemma F_19d0c : fetch_word Plain.M.loaded_segments (0x19d64 : word) = Some W_19d0c.
Proof. vm_refl. Qed.
Lemma D_19d0c : decode_any W_19d0c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d10 : bv 32 := 0x00050413.
Lemma F_19d10 : fetch_word Plain.M.loaded_segments (0x19d68 : word) = Some W_19d10.
Proof. vm_refl. Qed.
Lemma D_19d10 : decode_any W_19d10 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d14 : bv 32 := 0x00456583.
Lemma F_19d14 : fetch_word Plain.M.loaded_segments (0x19d6c : word) = Some W_19d14.
Proof. vm_refl. Qed.
Lemma D_19d14 : decode_any W_19d14 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d18 : bv 32 := 0x01056603.
Lemma F_19d18 : fetch_word Plain.M.loaded_segments (0x19d70 : word) = Some W_19d18.
Proof. vm_refl. Qed.
Lemma D_19d18 : decode_any W_19d18 = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d1c : bv 32 := 0x03853503.
Lemma F_19d1c : fetch_word Plain.M.loaded_segments (0x19d74 : word) = Some W_19d1c.
Proof. vm_refl. Qed.
Lemma D_19d1c : decode_any W_19d1c = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d20 : bv 32 := 0x02b60633.
Lemma F_19d20 : fetch_word Plain.M.loaded_segments (0x19d78 : word) = Some W_19d20.
Proof. vm_refl. Qed.
Lemma D_19d20 : decode_any W_19d20 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d24 : bv 32 := 0x00261613.
Lemma F_19d24 : fetch_word Plain.M.loaded_segments (0x19d7c : word) = Some W_19d24.
Proof. vm_refl. Qed.
Lemma D_19d24 : decode_any W_19d24 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d28 : bv 32 := 0x00000593.
Lemma F_19d28 : fetch_word Plain.M.loaded_segments (0x19d80 : word) = Some W_19d28.
Proof. vm_refl. Qed.
Lemma D_19d28 : decode_any W_19d28 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d2c : bv 32 := 0x0d81d0ef.
Lemma F_19d2c : fetch_word Plain.M.loaded_segments (0x19d84 : word) = Some W_19d2c.
Proof. vm_refl. Qed.
Lemma D_19d2c : decode_any W_19d2c = Some (Jal 1 119000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d30 : bv 32 := 0x0c40006f.
Lemma F_19d30 : fetch_word Plain.M.loaded_segments (0x19d88 : word) = Some W_19d30.
Proof. vm_refl. Qed.
Lemma D_19d30 : decode_any W_19d30 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d50 : bv 32 := 0x0001e517.
Lemma F_19d50 : fetch_word Plain.M.loaded_segments (0x19da8 : word) = Some W_19d50.
Proof. vm_refl. Qed.
Lemma D_19d50 : decode_any W_19d50 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d54 : bv 32 := 0x6c853983.
Lemma F_19d54 : fetch_word Plain.M.loaded_segments (0x19dac : word) = Some W_19d54.
Proof. vm_refl. Qed.
Lemma D_19d54 : decode_any W_19d54 = Some (Load SZ8 true 19 10 1736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d58 : bv 32 := 0x0009a503.
Lemma F_19d58 : fetch_word Plain.M.loaded_segments (0x19db0 : word) = Some W_19d58.
Proof. vm_refl. Qed.
Lemma D_19d58 : decode_any W_19d58 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d5c : bv 32 := 0x00600593.
Lemma F_19d5c : fetch_word Plain.M.loaded_segments (0x19db4 : word) = Some W_19d5c.
Proof. vm_refl. Qed.
Lemma D_19d5c : decode_any W_19d5c = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d60 : bv 32 := 0x04b55263.
Lemma F_19d60 : fetch_word Plain.M.loaded_segments (0x19db8 : word) = Some W_19d60.
Proof. vm_refl. Qed.
Lemma D_19d60 : decode_any W_19d60 = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d64 : bv 32 := 0xffff7517.
Lemma F_19d64 : fetch_word Plain.M.loaded_segments (0x19dbc : word) = Some W_19d64.
Proof. vm_refl. Qed.
Lemma D_19d64 : decode_any W_19d64 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d68 : bv 32 := 0xffff8597.
Lemma F_19d68 : fetch_word Plain.M.loaded_segments (0x19dc0 : word) = Some W_19d68.
Proof. vm_refl. Qed.
Lemma D_19d68 : decode_any W_19d68 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d6c : bv 32 := 0x99c50513.
Lemma F_19d6c : fetch_word Plain.M.loaded_segments (0x19dc4 : word) = Some W_19d6c.
Proof. vm_refl. Qed.
Lemma D_19d6c : decode_any W_19d6c = Some (OpImm ALU_ADD 10 10 2460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d70 : bv 32 := 0xa0a58593.
Lemma F_19d70 : fetch_word Plain.M.loaded_segments (0x19dc8 : word) = Some W_19d70.
Proof. vm_refl. Qed.
Lemma D_19d70 : decode_any W_19d70 = Some (OpImm ALU_ADD 11 11 2570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d74 : bv 32 := 0x00000613.
Lemma F_19d74 : fetch_word Plain.M.loaded_segments (0x19dcc : word) = Some W_19d74.
Proof. vm_refl. Qed.
Lemma D_19d74 : decode_any W_19d74 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d78 : bv 32 := 0xea5fd0ef.
Lemma F_19d78 : fetch_word Plain.M.loaded_segments (0x19dd0 : word) = Some W_19d78.
Proof. vm_refl. Qed.
Lemma D_19d78 : decode_any W_19d78 = Some (Jal 1 2088612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d7c : bv 32 := 0x00050413.
Lemma F_19d7c : fetch_word Plain.M.loaded_segments (0x19dd4 : word) = Some W_19d7c.
Proof. vm_refl. Qed.
Lemma D_19d7c : decode_any W_19d7c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d80 : bv 32 := 0x06051a63.
Lemma F_19d80 : fetch_word Plain.M.loaded_segments (0x19dd8 : word) = Some W_19d80.
Proof. vm_refl. Qed.
Lemma D_19d80 : decode_any W_19d80 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d84 : bv 32 := 0x0009a503.
Lemma F_19d84 : fetch_word Plain.M.loaded_segments (0x19ddc : word) = Some W_19d84.
Proof. vm_refl. Qed.
Lemma D_19d84 : decode_any W_19d84 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d88 : bv 32 := 0x00500593.
Lemma F_19d88 : fetch_word Plain.M.loaded_segments (0x19de0 : word) = Some W_19d88.
Proof. vm_refl. Qed.
Lemma D_19d88 : decode_any W_19d88 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d8c : bv 32 := 0x00a5cc63.
Lemma F_19d8c : fetch_word Plain.M.loaded_segments (0x19de4 : word) = Some W_19d8c.
Proof. vm_refl. Qed.
Lemma D_19d8c : decode_any W_19d8c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d90 : bv 32 := 0xffff7517.
Lemma F_19d90 : fetch_word Plain.M.loaded_segments (0x19de8 : word) = Some W_19d90.
Proof. vm_refl. Qed.
Lemma D_19d90 : decode_any W_19d90 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d94 : bv 32 := 0xffff8597.
Lemma F_19d94 : fetch_word Plain.M.loaded_segments (0x19dec : word) = Some W_19d94.
Proof. vm_refl. Qed.
Lemma D_19d94 : decode_any W_19d94 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d98 : bv 32 := 0x97050513.
Lemma F_19d98 : fetch_word Plain.M.loaded_segments (0x19df0 : word) = Some W_19d98.
Proof. vm_refl. Qed.
Lemma D_19d98 : decode_any W_19d98 = Some (OpImm ALU_ADD 10 10 2416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19d9c : bv 32 := 0x93158593.
Lemma F_19d9c : fetch_word Plain.M.loaded_segments (0x19df4 : word) = Some W_19d9c.
Proof. vm_refl. Qed.
Lemma D_19d9c : decode_any W_19d9c = Some (OpImm ALU_ADD 11 11 2353, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19da0 : bv 32 := 0xf19ff06f.
Lemma F_19da0 : fetch_word Plain.M.loaded_segments (0x19df8 : word) = Some W_19da0.
Proof. vm_refl. Qed.
Lemma D_19da0 : decode_any W_19da0 = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19df4 : bv 32 := 0x03843503.
Lemma F_19df4 : fetch_word Plain.M.loaded_segments (0x19e4c : word) = Some W_19df4.
Proof. vm_refl. Qed.
Lemma D_19df4 : decode_any W_19df4 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19df8 : bv 32 := 0x0384b583.
Lemma F_19df8 : fetch_word Plain.M.loaded_segments (0x19e50 : word) = Some W_19df8.
Proof. vm_refl. Qed.
Lemma D_19df8 : decode_any W_19df8 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19dfc : bv 32 := 0x00090613.
Lemma F_19dfc : fetch_word Plain.M.loaded_segments (0x19e54 : word) = Some W_19dfc.
Proof. vm_refl. Qed.
Lemma D_19dfc : decode_any W_19dfc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e00 : bv 32 := 0x4011c0ef.
Lemma F_19e00 : fetch_word Plain.M.loaded_segments (0x19e58 : word) = Some W_19e00.
Proof. vm_refl. Qed.
Lemma D_19e00 : decode_any W_19e00 = Some (Jal 1 117760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e04 : bv 32 := 0x00040513.
Lemma F_19e04 : fetch_word Plain.M.loaded_segments (0x19e5c : word) = Some W_19e04.
Proof. vm_refl. Qed.
Lemma D_19e04 : decode_any W_19e04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e08 : bv 32 := 0x02813083.
Lemma F_19e08 : fetch_word Plain.M.loaded_segments (0x19e60 : word) = Some W_19e08.
Proof. vm_refl. Qed.
Lemma D_19e08 : decode_any W_19e08 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e0c : bv 32 := 0x02013403.
Lemma F_19e0c : fetch_word Plain.M.loaded_segments (0x19e64 : word) = Some W_19e0c.
Proof. vm_refl. Qed.
Lemma D_19e0c : decode_any W_19e0c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e10 : bv 32 := 0x01813483.
Lemma F_19e10 : fetch_word Plain.M.loaded_segments (0x19e68 : word) = Some W_19e10.
Proof. vm_refl. Qed.
Lemma D_19e10 : decode_any W_19e10 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e14 : bv 32 := 0x01013903.
Lemma F_19e14 : fetch_word Plain.M.loaded_segments (0x19e6c : word) = Some W_19e14.
Proof. vm_refl. Qed.
Lemma D_19e14 : decode_any W_19e14 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e18 : bv 32 := 0x00813983.
Lemma F_19e18 : fetch_word Plain.M.loaded_segments (0x19e70 : word) = Some W_19e18.
Proof. vm_refl. Qed.
Lemma D_19e18 : decode_any W_19e18 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e1c : bv 32 := 0x03010113.
Lemma F_19e1c : fetch_word Plain.M.loaded_segments (0x19e74 : word) = Some W_19e1c.
Proof. vm_refl. Qed.
Lemma D_19e1c : decode_any W_19e1c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19e20 : bv 32 := 0x00008067.
Lemma F_19e20 : fetch_word Plain.M.loaded_segments (0x19e78 : word) = Some W_19e20.
Proof. vm_refl. Qed.
Lemma D_19e20 : decode_any W_19e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
