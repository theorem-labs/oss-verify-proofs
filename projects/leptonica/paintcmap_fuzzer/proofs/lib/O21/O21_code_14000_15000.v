(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushS21.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_14008 : bv 32 := 0x00100513.
Lemma F_14008 : fetch_word Plain.M.loaded_segments (0x1410c : word) = Some W_14008.
Proof. vm_refl. Qed.
Lemma D_14008 : decode_any W_14008 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1400c : bv 32 := 0x01400593.
Lemma F_1400c : fetch_word Plain.M.loaded_segments (0x14110 : word) = Some W_1400c.
Proof. vm_refl. Qed.
Lemma D_1400c : decode_any W_1400c = Some (OpImm ALU_ADD 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14010 : bv 32 := 0x784030ef.
Lemma F_14010 : fetch_word Plain.M.loaded_segments (0x14114 : word) = Some W_14010.
Proof. vm_refl. Qed.
Lemma D_14010 : decode_any W_14010 = Some (Jal 1 14212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14014 : bv 32 := 0x06050463.
Lemma F_14014 : fetch_word Plain.M.loaded_segments (0x14118 : word) = Some W_14014.
Proof. vm_refl. Qed.
Lemma D_14014 : decode_any W_14014 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14018 : bv 32 := 0xfff00593.
Lemma F_14018 : fetch_word Plain.M.loaded_segments (0x1411c : word) = Some W_14018.
Proof. vm_refl. Qed.
Lemma D_14018 : decode_any W_14018 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1401c : bv 32 := 0x01352023.
Lemma F_1401c : fetch_word Plain.M.loaded_segments (0x14120 : word) = Some W_1401c.
Proof. vm_refl. Qed.
Lemma D_1401c : decode_any W_1401c = Some (Store SZ4 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14020 : bv 32 := 0x01252223.
Lemma F_14020 : fetch_word Plain.M.loaded_segments (0x14124 : word) = Some W_14020.
Proof. vm_refl. Qed.
Lemma D_14020 : decode_any W_14020 = Some (Store SZ4 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14024 : bv 32 := 0x00b48463.
Lemma F_14024 : fetch_word Plain.M.loaded_segments (0x14128 : word) = Some W_14024.
Proof. vm_refl. Qed.
Lemma D_14024 : decode_any W_14024 = Some (Branch BC_EQ 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14028 : bv 32 := 0x00952423.
Lemma F_14028 : fetch_word Plain.M.loaded_segments (0x1412c : word) = Some W_14028.
Proof. vm_refl. Qed.
Lemma D_14028 : decode_any W_14028 = Some (Store SZ4 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1402c : bv 32 := 0x08b40463.
Lemma F_1402c : fetch_word Plain.M.loaded_segments (0x14130 : word) = Some W_1402c.
Proof. vm_refl. Qed.
Lemma D_1402c : decode_any W_1402c = Some (Branch BC_EQ 8 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14030 : bv 32 := 0x00852623.
Lemma F_14030 : fetch_word Plain.M.loaded_segments (0x14134 : word) = Some W_14030.
Proof. vm_refl. Qed.
Lemma D_14030 : decode_any W_14030 = Some (Store SZ4 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14034 : bv 32 := 0x0800006f.
Lemma F_14034 : fetch_word Plain.M.loaded_segments (0x14138 : word) = Some W_14034.
Proof. vm_refl. Qed.
Lemma D_14034 : decode_any W_14034 = Some (Jal 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140b4 : bv 32 := 0x0310000f.
Lemma F_140b4 : fetch_word Plain.M.loaded_segments (0x141b8 : word) = Some W_140b4.
Proof. vm_refl. Qed.
Lemma D_140b4 : decode_any W_140b4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140b8 : bv 32 := 0x00100593.
Lemma F_140b8 : fetch_word Plain.M.loaded_segments (0x141bc : word) = Some W_140b8.
Proof. vm_refl. Qed.
Lemma D_140b8 : decode_any W_140b8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140bc : bv 32 := 0x00b52823.
Lemma F_140bc : fetch_word Plain.M.loaded_segments (0x141c0 : word) = Some W_140bc.
Proof. vm_refl. Qed.
Lemma D_140bc : decode_any W_140bc = Some (Store SZ4 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140c0 : bv 32 := 0x0330000f.
Lemma F_140c0 : fetch_word Plain.M.loaded_segments (0x141c4 : word) = Some W_140c0.
Proof. vm_refl. Qed.
Lemma D_140c0 : decode_any W_140c0 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140c4 : bv 32 := 0x0580006f.
Lemma F_140c4 : fetch_word Plain.M.loaded_segments (0x141c8 : word) = Some W_140c4.
Proof. vm_refl. Qed.
Lemma D_140c4 : decode_any W_140c4 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1411c : bv 32 := 0x02813083.
Lemma F_1411c : fetch_word Plain.M.loaded_segments (0x14220 : word) = Some W_1411c.
Proof. vm_refl. Qed.
Lemma D_1411c : decode_any W_1411c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14120 : bv 32 := 0x02013403.
Lemma F_14120 : fetch_word Plain.M.loaded_segments (0x14224 : word) = Some W_14120.
Proof. vm_refl. Qed.
Lemma D_14120 : decode_any W_14120 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14124 : bv 32 := 0x01813483.
Lemma F_14124 : fetch_word Plain.M.loaded_segments (0x14228 : word) = Some W_14124.
Proof. vm_refl. Qed.
Lemma D_14124 : decode_any W_14124 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14128 : bv 32 := 0x01013903.
Lemma F_14128 : fetch_word Plain.M.loaded_segments (0x1422c : word) = Some W_14128.
Proof. vm_refl. Qed.
Lemma D_14128 : decode_any W_14128 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1412c : bv 32 := 0x00813983.
Lemma F_1412c : fetch_word Plain.M.loaded_segments (0x14230 : word) = Some W_1412c.
Proof. vm_refl. Qed.
Lemma D_1412c : decode_any W_1412c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14130 : bv 32 := 0x03010113.
Lemma F_14130 : fetch_word Plain.M.loaded_segments (0x14234 : word) = Some W_14130.
Proof. vm_refl. Qed.
Lemma D_14130 : decode_any W_14130 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14134 : bv 32 := 0x00008067.
Lemma F_14134 : fetch_word Plain.M.loaded_segments (0x14238 : word) = Some W_14134.
Proof. vm_refl. Qed.
Lemma D_14134 : decode_any W_14134 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14138 : bv 32 := 0x04050863.
Lemma F_14138 : fetch_word Plain.M.loaded_segments (0x1423c : word) = Some W_14138.
Proof. vm_refl. Qed.
Lemma D_14138 : decode_any W_14138 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1413c : bv 32 := 0x00053583.
Lemma F_1413c : fetch_word Plain.M.loaded_segments (0x14240 : word) = Some W_1413c.
Proof. vm_refl. Qed.
Lemma D_1413c : decode_any W_1413c = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14140 : bv 32 := 0x06058863.
Lemma F_14140 : fetch_word Plain.M.loaded_segments (0x14244 : word) = Some W_14140.
Proof. vm_refl. Qed.
Lemma D_14140 : decode_any W_14140 = Some (Branch BC_EQ 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14144 : bv 32 := 0x01058613.
Lemma F_14144 : fetch_word Plain.M.loaded_segments (0x14248 : word) = Some W_14144.
Proof. vm_refl. Qed.
Lemma D_14144 : decode_any W_14144 = Some (OpImm ALU_ADD 12 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14148 : bv 32 := 0xfff00693.
Lemma F_14148 : fetch_word Plain.M.loaded_segments (0x1424c : word) = Some W_14148.
Proof. vm_refl. Qed.
Lemma D_14148 : decode_any W_14148 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1414c : bv 32 := 0x06d6262f.
Lemma F_1414c : fetch_word Plain.M.loaded_segments (0x14250 : word) = Some W_1414c.
Proof. vm_refl. Qed.
Lemma D_1414c : decode_any W_1414c = Some (Amo AMO_ADD AW true true 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14150 : bv 32 := 0x00100693.
Lemma F_14150 : fetch_word Plain.M.loaded_segments (0x14254 : word) = Some W_14150.
Proof. vm_refl. Qed.
Lemma D_14150 : decode_any W_14150 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14154 : bv 32 := 0x02d61663.
Lemma F_14154 : fetch_word Plain.M.loaded_segments (0x14258 : word) = Some W_14154.
Proof. vm_refl. Qed.
Lemma D_14154 : decode_any W_14154 = Some (Branch BC_NE 12 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14158 : bv 32 := 0xff010113.
Lemma F_14158 : fetch_word Plain.M.loaded_segments (0x1425c : word) = Some W_14158.
Proof. vm_refl. Qed.
Lemma D_14158 : decode_any W_14158 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1415c : bv 32 := 0x00113423.
Lemma F_1415c : fetch_word Plain.M.loaded_segments (0x14260 : word) = Some W_1415c.
Proof. vm_refl. Qed.
Lemma D_1415c : decode_any W_1415c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14160 : bv 32 := 0x00813023.
Lemma F_14160 : fetch_word Plain.M.loaded_segments (0x14264 : word) = Some W_14160.
Proof. vm_refl. Qed.
Lemma D_14160 : decode_any W_14160 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14164 : bv 32 := 0x00050413.
Lemma F_14164 : fetch_word Plain.M.loaded_segments (0x14268 : word) = Some W_14164.
Proof. vm_refl. Qed.
Lemma D_14164 : decode_any W_14164 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14168 : bv 32 := 0x00058513.
Lemma F_14168 : fetch_word Plain.M.loaded_segments (0x1426c : word) = Some W_14168.
Proof. vm_refl. Qed.
Lemma D_14168 : decode_any W_14168 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1416c : bv 32 := 0x760030ef.
Lemma F_1416c : fetch_word Plain.M.loaded_segments (0x14270 : word) = Some W_1416c.
Proof. vm_refl. Qed.
Lemma D_1416c : decode_any W_1416c = Some (Jal 1 14176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14170 : bv 32 := 0x00040513.
Lemma F_14170 : fetch_word Plain.M.loaded_segments (0x14274 : word) = Some W_14170.
Proof. vm_refl. Qed.
Lemma D_14170 : decode_any W_14170 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14174 : bv 32 := 0x00813083.
Lemma F_14174 : fetch_word Plain.M.loaded_segments (0x14278 : word) = Some W_14174.
Proof. vm_refl. Qed.
Lemma D_14174 : decode_any W_14174 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14178 : bv 32 := 0x00013403.
Lemma F_14178 : fetch_word Plain.M.loaded_segments (0x1427c : word) = Some W_14178.
Proof. vm_refl. Qed.
Lemma D_14178 : decode_any W_14178 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1417c : bv 32 := 0x01010113.
Lemma F_1417c : fetch_word Plain.M.loaded_segments (0x14280 : word) = Some W_1417c.
Proof. vm_refl. Qed.
Lemma D_1417c : decode_any W_1417c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14180 : bv 32 := 0x00053023.
Lemma F_14180 : fetch_word Plain.M.loaded_segments (0x14284 : word) = Some W_14180.
Proof. vm_refl. Qed.
Lemma D_14180 : decode_any W_14180 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14184 : bv 32 := 0x02c0006f.
Lemma F_14184 : fetch_word Plain.M.loaded_segments (0x14288 : word) = Some W_14184.
Proof. vm_refl. Qed.
Lemma D_14184 : decode_any W_14184 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141b0 : bv 32 := 0x00008067.
Lemma F_141b0 : fetch_word Plain.M.loaded_segments (0x142b4 : word) = Some W_141b0.
Proof. vm_refl. Qed.
Lemma D_141b0 : decode_any W_141b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141b4 : bv 32 := 0x00058463.
Lemma F_141b4 : fetch_word Plain.M.loaded_segments (0x142b8 : word) = Some W_141b4.
Proof. vm_refl. Qed.
Lemma D_141b4 : decode_any W_141b4 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141b8 : bv 32 := 0x0005a023.
Lemma F_141b8 : fetch_word Plain.M.loaded_segments (0x142bc : word) = Some W_141b8.
Proof. vm_refl. Qed.
Lemma D_141b8 : decode_any W_141b8 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141bc : bv 32 := 0x00060463.
Lemma F_141bc : fetch_word Plain.M.loaded_segments (0x142c0 : word) = Some W_141bc.
Proof. vm_refl. Qed.
Lemma D_141bc : decode_any W_141bc = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141c0 : bv 32 := 0x00062023.
Lemma F_141c0 : fetch_word Plain.M.loaded_segments (0x142c4 : word) = Some W_141c0.
Proof. vm_refl. Qed.
Lemma D_141c0 : decode_any W_141c0 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141c4 : bv 32 := 0x00068463.
Lemma F_141c4 : fetch_word Plain.M.loaded_segments (0x142c8 : word) = Some W_141c4.
Proof. vm_refl. Qed.
Lemma D_141c4 : decode_any W_141c4 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141c8 : bv 32 := 0x0006a023.
Lemma F_141c8 : fetch_word Plain.M.loaded_segments (0x142cc : word) = Some W_141c8.
Proof. vm_refl. Qed.
Lemma D_141c8 : decode_any W_141c8 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141cc : bv 32 := 0x00070463.
Lemma F_141cc : fetch_word Plain.M.loaded_segments (0x142d0 : word) = Some W_141cc.
Proof. vm_refl. Qed.
Lemma D_141cc : decode_any W_141cc = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d0 : bv 32 := 0x00072023.
Lemma F_141d0 : fetch_word Plain.M.loaded_segments (0x142d4 : word) = Some W_141d0.
Proof. vm_refl. Qed.
Lemma D_141d0 : decode_any W_141d0 = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d4 : bv 32 := 0x04050063.
Lemma F_141d4 : fetch_word Plain.M.loaded_segments (0x142d8 : word) = Some W_141d4.
Proof. vm_refl. Qed.
Lemma D_141d4 : decode_any W_141d4 = Some (Branch BC_EQ 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141d8 : bv 32 := 0x00058663.
Lemma F_141d8 : fetch_word Plain.M.loaded_segments (0x142dc : word) = Some W_141d8.
Proof. vm_refl. Qed.
Lemma D_141d8 : decode_any W_141d8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141dc : bv 32 := 0x00052783.
Lemma F_141dc : fetch_word Plain.M.loaded_segments (0x142e0 : word) = Some W_141dc.
Proof. vm_refl. Qed.
Lemma D_141dc : decode_any W_141dc = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141e0 : bv 32 := 0x00f5a023.
Lemma F_141e0 : fetch_word Plain.M.loaded_segments (0x142e4 : word) = Some W_141e0.
Proof. vm_refl. Qed.
Lemma D_141e0 : decode_any W_141e0 = Some (Store SZ4 11 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141e4 : bv 32 := 0x00060663.
Lemma F_141e4 : fetch_word Plain.M.loaded_segments (0x142e8 : word) = Some W_141e4.
Proof. vm_refl. Qed.
Lemma D_141e4 : decode_any W_141e4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141e8 : bv 32 := 0x00452583.
Lemma F_141e8 : fetch_word Plain.M.loaded_segments (0x142ec : word) = Some W_141e8.
Proof. vm_refl. Qed.
Lemma D_141e8 : decode_any W_141e8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141ec : bv 32 := 0x00b62023.
Lemma F_141ec : fetch_word Plain.M.loaded_segments (0x142f0 : word) = Some W_141ec.
Proof. vm_refl. Qed.
Lemma D_141ec : decode_any W_141ec = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141f0 : bv 32 := 0x00068663.
Lemma F_141f0 : fetch_word Plain.M.loaded_segments (0x142f4 : word) = Some W_141f0.
Proof. vm_refl. Qed.
Lemma D_141f0 : decode_any W_141f0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141f4 : bv 32 := 0x00852583.
Lemma F_141f4 : fetch_word Plain.M.loaded_segments (0x142f8 : word) = Some W_141f4.
Proof. vm_refl. Qed.
Lemma D_141f4 : decode_any W_141f4 = Some (Load SZ4 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141f8 : bv 32 := 0x00b6a023.
Lemma F_141f8 : fetch_word Plain.M.loaded_segments (0x142fc : word) = Some W_141f8.
Proof. vm_refl. Qed.
Lemma D_141f8 : decode_any W_141f8 = Some (Store SZ4 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_141fc : bv 32 := 0x00000593.
Lemma F_141fc : fetch_word Plain.M.loaded_segments (0x14300 : word) = Some W_141fc.
Proof. vm_refl. Qed.
Lemma D_141fc : decode_any W_141fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14200 : bv 32 := 0x00070663.
Lemma F_14200 : fetch_word Plain.M.loaded_segments (0x14304 : word) = Some W_14200.
Proof. vm_refl. Qed.
Lemma D_14200 : decode_any W_14200 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14204 : bv 32 := 0x00c52503.
Lemma F_14204 : fetch_word Plain.M.loaded_segments (0x14308 : word) = Some W_14204.
Proof. vm_refl. Qed.
Lemma D_14204 : decode_any W_14204 = Some (Load SZ4 true 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14208 : bv 32 := 0x00a72023.
Lemma F_14208 : fetch_word Plain.M.loaded_segments (0x1430c : word) = Some W_14208.
Proof. vm_refl. Qed.
Lemma D_14208 : decode_any W_14208 = Some (Store SZ4 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1420c : bv 32 := 0x00058513.
Lemma F_1420c : fetch_word Plain.M.loaded_segments (0x14310 : word) = Some W_1420c.
Proof. vm_refl. Qed.
Lemma D_1420c : decode_any W_1420c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14210 : bv 32 := 0x00008067.
Lemma F_14210 : fetch_word Plain.M.loaded_segments (0x14314 : word) = Some W_14210.
Proof. vm_refl. Qed.
Lemma D_14210 : decode_any W_14210 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1470c : bv 32 := 0x00050663.
Lemma F_1470c : fetch_word Plain.M.loaded_segments (0x14810 : word) = Some W_1470c.
Proof. vm_refl. Qed.
Lemma D_1470c : decode_any W_1470c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14710 : bv 32 := 0x01052503.
Lemma F_14710 : fetch_word Plain.M.loaded_segments (0x14814 : word) = Some W_14710.
Proof. vm_refl. Qed.
Lemma D_14710 : decode_any W_14710 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14714 : bv 32 := 0x00008067.
Lemma F_14714 : fetch_word Plain.M.loaded_segments (0x14818 : word) = Some W_14714.
Proof. vm_refl. Qed.
Lemma D_14714 : decode_any W_14714 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1474c : bv 32 := 0xfe010113.
Lemma F_1474c : fetch_word Plain.M.loaded_segments (0x14850 : word) = Some W_1474c.
Proof. vm_refl. Qed.
Lemma D_1474c : decode_any W_1474c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14750 : bv 32 := 0x00113c23.
Lemma F_14750 : fetch_word Plain.M.loaded_segments (0x14854 : word) = Some W_14750.
Proof. vm_refl. Qed.
Lemma D_14750 : decode_any W_14750 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14754 : bv 32 := 0x00813823.
Lemma F_14754 : fetch_word Plain.M.loaded_segments (0x14858 : word) = Some W_14754.
Proof. vm_refl. Qed.
Lemma D_14754 : decode_any W_14754 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14758 : bv 32 := 0x00913423.
Lemma F_14758 : fetch_word Plain.M.loaded_segments (0x1485c : word) = Some W_14758.
Proof. vm_refl. Qed.
Lemma D_14758 : decode_any W_14758 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1475c : bv 32 := 0x06050863.
Lemma F_1475c : fetch_word Plain.M.loaded_segments (0x14860 : word) = Some W_1475c.
Proof. vm_refl. Qed.
Lemma D_1475c : decode_any W_1475c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14760 : bv 32 := 0x00053403.
Lemma F_14760 : fetch_word Plain.M.loaded_segments (0x14864 : word) = Some W_14760.
Proof. vm_refl. Qed.
Lemma D_14760 : decode_any W_14760 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14764 : bv 32 := 0x0a040063.
Lemma F_14764 : fetch_word Plain.M.loaded_segments (0x14868 : word) = Some W_14764.
Proof. vm_refl. Qed.
Lemma D_14764 : decode_any W_14764 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14804 : bv 32 := 0x01813083.
Lemma F_14804 : fetch_word Plain.M.loaded_segments (0x14908 : word) = Some W_14804.
Proof. vm_refl. Qed.
Lemma D_14804 : decode_any W_14804 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14808 : bv 32 := 0x01013403.
Lemma F_14808 : fetch_word Plain.M.loaded_segments (0x1490c : word) = Some W_14808.
Proof. vm_refl. Qed.
Lemma D_14808 : decode_any W_14808 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1480c : bv 32 := 0x00813483.
Lemma F_1480c : fetch_word Plain.M.loaded_segments (0x14910 : word) = Some W_1480c.
Proof. vm_refl. Qed.
Lemma D_1480c : decode_any W_1480c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14810 : bv 32 := 0x02010113.
Lemma F_14810 : fetch_word Plain.M.loaded_segments (0x14914 : word) = Some W_14810.
Proof. vm_refl. Qed.
Lemma D_14810 : decode_any W_14810 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14814 : bv 32 := 0x00008067.
Lemma F_14814 : fetch_word Plain.M.loaded_segments (0x14918 : word) = Some W_14814.
Proof. vm_refl. Qed.
Lemma D_14814 : decode_any W_14814 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14818 : bv 32 := 0xfe010113.
Lemma F_14818 : fetch_word Plain.M.loaded_segments (0x1491c : word) = Some W_14818.
Proof. vm_refl. Qed.
Lemma D_14818 : decode_any W_14818 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1481c : bv 32 := 0x00113c23.
Lemma F_1481c : fetch_word Plain.M.loaded_segments (0x14920 : word) = Some W_1481c.
Proof. vm_refl. Qed.
Lemma D_1481c : decode_any W_1481c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14820 : bv 32 := 0x00813823.
Lemma F_14820 : fetch_word Plain.M.loaded_segments (0x14924 : word) = Some W_14820.
Proof. vm_refl. Qed.
Lemma D_14820 : decode_any W_14820 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14824 : bv 32 := 0x00913423.
Lemma F_14824 : fetch_word Plain.M.loaded_segments (0x14928 : word) = Some W_14824.
Proof. vm_refl. Qed.
Lemma D_14824 : decode_any W_14824 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14828 : bv 32 := 0x02050a63.
Lemma F_14828 : fetch_word Plain.M.loaded_segments (0x1492c : word) = Some W_14828.
Proof. vm_refl. Qed.
Lemma D_14828 : decode_any W_14828 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1482c : bv 32 := 0x00050493.
Lemma F_1482c : fetch_word Plain.M.loaded_segments (0x14930 : word) = Some W_1482c.
Proof. vm_refl. Qed.
Lemma D_1482c : decode_any W_1482c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14830 : bv 32 := 0x00052503.
Lemma F_14830 : fetch_word Plain.M.loaded_segments (0x14934 : word) = Some W_14830.
Proof. vm_refl. Qed.
Lemma D_14830 : decode_any W_14830 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14834 : bv 32 := 0x0044a583.
Lemma F_14834 : fetch_word Plain.M.loaded_segments (0x14938 : word) = Some W_14834.
Proof. vm_refl. Qed.
Lemma D_14834 : decode_any W_14834 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14838 : bv 32 := 0x0084a603.
Lemma F_14838 : fetch_word Plain.M.loaded_segments (0x1493c : word) = Some W_14838.
Proof. vm_refl. Qed.
Lemma D_14838 : decode_any W_14838 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1483c : bv 32 := 0xa99ff0ef.
Lemma F_1483c : fetch_word Plain.M.loaded_segments (0x14940 : word) = Some W_1483c.
Proof. vm_refl. Qed.
Lemma D_1483c : decode_any W_1483c = Some (Jal 1 2095768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14840 : bv 32 := 0x04050263.
Lemma F_14840 : fetch_word Plain.M.loaded_segments (0x14944 : word) = Some W_14840.
Proof. vm_refl. Qed.
Lemma D_14840 : decode_any W_14840 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14844 : bv 32 := 0x00050413.
Lemma F_14844 : fetch_word Plain.M.loaded_segments (0x14948 : word) = Some W_14844.
Proof. vm_refl. Qed.
Lemma D_14844 : decode_any W_14844 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14848 : bv 32 := 0x08a48063.
Lemma F_14848 : fetch_word Plain.M.loaded_segments (0x1494c : word) = Some W_14848.
Proof. vm_refl. Qed.
Lemma D_14848 : decode_any W_14848 = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1484c : bv 32 := 0x00c4a503.
Lemma F_1484c : fetch_word Plain.M.loaded_segments (0x14950 : word) = Some W_1484c.
Proof. vm_refl. Qed.
Lemma D_1484c : decode_any W_1484c = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14850 : bv 32 := 0x08a05463.
Lemma F_14850 : fetch_word Plain.M.loaded_segments (0x14954 : word) = Some W_14850.
Proof. vm_refl. Qed.
Lemma D_14850 : decode_any W_14850 = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14854 : bv 32 := 0x00a42623.
Lemma F_14854 : fetch_word Plain.M.loaded_segments (0x14958 : word) = Some W_14854.
Proof. vm_refl. Qed.
Lemma D_14854 : decode_any W_14854 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14858 : bv 32 := 0x0ac0006f.
Lemma F_14858 : fetch_word Plain.M.loaded_segments (0x1495c : word) = Some W_14858.
Proof. vm_refl. Qed.
Lemma D_14858 : decode_any W_14858 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14884 : bv 32 := 0x0000c517.
Lemma F_14884 : fetch_word Plain.M.loaded_segments (0x14988 : word) = Some W_14884.
Proof. vm_refl. Qed.
Lemma D_14884 : decode_any W_14884 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14888 : bv 32 := 0xb9853503.
Lemma F_14888 : fetch_word Plain.M.loaded_segments (0x1498c : word) = Some W_14888.
Proof. vm_refl. Qed.
Lemma D_14888 : decode_any W_14888 = Some (Load SZ8 true 10 10 2968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1488c : bv 32 := 0x00052503.
Lemma F_1488c : fetch_word Plain.M.loaded_segments (0x14990 : word) = Some W_1488c.
Proof. vm_refl. Qed.
Lemma D_1488c : decode_any W_1488c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14890 : bv 32 := 0x00500593.
Lemma F_14890 : fetch_word Plain.M.loaded_segments (0x14994 : word) = Some W_14890.
Proof. vm_refl. Qed.
Lemma D_14890 : decode_any W_14890 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14894 : bv 32 := 0x02a5c663.
Lemma F_14894 : fetch_word Plain.M.loaded_segments (0x14998 : word) = Some W_14894.
Proof. vm_refl. Qed.
Lemma D_14894 : decode_any W_14894 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14898 : bv 32 := 0xffffc517.
Lemma F_14898 : fetch_word Plain.M.loaded_segments (0x1499c : word) = Some W_14898.
Proof. vm_refl. Qed.
Lemma D_14898 : decode_any W_14898 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1489c : bv 32 := 0xffffc597.
Lemma F_1489c : fetch_word Plain.M.loaded_segments (0x149a0 : word) = Some W_1489c.
Proof. vm_refl. Qed.
Lemma D_1489c : decode_any W_1489c = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148a0 : bv 32 := 0xaa950513.
Lemma F_148a0 : fetch_word Plain.M.loaded_segments (0x149a4 : word) = Some W_148a0.
Proof. vm_refl. Qed.
Lemma D_148a0 : decode_any W_148a0 = Some (OpImm ALU_ADD 10 10 2729, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148a4 : bv 32 := 0x18658593.
Lemma F_148a4 : fetch_word Plain.M.loaded_segments (0x149a8 : word) = Some W_148a4.
Proof. vm_refl. Qed.
Lemma D_148a4 : decode_any W_148a4 = Some (OpImm ALU_ADD 11 11 390, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148a8 : bv 32 := 0x00000613.
Lemma F_148a8 : fetch_word Plain.M.loaded_segments (0x149ac : word) = Some W_148a8.
Proof. vm_refl. Qed.
Lemma D_148a8 : decode_any W_148a8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148ac : bv 32 := 0x01813083.
Lemma F_148ac : fetch_word Plain.M.loaded_segments (0x149b0 : word) = Some W_148ac.
Proof. vm_refl. Qed.
Lemma D_148ac : decode_any W_148ac = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148b0 : bv 32 := 0x01013403.
Lemma F_148b0 : fetch_word Plain.M.loaded_segments (0x149b4 : word) = Some W_148b0.
Proof. vm_refl. Qed.
Lemma D_148b0 : decode_any W_148b0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148b4 : bv 32 := 0x00813483.
Lemma F_148b4 : fetch_word Plain.M.loaded_segments (0x149b8 : word) = Some W_148b4.
Proof. vm_refl. Qed.
Lemma D_148b4 : decode_any W_148b4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148b8 : bv 32 := 0x02010113.
Lemma F_148b8 : fetch_word Plain.M.loaded_segments (0x149bc : word) = Some W_148b8.
Proof. vm_refl. Qed.
Lemma D_148b8 : decode_any W_148b8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148bc : bv 32 := 0xcc4ff06f.
Lemma F_148bc : fetch_word Plain.M.loaded_segments (0x149c0 : word) = Some W_148bc.
Proof. vm_refl. Qed.
Lemma D_148bc : decode_any W_148bc = Some (Jal 0 2094276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14904 : bv 32 := 0x0184b503.
Lemma F_14904 : fetch_word Plain.M.loaded_segments (0x14a08 : word) = Some W_14904.
Proof. vm_refl. Qed.
Lemma D_14904 : decode_any W_14904 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14908 : bv 32 := 0x00a43c23.
Lemma F_14908 : fetch_word Plain.M.loaded_segments (0x14a0c : word) = Some W_14908.
Proof. vm_refl. Qed.
Lemma D_14908 : decode_any W_14908 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1490c : bv 32 := 0x00040513.
Lemma F_1490c : fetch_word Plain.M.loaded_segments (0x14a10 : word) = Some W_1490c.
Proof. vm_refl. Qed.
Lemma D_1490c : decode_any W_1490c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14910 : bv 32 := 0x00048593.
Lemma F_14910 : fetch_word Plain.M.loaded_segments (0x14a14 : word) = Some W_14910.
Proof. vm_refl. Qed.
Lemma D_14910 : decode_any W_14910 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14914 : bv 32 := 0x0bc000ef.
Lemma F_14914 : fetch_word Plain.M.loaded_segments (0x14a18 : word) = Some W_14914.
Proof. vm_refl. Qed.
Lemma D_14914 : decode_any W_14914 = Some (Jal 1 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14918 : bv 32 := 0x0284b583.
Lemma F_14918 : fetch_word Plain.M.loaded_segments (0x14a1c : word) = Some W_14918.
Proof. vm_refl. Qed.
Lemma D_14918 : decode_any W_14918 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1491c : bv 32 := 0x02840513.
Lemma F_1491c : fetch_word Plain.M.loaded_segments (0x14a20 : word) = Some W_1491c.
Proof. vm_refl. Qed.
Lemma D_1491c : decode_any W_1491c = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14920 : bv 32 := 0xe08ff0ef.
Lemma F_14920 : fetch_word Plain.M.loaded_segments (0x14a24 : word) = Some W_14920.
Proof. vm_refl. Qed.
Lemma D_14920 : decode_any W_14920 = Some (Jal 1 2094600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14924 : bv 32 := 0x0204a503.
Lemma F_14924 : fetch_word Plain.M.loaded_segments (0x14a28 : word) = Some W_14924.
Proof. vm_refl. Qed.
Lemma D_14924 : decode_any W_14924 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14928 : bv 32 := 0x02a42023.
Lemma F_14928 : fetch_word Plain.M.loaded_segments (0x14a2c : word) = Some W_14928.
Proof. vm_refl. Qed.
Lemma D_14928 : decode_any W_14928 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1492c : bv 32 := 0x00040513.
Lemma F_1492c : fetch_word Plain.M.loaded_segments (0x14a30 : word) = Some W_1492c.
Proof. vm_refl. Qed.
Lemma D_1492c : decode_any W_1492c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14930 : bv 32 := 0x00000593.
Lemma F_14930 : fetch_word Plain.M.loaded_segments (0x14a34 : word) = Some W_14930.
Proof. vm_refl. Qed.
Lemma D_14930 : decode_any W_14930 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14934 : bv 32 := 0x0f9000ef.
Lemma F_14934 : fetch_word Plain.M.loaded_segments (0x14a38 : word) = Some W_14934.
Proof. vm_refl. Qed.
Lemma D_14934 : decode_any W_14934 = Some (Jal 1 2296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14938 : bv 32 := 0x00040513.
Lemma F_14938 : fetch_word Plain.M.loaded_segments (0x14a3c : word) = Some W_14938.
Proof. vm_refl. Qed.
Lemma D_14938 : decode_any W_14938 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493c : bv 32 := 0x01813083.
Lemma F_1493c : fetch_word Plain.M.loaded_segments (0x14a40 : word) = Some W_1493c.
Proof. vm_refl. Qed.
Lemma D_1493c : decode_any W_1493c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14940 : bv 32 := 0x01013403.
Lemma F_14940 : fetch_word Plain.M.loaded_segments (0x14a44 : word) = Some W_14940.
Proof. vm_refl. Qed.
Lemma D_14940 : decode_any W_14940 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14944 : bv 32 := 0x00813483.
Lemma F_14944 : fetch_word Plain.M.loaded_segments (0x14a48 : word) = Some W_14944.
Proof. vm_refl. Qed.
Lemma D_14944 : decode_any W_14944 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14948 : bv 32 := 0x02010113.
Lemma F_14948 : fetch_word Plain.M.loaded_segments (0x14a4c : word) = Some W_14948.
Proof. vm_refl. Qed.
Lemma D_14948 : decode_any W_14948 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1494c : bv 32 := 0x00008067.
Lemma F_1494c : fetch_word Plain.M.loaded_segments (0x14a50 : word) = Some W_1494c.
Proof. vm_refl. Qed.
Lemma D_1494c : decode_any W_1494c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14950 : bv 32 := 0x00058463.
Lemma F_14950 : fetch_word Plain.M.loaded_segments (0x14a54 : word) = Some W_14950.
Proof. vm_refl. Qed.
Lemma D_14950 : decode_any W_14950 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14954 : bv 32 := 0x0005a023.
Lemma F_14954 : fetch_word Plain.M.loaded_segments (0x14a58 : word) = Some W_14954.
Proof. vm_refl. Qed.
Lemma D_14954 : decode_any W_14954 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14958 : bv 32 := 0x00060463.
Lemma F_14958 : fetch_word Plain.M.loaded_segments (0x14a5c : word) = Some W_14958.
Proof. vm_refl. Qed.
Lemma D_14958 : decode_any W_14958 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1495c : bv 32 := 0x00062023.
Lemma F_1495c : fetch_word Plain.M.loaded_segments (0x14a60 : word) = Some W_1495c.
Proof. vm_refl. Qed.
Lemma D_1495c : decode_any W_1495c = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14960 : bv 32 := 0x00068463.
Lemma F_14960 : fetch_word Plain.M.loaded_segments (0x14a64 : word) = Some W_14960.
Proof. vm_refl. Qed.
Lemma D_14960 : decode_any W_14960 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14964 : bv 32 := 0x0006a023.
Lemma F_14964 : fetch_word Plain.M.loaded_segments (0x14a68 : word) = Some W_14964.
Proof. vm_refl. Qed.
Lemma D_14964 : decode_any W_14964 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14968 : bv 32 := 0x02050a63.
Lemma F_14968 : fetch_word Plain.M.loaded_segments (0x14a6c : word) = Some W_14968.
Proof. vm_refl. Qed.
Lemma D_14968 : decode_any W_14968 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1496c : bv 32 := 0x00058663.
Lemma F_1496c : fetch_word Plain.M.loaded_segments (0x14a70 : word) = Some W_1496c.
Proof. vm_refl. Qed.
Lemma D_1496c : decode_any W_1496c = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14970 : bv 32 := 0x00052703.
Lemma F_14970 : fetch_word Plain.M.loaded_segments (0x14a74 : word) = Some W_14970.
Proof. vm_refl. Qed.
Lemma D_14970 : decode_any W_14970 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14974 : bv 32 := 0x00e5a023.
Lemma F_14974 : fetch_word Plain.M.loaded_segments (0x14a78 : word) = Some W_14974.
Proof. vm_refl. Qed.
Lemma D_14974 : decode_any W_14974 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14978 : bv 32 := 0x00060663.
Lemma F_14978 : fetch_word Plain.M.loaded_segments (0x14a7c : word) = Some W_14978.
Proof. vm_refl. Qed.
Lemma D_14978 : decode_any W_14978 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1497c : bv 32 := 0x00452583.
Lemma F_1497c : fetch_word Plain.M.loaded_segments (0x14a80 : word) = Some W_1497c.
Proof. vm_refl. Qed.
Lemma D_1497c : decode_any W_1497c = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14980 : bv 32 := 0x00b62023.
Lemma F_14980 : fetch_word Plain.M.loaded_segments (0x14a84 : word) = Some W_14980.
Proof. vm_refl. Qed.
Lemma D_14980 : decode_any W_14980 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14984 : bv 32 := 0x00000593.
Lemma F_14984 : fetch_word Plain.M.loaded_segments (0x14a88 : word) = Some W_14984.
Proof. vm_refl. Qed.
Lemma D_14984 : decode_any W_14984 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14988 : bv 32 := 0x00068663.
Lemma F_14988 : fetch_word Plain.M.loaded_segments (0x14a8c : word) = Some W_14988.
Proof. vm_refl. Qed.
Lemma D_14988 : decode_any W_14988 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1498c : bv 32 := 0x00852503.
Lemma F_1498c : fetch_word Plain.M.loaded_segments (0x14a90 : word) = Some W_1498c.
Proof. vm_refl. Qed.
Lemma D_1498c : decode_any W_1498c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14990 : bv 32 := 0x00a6a023.
Lemma F_14990 : fetch_word Plain.M.loaded_segments (0x14a94 : word) = Some W_14990.
Proof. vm_refl. Qed.
Lemma D_14990 : decode_any W_14990 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14994 : bv 32 := 0x00058513.
Lemma F_14994 : fetch_word Plain.M.loaded_segments (0x14a98 : word) = Some W_14994.
Proof. vm_refl. Qed.
Lemma D_14994 : decode_any W_14994 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14998 : bv 32 := 0x00008067.
Lemma F_14998 : fetch_word Plain.M.loaded_segments (0x14a9c : word) = Some W_14998.
Proof. vm_refl. Qed.
Lemma D_14998 : decode_any W_14998 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149d0 : bv 32 := 0xfd010113.
Lemma F_149d0 : fetch_word Plain.M.loaded_segments (0x14ad4 : word) = Some W_149d0.
Proof. vm_refl. Qed.
Lemma D_149d0 : decode_any W_149d0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149d4 : bv 32 := 0x02113423.
Lemma F_149d4 : fetch_word Plain.M.loaded_segments (0x14ad8 : word) = Some W_149d4.
Proof. vm_refl. Qed.
Lemma D_149d4 : decode_any W_149d4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149d8 : bv 32 := 0x02813023.
Lemma F_149d8 : fetch_word Plain.M.loaded_segments (0x14adc : word) = Some W_149d8.
Proof. vm_refl. Qed.
Lemma D_149d8 : decode_any W_149d8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149dc : bv 32 := 0x00913c23.
Lemma F_149dc : fetch_word Plain.M.loaded_segments (0x14ae0 : word) = Some W_149dc.
Proof. vm_refl. Qed.
Lemma D_149dc : decode_any W_149dc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149e0 : bv 32 := 0x0e058063.
Lemma F_149e0 : fetch_word Plain.M.loaded_segments (0x14ae4 : word) = Some W_149e0.
Proof. vm_refl. Qed.
Lemma D_149e0 : decode_any W_149e0 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149e4 : bv 32 := 0x10050263.
Lemma F_149e4 : fetch_word Plain.M.loaded_segments (0x14ae8 : word) = Some W_149e4.
Proof. vm_refl. Qed.
Lemma D_149e4 : decode_any W_149e4 = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149e8 : bv 32 := 0x0ca58863.
Lemma F_149e8 : fetch_word Plain.M.loaded_segments (0x14aec : word) = Some W_149e8.
Proof. vm_refl. Qed.
Lemma D_149e8 : decode_any W_149e8 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ec : bv 32 := 0x0085a603.
Lemma F_149ec : fetch_word Plain.M.loaded_segments (0x14af0 : word) = Some W_149ec.
Proof. vm_refl. Qed.
Lemma D_149ec : decode_any W_149ec = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149f0 : bv 32 := 0x00852683.
Lemma F_149f0 : fetch_word Plain.M.loaded_segments (0x14af4 : word) = Some W_149f0.
Proof. vm_refl. Qed.
Lemma D_149f0 : decode_any W_149f0 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149f4 : bv 32 := 0x10d61e63.
Lemma F_149f4 : fetch_word Plain.M.loaded_segments (0x14af8 : word) = Some W_149f4.
Proof. vm_refl. Qed.
Lemma D_149f4 : decode_any W_149f4 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149f8 : bv 32 := 0x03053603.
Lemma F_149f8 : fetch_word Plain.M.loaded_segments (0x14afc : word) = Some W_149f8.
Proof. vm_refl. Qed.
Lemma D_149f8 : decode_any W_149f8 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149fc : bv 32 := 0x00c13823.
Lemma F_149fc : fetch_word Plain.M.loaded_segments (0x14b00 : word) = Some W_149fc.
Proof. vm_refl. Qed.
Lemma D_149fc : decode_any W_149fc = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a00 : bv 32 := 0x02060063.
Lemma F_14a00 : fetch_word Plain.M.loaded_segments (0x14b04 : word) = Some W_14a00.
Proof. vm_refl. Qed.
Lemma D_14a00 : decode_any W_14a00 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a20 : bv 32 := 0x0305b403.
Lemma F_14a20 : fetch_word Plain.M.loaded_segments (0x14b24 : word) = Some W_14a20.
Proof. vm_refl. Qed.
Lemma D_14a20 : decode_any W_14a20 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a24 : bv 32 := 0x08040a63.
Lemma F_14a24 : fetch_word Plain.M.loaded_segments (0x14b28 : word) = Some W_14a24.
Proof. vm_refl. Qed.
Lemma D_14a24 : decode_any W_14a24 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a28 : bv 32 := 0x00050493.
Lemma F_14a28 : fetch_word Plain.M.loaded_segments (0x14b2c : word) = Some W_14a28.
Proof. vm_refl. Qed.
Lemma D_14a28 : decode_any W_14a28 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a2c : bv 32 := 0x00c10613.
Lemma F_14a2c : fetch_word Plain.M.loaded_segments (0x14b30 : word) = Some W_14a2c.
Proof. vm_refl. Qed.
Lemma D_14a2c : decode_any W_14a2c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a30 : bv 32 := 0x00040513.
Lemma F_14a30 : fetch_word Plain.M.loaded_segments (0x14b34 : word) = Some W_14a30.
Proof. vm_refl. Qed.
Lemma D_14a30 : decode_any W_14a30 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a34 : bv 32 := 0x00000593.
Lemma F_14a34 : fetch_word Plain.M.loaded_segments (0x14b38 : word) = Some W_14a34.
Proof. vm_refl. Qed.
Lemma D_14a34 : decode_any W_14a34 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a38 : bv 32 := 0x311000ef.
Lemma F_14a38 : fetch_word Plain.M.loaded_segments (0x14b3c : word) = Some W_14a38.
Proof. vm_refl. Qed.
Lemma D_14a38 : decode_any W_14a38 = Some (Jal 1 2832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a3c : bv 32 := 0x00c12503.
Lemma F_14a3c : fetch_word Plain.M.loaded_segments (0x14b40 : word) = Some W_14a3c.
Proof. vm_refl. Qed.
Lemma D_14a3c : decode_any W_14a3c = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a40 : bv 32 := 0x10050663.
Lemma F_14a40 : fetch_word Plain.M.loaded_segments (0x14b44 : word) = Some W_14a40.
Proof. vm_refl. Qed.
Lemma D_14a40 : decode_any W_14a40 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a44 : bv 32 := 0x00040513.
Lemma F_14a44 : fetch_word Plain.M.loaded_segments (0x14b48 : word) = Some W_14a44.
Proof. vm_refl. Qed.
Lemma D_14a44 : decode_any W_14a44 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a48 : bv 32 := 0x205000ef.
Lemma F_14a48 : fetch_word Plain.M.loaded_segments (0x14b4c : word) = Some W_14a48.
Proof. vm_refl. Qed.
Lemma D_14a48 : decode_any W_14a48 = Some (Jal 1 2564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a4c : bv 32 := 0x12050463.
Lemma F_14a4c : fetch_word Plain.M.loaded_segments (0x14b50 : word) = Some W_14a4c.
Proof. vm_refl. Qed.
Lemma D_14a4c : decode_any W_14a4c = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a50 : bv 32 := 0x00048593.
Lemma F_14a50 : fetch_word Plain.M.loaded_segments (0x14b54 : word) = Some W_14a50.
Proof. vm_refl. Qed.
Lemma D_14a50 : decode_any W_14a50 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a54 : bv 32 := 0x0304b603.
Lemma F_14a54 : fetch_word Plain.M.loaded_segments (0x14b58 : word) = Some W_14a54.
Proof. vm_refl. Qed.
Lemma D_14a54 : decode_any W_14a54 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a58 : bv 32 := 0x00c13823.
Lemma F_14a58 : fetch_word Plain.M.loaded_segments (0x14b5c : word) = Some W_14a58.
Proof. vm_refl. Qed.
Lemma D_14a58 : decode_any W_14a58 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a5c : bv 32 := 0x00060c63.
Lemma F_14a5c : fetch_word Plain.M.loaded_segments (0x14b60 : word) = Some W_14a5c.
Proof. vm_refl. Qed.
Lemma D_14a5c : decode_any W_14a5c = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a74 : bv 32 := 0x02a5b823.
Lemma F_14a74 : fetch_word Plain.M.loaded_segments (0x14b78 : word) = Some W_14a74.
Proof. vm_refl. Qed.
Lemma D_14a74 : decode_any W_14a74 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a78 : bv 32 := 0x01010613.
Lemma F_14a78 : fetch_word Plain.M.loaded_segments (0x14b7c : word) = Some W_14a78.
Proof. vm_refl. Qed.
Lemma D_14a78 : decode_any W_14a78 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a7c : bv 32 := 0x00000593.
Lemma F_14a7c : fetch_word Plain.M.loaded_segments (0x14b80 : word) = Some W_14a7c.
Proof. vm_refl. Qed.
Lemma D_14a7c : decode_any W_14a7c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a80 : bv 32 := 0x2c9000ef.
Lemma F_14a80 : fetch_word Plain.M.loaded_segments (0x14b84 : word) = Some W_14a80.
Proof. vm_refl. Qed.
Lemma D_14a80 : decode_any W_14a80 = Some (Jal 1 2760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a84 : bv 32 := 0x01012503.
Lemma F_14a84 : fetch_word Plain.M.loaded_segments (0x14b88 : word) = Some W_14a84.
Proof. vm_refl. Qed.
Lemma D_14a84 : decode_any W_14a84 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a88 : bv 32 := 0x02051863.
Lemma F_14a88 : fetch_word Plain.M.loaded_segments (0x14b8c : word) = Some W_14a88.
Proof. vm_refl. Qed.
Lemma D_14a88 : decode_any W_14a88 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ab8 : bv 32 := 0x00000513.
Lemma F_14ab8 : fetch_word Plain.M.loaded_segments (0x14bbc : word) = Some W_14ab8.
Proof. vm_refl. Qed.
Lemma D_14ab8 : decode_any W_14ab8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14abc : bv 32 := 0x0ec0006f.
Lemma F_14abc : fetch_word Plain.M.loaded_segments (0x14bc0 : word) = Some W_14abc.
Proof. vm_refl. Qed.
Lemma D_14abc : decode_any W_14abc = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b74 : bv 32 := 0x0000c517.
Lemma F_14b74 : fetch_word Plain.M.loaded_segments (0x14c78 : word) = Some W_14b74.
Proof. vm_refl. Qed.
Lemma D_14b74 : decode_any W_14b74 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b78 : bv 32 := 0x8a853503.
Lemma F_14b78 : fetch_word Plain.M.loaded_segments (0x14c7c : word) = Some W_14b78.
Proof. vm_refl. Qed.
Lemma D_14b78 : decode_any W_14b78 = Some (Load SZ8 true 10 10 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b7c : bv 32 := 0x00052503.
Lemma F_14b7c : fetch_word Plain.M.loaded_segments (0x14c80 : word) = Some W_14b7c.
Proof. vm_refl. Qed.
Lemma D_14b7c : decode_any W_14b7c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b80 : bv 32 := 0x00500593.
Lemma F_14b80 : fetch_word Plain.M.loaded_segments (0x14c84 : word) = Some W_14b80.
Proof. vm_refl. Qed.
Lemma D_14b80 : decode_any W_14b80 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b84 : bv 32 := 0x02a5c063.
Lemma F_14b84 : fetch_word Plain.M.loaded_segments (0x14c88 : word) = Some W_14b84.
Proof. vm_refl. Qed.
Lemma D_14b84 : decode_any W_14b84 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b88 : bv 32 := 0xffffb517.
Lemma F_14b88 : fetch_word Plain.M.loaded_segments (0x14c8c : word) = Some W_14b88.
Proof. vm_refl. Qed.
Lemma D_14b88 : decode_any W_14b88 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b8c : bv 32 := 0xffffc597.
Lemma F_14b8c : fetch_word Plain.M.loaded_segments (0x14c90 : word) = Some W_14b8c.
Proof. vm_refl. Qed.
Lemma D_14b8c : decode_any W_14b8c = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b90 : bv 32 := 0x7c750513.
Lemma F_14b90 : fetch_word Plain.M.loaded_segments (0x14c94 : word) = Some W_14b90.
Proof. vm_refl. Qed.
Lemma D_14b90 : decode_any W_14b90 = Some (OpImm ALU_ADD 10 10 1991, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b94 : bv 32 := 0x84358593.
Lemma F_14b94 : fetch_word Plain.M.loaded_segments (0x14c98 : word) = Some W_14b94.
Proof. vm_refl. Qed.
Lemma D_14b94 : decode_any W_14b94 = Some (OpImm ALU_ADD 11 11 2115, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b98 : bv 32 := 0x00100613.
Lemma F_14b98 : fetch_word Plain.M.loaded_segments (0x14c9c : word) = Some W_14b98.
Proof. vm_refl. Qed.
Lemma D_14b98 : decode_any W_14b98 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b9c : bv 32 := 0x914ff0ef.
Lemma F_14b9c : fetch_word Plain.M.loaded_segments (0x14ca0 : word) = Some W_14b9c.
Proof. vm_refl. Qed.
Lemma D_14b9c : decode_any W_14b9c = Some (Jal 1 2093332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ba0 : bv 32 := 0x0080006f.
Lemma F_14ba0 : fetch_word Plain.M.loaded_segments (0x14ca4 : word) = Some W_14ba0.
Proof. vm_refl. Qed.
Lemma D_14ba0 : decode_any W_14ba0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ba8 : bv 32 := 0x02813083.
Lemma F_14ba8 : fetch_word Plain.M.loaded_segments (0x14cac : word) = Some W_14ba8.
Proof. vm_refl. Qed.
Lemma D_14ba8 : decode_any W_14ba8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bac : bv 32 := 0x02013403.
Lemma F_14bac : fetch_word Plain.M.loaded_segments (0x14cb0 : word) = Some W_14bac.
Proof. vm_refl. Qed.
Lemma D_14bac : decode_any W_14bac = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bb0 : bv 32 := 0x01813483.
Lemma F_14bb0 : fetch_word Plain.M.loaded_segments (0x14cb4 : word) = Some W_14bb0.
Proof. vm_refl. Qed.
Lemma D_14bb0 : decode_any W_14bb0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bb4 : bv 32 := 0x03010113.
Lemma F_14bb4 : fetch_word Plain.M.loaded_segments (0x14cb8 : word) = Some W_14bb4.
Proof. vm_refl. Qed.
Lemma D_14bb4 : decode_any W_14bb4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bb8 : bv 32 := 0x00008067.
Lemma F_14bb8 : fetch_word Plain.M.loaded_segments (0x14cbc : word) = Some W_14bb8.
Proof. vm_refl. Qed.
Lemma D_14bb8 : decode_any W_14bb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ca0 : bv 32 := 0xfd010113.
Lemma F_14ca0 : fetch_word Plain.M.loaded_segments (0x14da4 : word) = Some W_14ca0.
Proof. vm_refl. Qed.
Lemma D_14ca0 : decode_any W_14ca0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ca4 : bv 32 := 0x02113423.
Lemma F_14ca4 : fetch_word Plain.M.loaded_segments (0x14da8 : word) = Some W_14ca4.
Proof. vm_refl. Qed.
Lemma D_14ca4 : decode_any W_14ca4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ca8 : bv 32 := 0x02813023.
Lemma F_14ca8 : fetch_word Plain.M.loaded_segments (0x14dac : word) = Some W_14ca8.
Proof. vm_refl. Qed.
Lemma D_14ca8 : decode_any W_14ca8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cac : bv 32 := 0x00913c23.
Lemma F_14cac : fetch_word Plain.M.loaded_segments (0x14db0 : word) = Some W_14cac.
Proof. vm_refl. Qed.
Lemma D_14cac : decode_any W_14cac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cb0 : bv 32 := 0x01213823.
Lemma F_14cb0 : fetch_word Plain.M.loaded_segments (0x14db4 : word) = Some W_14cb0.
Proof. vm_refl. Qed.
Lemma D_14cb0 : decode_any W_14cb0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cb4 : bv 32 := 0x01313423.
Lemma F_14cb4 : fetch_word Plain.M.loaded_segments (0x14db8 : word) = Some W_14cb4.
Proof. vm_refl. Qed.
Lemma D_14cb4 : decode_any W_14cb4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cb8 : bv 32 := 0x00050413.
Lemma F_14cb8 : fetch_word Plain.M.loaded_segments (0x14dbc : word) = Some W_14cb8.
Proof. vm_refl. Qed.
Lemma D_14cb8 : decode_any W_14cb8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cbc : bv 32 := 0x06058063.
Lemma F_14cbc : fetch_word Plain.M.loaded_segments (0x14dc0 : word) = Some W_14cbc.
Proof. vm_refl. Qed.
Lemma D_14cbc : decode_any W_14cbc = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc0 : bv 32 := 0x00058493.
Lemma F_14cc0 : fetch_word Plain.M.loaded_segments (0x14dc4 : word) = Some W_14cc0.
Proof. vm_refl. Qed.
Lemma D_14cc0 : decode_any W_14cc0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc4 : bv 32 := 0x18858e63.
Lemma F_14cc4 : fetch_word Plain.M.loaded_segments (0x14dc8 : word) = Some W_14cc4.
Proof. vm_refl. Qed.
Lemma D_14cc4 : decode_any W_14cc4 = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc8 : bv 32 := 0x0044a503.
Lemma F_14cc8 : fetch_word Plain.M.loaded_segments (0x14dcc : word) = Some W_14cc8.
Proof. vm_refl. Qed.
Lemma D_14cc8 : decode_any W_14cc8 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ccc : bv 32 := 0x0104a583.
Lemma F_14ccc : fetch_word Plain.M.loaded_segments (0x14dd0 : word) = Some W_14ccc.
Proof. vm_refl. Qed.
Lemma D_14ccc : decode_any W_14ccc = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd0 : bv 32 := 0x02a58533.
Lemma F_14cd0 : fetch_word Plain.M.loaded_segments (0x14dd4 : word) = Some W_14cd0.
Proof. vm_refl. Qed.
Lemma D_14cd0 : decode_any W_14cd0 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd4 : bv 32 := 0x0025191b.
Lemma F_14cd4 : fetch_word Plain.M.loaded_segments (0x14dd8 : word) = Some W_14cd4.
Proof. vm_refl. Qed.
Lemma D_14cd4 : decode_any W_14cd4 = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd8 : bv 32 := 0x08040463.
Lemma F_14cd8 : fetch_word Plain.M.loaded_segments (0x14ddc : word) = Some W_14cd8.
Proof. vm_refl. Qed.
Lemma D_14cd8 : decode_any W_14cd8 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d14 : bv 32 := 0x00000613.
Lemma F_14d14 : fetch_word Plain.M.loaded_segments (0x14e18 : word) = Some W_14d14.
Proof. vm_refl. Qed.
Lemma D_14d14 : decode_any W_14d14 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d18 : bv 32 := 0x02c0006f.
Lemma F_14d18 : fetch_word Plain.M.loaded_segments (0x14e1c : word) = Some W_14d18.
Proof. vm_refl. Qed.
Lemma D_14d18 : decode_any W_14d18 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d44 : bv 32 := 0x02813083.
Lemma F_14d44 : fetch_word Plain.M.loaded_segments (0x14e48 : word) = Some W_14d44.
Proof. vm_refl. Qed.
Lemma D_14d44 : decode_any W_14d44 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d48 : bv 32 := 0x02013403.
Lemma F_14d48 : fetch_word Plain.M.loaded_segments (0x14e4c : word) = Some W_14d48.
Proof. vm_refl. Qed.
Lemma D_14d48 : decode_any W_14d48 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d4c : bv 32 := 0x01813483.
Lemma F_14d4c : fetch_word Plain.M.loaded_segments (0x14e50 : word) = Some W_14d4c.
Proof. vm_refl. Qed.
Lemma D_14d4c : decode_any W_14d4c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d50 : bv 32 := 0x01013903.
Lemma F_14d50 : fetch_word Plain.M.loaded_segments (0x14e54 : word) = Some W_14d50.
Proof. vm_refl. Qed.
Lemma D_14d50 : decode_any W_14d50 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d54 : bv 32 := 0x00813983.
Lemma F_14d54 : fetch_word Plain.M.loaded_segments (0x14e58 : word) = Some W_14d54.
Proof. vm_refl. Qed.
Lemma D_14d54 : decode_any W_14d54 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d58 : bv 32 := 0x03010113.
Lemma F_14d58 : fetch_word Plain.M.loaded_segments (0x14e5c : word) = Some W_14d58.
Proof. vm_refl. Qed.
Lemma D_14d58 : decode_any W_14d58 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d5c : bv 32 := 0x824ff06f.
Lemma F_14d5c : fetch_word Plain.M.loaded_segments (0x14e60 : word) = Some W_14d5c.
Proof. vm_refl. Qed.
Lemma D_14d5c : decode_any W_14d5c = Some (Jal 0 2093092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d60 : bv 32 := 0x00048513.
Lemma F_14d60 : fetch_word Plain.M.loaded_segments (0x14e64 : word) = Some W_14d60.
Proof. vm_refl. Qed.
Lemma D_14d60 : decode_any W_14d60 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d64 : bv 32 := 0xab5ff0ef.
Lemma F_14d64 : fetch_word Plain.M.loaded_segments (0x14e68 : word) = Some W_14d64.
Proof. vm_refl. Qed.
Lemma D_14d64 : decode_any W_14d64 = Some (Jal 1 2095796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d68 : bv 32 := 0x04050263.
Lemma F_14d68 : fetch_word Plain.M.loaded_segments (0x14e6c : word) = Some W_14d68.
Proof. vm_refl. Qed.
Lemma D_14d68 : decode_any W_14d68 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d6c : bv 32 := 0x00050413.
Lemma F_14d6c : fetch_word Plain.M.loaded_segments (0x14e70 : word) = Some W_14d6c.
Proof. vm_refl. Qed.
Lemma D_14d6c : decode_any W_14d6c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d70 : bv 32 := 0x00456583.
Lemma F_14d70 : fetch_word Plain.M.loaded_segments (0x14e74 : word) = Some W_14d70.
Proof. vm_refl. Qed.
Lemma D_14d70 : decode_any W_14d70 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d74 : bv 32 := 0x01056603.
Lemma F_14d74 : fetch_word Plain.M.loaded_segments (0x14e78 : word) = Some W_14d74.
Proof. vm_refl. Qed.
Lemma D_14d74 : decode_any W_14d74 = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d78 : bv 32 := 0x03853503.
Lemma F_14d78 : fetch_word Plain.M.loaded_segments (0x14e7c : word) = Some W_14d78.
Proof. vm_refl. Qed.
Lemma D_14d78 : decode_any W_14d78 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d7c : bv 32 := 0x02b60633.
Lemma F_14d7c : fetch_word Plain.M.loaded_segments (0x14e80 : word) = Some W_14d7c.
Proof. vm_refl. Qed.
Lemma D_14d7c : decode_any W_14d7c = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d80 : bv 32 := 0x00261613.
Lemma F_14d80 : fetch_word Plain.M.loaded_segments (0x14e84 : word) = Some W_14d80.
Proof. vm_refl. Qed.
Lemma D_14d80 : decode_any W_14d80 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d84 : bv 32 := 0x00000593.
Lemma F_14d84 : fetch_word Plain.M.loaded_segments (0x14e88 : word) = Some W_14d84.
Proof. vm_refl. Qed.
Lemma D_14d84 : decode_any W_14d84 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d88 : bv 32 := 0x07c0a0ef.
Lemma F_14d88 : fetch_word Plain.M.loaded_segments (0x14e8c : word) = Some W_14d88.
Proof. vm_refl. Qed.
Lemma D_14d88 : decode_any W_14d88 = Some (Jal 1 41084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d8c : bv 32 := 0x0c40006f.
Lemma F_14d8c : fetch_word Plain.M.loaded_segments (0x14e90 : word) = Some W_14d8c.
Proof. vm_refl. Qed.
Lemma D_14d8c : decode_any W_14d8c = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dac : bv 32 := 0x0000b517.
Lemma F_14dac : fetch_word Plain.M.loaded_segments (0x14eb0 : word) = Some W_14dac.
Proof. vm_refl. Qed.
Lemma D_14dac : decode_any W_14dac = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14db0 : bv 32 := 0x67053983.
Lemma F_14db0 : fetch_word Plain.M.loaded_segments (0x14eb4 : word) = Some W_14db0.
Proof. vm_refl. Qed.
Lemma D_14db0 : decode_any W_14db0 = Some (Load SZ8 true 19 10 1648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14db4 : bv 32 := 0x0009a503.
Lemma F_14db4 : fetch_word Plain.M.loaded_segments (0x14eb8 : word) = Some W_14db4.
Proof. vm_refl. Qed.
Lemma D_14db4 : decode_any W_14db4 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14db8 : bv 32 := 0x00600593.
Lemma F_14db8 : fetch_word Plain.M.loaded_segments (0x14ebc : word) = Some W_14db8.
Proof. vm_refl. Qed.
Lemma D_14db8 : decode_any W_14db8 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dbc : bv 32 := 0x04b55263.
Lemma F_14dbc : fetch_word Plain.M.loaded_segments (0x14ec0 : word) = Some W_14dbc.
Proof. vm_refl. Qed.
Lemma D_14dbc : decode_any W_14dbc = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dc0 : bv 32 := 0xffffb517.
Lemma F_14dc0 : fetch_word Plain.M.loaded_segments (0x14ec4 : word) = Some W_14dc0.
Proof. vm_refl. Qed.
Lemma D_14dc0 : decode_any W_14dc0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dc4 : bv 32 := 0xffffc597.
Lemma F_14dc4 : fetch_word Plain.M.loaded_segments (0x14ec8 : word) = Some W_14dc4.
Proof. vm_refl. Qed.
Lemma D_14dc4 : decode_any W_14dc4 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dc8 : bv 32 := 0x58150513.
Lemma F_14dc8 : fetch_word Plain.M.loaded_segments (0x14ecc : word) = Some W_14dc8.
Proof. vm_refl. Qed.
Lemma D_14dc8 : decode_any W_14dc8 = Some (OpImm ALU_ADD 10 10 1409, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dcc : bv 32 := 0xab858593.
Lemma F_14dcc : fetch_word Plain.M.loaded_segments (0x14ed0 : word) = Some W_14dcc.
Proof. vm_refl. Qed.
Lemma D_14dcc : decode_any W_14dcc = Some (OpImm ALU_ADD 11 11 2744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dd0 : bv 32 := 0x00000613.
Lemma F_14dd0 : fetch_word Plain.M.loaded_segments (0x14ed4 : word) = Some W_14dd0.
Proof. vm_refl. Qed.
Lemma D_14dd0 : decode_any W_14dd0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dd4 : bv 32 := 0xfadfe0ef.
Lemma F_14dd4 : fetch_word Plain.M.loaded_segments (0x14ed8 : word) = Some W_14dd4.
Proof. vm_refl. Qed.
Lemma D_14dd4 : decode_any W_14dd4 = Some (Jal 1 2092972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dd8 : bv 32 := 0x00050413.
Lemma F_14dd8 : fetch_word Plain.M.loaded_segments (0x14edc : word) = Some W_14dd8.
Proof. vm_refl. Qed.
Lemma D_14dd8 : decode_any W_14dd8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ddc : bv 32 := 0x06051a63.
Lemma F_14ddc : fetch_word Plain.M.loaded_segments (0x14ee0 : word) = Some W_14ddc.
Proof. vm_refl. Qed.
Lemma D_14ddc : decode_any W_14ddc = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14de0 : bv 32 := 0x0009a503.
Lemma F_14de0 : fetch_word Plain.M.loaded_segments (0x14ee4 : word) = Some W_14de0.
Proof. vm_refl. Qed.
Lemma D_14de0 : decode_any W_14de0 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14de4 : bv 32 := 0x00500593.
Lemma F_14de4 : fetch_word Plain.M.loaded_segments (0x14ee8 : word) = Some W_14de4.
Proof. vm_refl. Qed.
Lemma D_14de4 : decode_any W_14de4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14de8 : bv 32 := 0x00a5cc63.
Lemma F_14de8 : fetch_word Plain.M.loaded_segments (0x14eec : word) = Some W_14de8.
Proof. vm_refl. Qed.
Lemma D_14de8 : decode_any W_14de8 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dec : bv 32 := 0xffffb517.
Lemma F_14dec : fetch_word Plain.M.loaded_segments (0x14ef0 : word) = Some W_14dec.
Proof. vm_refl. Qed.
Lemma D_14dec : decode_any W_14dec = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14df0 : bv 32 := 0xffffc597.
Lemma F_14df0 : fetch_word Plain.M.loaded_segments (0x14ef4 : word) = Some W_14df0.
Proof. vm_refl. Qed.
Lemma D_14df0 : decode_any W_14df0 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14df4 : bv 32 := 0x55550513.
Lemma F_14df4 : fetch_word Plain.M.loaded_segments (0x14ef8 : word) = Some W_14df4.
Proof. vm_refl. Qed.
Lemma D_14df4 : decode_any W_14df4 = Some (OpImm ALU_ADD 10 10 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14df8 : bv 32 := 0xa4f58593.
Lemma F_14df8 : fetch_word Plain.M.loaded_segments (0x14efc : word) = Some W_14df8.
Proof. vm_refl. Qed.
Lemma D_14df8 : decode_any W_14df8 = Some (OpImm ALU_ADD 11 11 2639, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dfc : bv 32 := 0xf19ff06f.
Lemma F_14dfc : fetch_word Plain.M.loaded_segments (0x14f00 : word) = Some W_14dfc.
Proof. vm_refl. Qed.
Lemma D_14dfc : decode_any W_14dfc = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e50 : bv 32 := 0x03843503.
Lemma F_14e50 : fetch_word Plain.M.loaded_segments (0x14f54 : word) = Some W_14e50.
Proof. vm_refl. Qed.
Lemma D_14e50 : decode_any W_14e50 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e54 : bv 32 := 0x0384b583.
Lemma F_14e54 : fetch_word Plain.M.loaded_segments (0x14f58 : word) = Some W_14e54.
Proof. vm_refl. Qed.
Lemma D_14e54 : decode_any W_14e54 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e58 : bv 32 := 0x00090613.
Lemma F_14e58 : fetch_word Plain.M.loaded_segments (0x14f5c : word) = Some W_14e58.
Proof. vm_refl. Qed.
Lemma D_14e58 : decode_any W_14e58 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e5c : bv 32 := 0x3a5090ef.
Lemma F_14e5c : fetch_word Plain.M.loaded_segments (0x14f60 : word) = Some W_14e5c.
Proof. vm_refl. Qed.
Lemma D_14e5c : decode_any W_14e5c = Some (Jal 1 39844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e60 : bv 32 := 0x00040513.
Lemma F_14e60 : fetch_word Plain.M.loaded_segments (0x14f64 : word) = Some W_14e60.
Proof. vm_refl. Qed.
Lemma D_14e60 : decode_any W_14e60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e64 : bv 32 := 0x02813083.
Lemma F_14e64 : fetch_word Plain.M.loaded_segments (0x14f68 : word) = Some W_14e64.
Proof. vm_refl. Qed.
Lemma D_14e64 : decode_any W_14e64 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e68 : bv 32 := 0x02013403.
Lemma F_14e68 : fetch_word Plain.M.loaded_segments (0x14f6c : word) = Some W_14e68.
Proof. vm_refl. Qed.
Lemma D_14e68 : decode_any W_14e68 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e6c : bv 32 := 0x01813483.
Lemma F_14e6c : fetch_word Plain.M.loaded_segments (0x14f70 : word) = Some W_14e6c.
Proof. vm_refl. Qed.
Lemma D_14e6c : decode_any W_14e6c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e70 : bv 32 := 0x01013903.
Lemma F_14e70 : fetch_word Plain.M.loaded_segments (0x14f74 : word) = Some W_14e70.
Proof. vm_refl. Qed.
Lemma D_14e70 : decode_any W_14e70 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e74 : bv 32 := 0x00813983.
Lemma F_14e74 : fetch_word Plain.M.loaded_segments (0x14f78 : word) = Some W_14e74.
Proof. vm_refl. Qed.
Lemma D_14e74 : decode_any W_14e74 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e78 : bv 32 := 0x03010113.
Lemma F_14e78 : fetch_word Plain.M.loaded_segments (0x14f7c : word) = Some W_14e78.
Proof. vm_refl. Qed.
Lemma D_14e78 : decode_any W_14e78 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14e7c : bv 32 := 0x00008067.
Lemma F_14e7c : fetch_word Plain.M.loaded_segments (0x14f80 : word) = Some W_14e7c.
Proof. vm_refl. Qed.
Lemma D_14e7c : decode_any W_14e7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
