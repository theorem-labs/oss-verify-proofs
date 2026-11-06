(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushS14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_160b4 : bv 32 := 0x00015517.
Lemma F_160b4 : fetch_word Plain.M.loaded_segments (0x161b0 : word) = Some W_160b4.
Proof. vm_refl. Qed.
Lemma D_160b4 : decode_any W_160b4 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160b8 : bv 32 := 0x89053503.
Lemma F_160b8 : fetch_word Plain.M.loaded_segments (0x161b4 : word) = Some W_160b8.
Proof. vm_refl. Qed.
Lemma D_160b8 : decode_any W_160b8 = Some (Load SZ8 true 10 10 2192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160bc : bv 32 := 0x00052503.
Lemma F_160bc : fetch_word Plain.M.loaded_segments (0x161b8 : word) = Some W_160bc.
Proof. vm_refl. Qed.
Lemma D_160bc : decode_any W_160bc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c0 : bv 32 := 0x00500593.
Lemma F_160c0 : fetch_word Plain.M.loaded_segments (0x161bc : word) = Some W_160c0.
Proof. vm_refl. Qed.
Lemma D_160c0 : decode_any W_160c0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c4 : bv 32 := 0x02a5c063.
Lemma F_160c4 : fetch_word Plain.M.loaded_segments (0x161c0 : word) = Some W_160c4.
Proof. vm_refl. Qed.
Lemma D_160c4 : decode_any W_160c4 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160c8 : bv 32 := 0xffffa517.
Lemma F_160c8 : fetch_word Plain.M.loaded_segments (0x161c4 : word) = Some W_160c8.
Proof. vm_refl. Qed.
Lemma D_160c8 : decode_any W_160c8 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160cc : bv 32 := 0xffffa597.
Lemma F_160cc : fetch_word Plain.M.loaded_segments (0x161c8 : word) = Some W_160cc.
Proof. vm_refl. Qed.
Lemma D_160cc : decode_any W_160cc = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d0 : bv 32 := 0x30750513.
Lemma F_160d0 : fetch_word Plain.M.loaded_segments (0x161cc : word) = Some W_160d0.
Proof. vm_refl. Qed.
Lemma D_160d0 : decode_any W_160d0 = Some (OpImm ALU_ADD 10 10 775, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d4 : bv 32 := 0x3c558593.
Lemma F_160d4 : fetch_word Plain.M.loaded_segments (0x161d0 : word) = Some W_160d4.
Proof. vm_refl. Qed.
Lemma D_160d4 : decode_any W_160d4 = Some (OpImm ALU_ADD 11 11 965, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160d8 : bv 32 := 0x00100613.
Lemma F_160d8 : fetch_word Plain.M.loaded_segments (0x161d4 : word) = Some W_160d8.
Proof. vm_refl. Qed.
Lemma D_160d8 : decode_any W_160d8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160dc : bv 32 := 0x994ff0ef.
Lemma F_160dc : fetch_word Plain.M.loaded_segments (0x161d8 : word) = Some W_160dc.
Proof. vm_refl. Qed.
Lemma D_160dc : decode_any W_160dc = Some (Jal 1 2093460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160e0 : bv 32 := 0x0080006f.
Lemma F_160e0 : fetch_word Plain.M.loaded_segments (0x161dc : word) = Some W_160e0.
Proof. vm_refl. Qed.
Lemma D_160e0 : decode_any W_160e0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160e8 : bv 32 := 0x02813083.
Lemma F_160e8 : fetch_word Plain.M.loaded_segments (0x161e4 : word) = Some W_160e8.
Proof. vm_refl. Qed.
Lemma D_160e8 : decode_any W_160e8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160ec : bv 32 := 0x02013403.
Lemma F_160ec : fetch_word Plain.M.loaded_segments (0x161e8 : word) = Some W_160ec.
Proof. vm_refl. Qed.
Lemma D_160ec : decode_any W_160ec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160f0 : bv 32 := 0x01813483.
Lemma F_160f0 : fetch_word Plain.M.loaded_segments (0x161ec : word) = Some W_160f0.
Proof. vm_refl. Qed.
Lemma D_160f0 : decode_any W_160f0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160f4 : bv 32 := 0x03010113.
Lemma F_160f4 : fetch_word Plain.M.loaded_segments (0x161f0 : word) = Some W_160f4.
Proof. vm_refl. Qed.
Lemma D_160f4 : decode_any W_160f4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_160f8 : bv 32 := 0x00008067.
Lemma F_160f8 : fetch_word Plain.M.loaded_segments (0x161f4 : word) = Some W_160f8.
Proof. vm_refl. Qed.
Lemma D_160f8 : decode_any W_160f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16328 : bv 32 := 0xfd010113.
Lemma F_16328 : fetch_word Plain.M.loaded_segments (0x16424 : word) = Some W_16328.
Proof. vm_refl. Qed.
Lemma D_16328 : decode_any W_16328 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1632c : bv 32 := 0x02113423.
Lemma F_1632c : fetch_word Plain.M.loaded_segments (0x16428 : word) = Some W_1632c.
Proof. vm_refl. Qed.
Lemma D_1632c : decode_any W_1632c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16330 : bv 32 := 0x02813023.
Lemma F_16330 : fetch_word Plain.M.loaded_segments (0x1642c : word) = Some W_16330.
Proof. vm_refl. Qed.
Lemma D_16330 : decode_any W_16330 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16334 : bv 32 := 0x00913c23.
Lemma F_16334 : fetch_word Plain.M.loaded_segments (0x16430 : word) = Some W_16334.
Proof. vm_refl. Qed.
Lemma D_16334 : decode_any W_16334 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16338 : bv 32 := 0x01213823.
Lemma F_16338 : fetch_word Plain.M.loaded_segments (0x16434 : word) = Some W_16338.
Proof. vm_refl. Qed.
Lemma D_16338 : decode_any W_16338 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1633c : bv 32 := 0x01313423.
Lemma F_1633c : fetch_word Plain.M.loaded_segments (0x16438 : word) = Some W_1633c.
Proof. vm_refl. Qed.
Lemma D_1633c : decode_any W_1633c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16340 : bv 32 := 0x00050413.
Lemma F_16340 : fetch_word Plain.M.loaded_segments (0x1643c : word) = Some W_16340.
Proof. vm_refl. Qed.
Lemma D_16340 : decode_any W_16340 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16344 : bv 32 := 0x06058063.
Lemma F_16344 : fetch_word Plain.M.loaded_segments (0x16440 : word) = Some W_16344.
Proof. vm_refl. Qed.
Lemma D_16344 : decode_any W_16344 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16348 : bv 32 := 0x00058493.
Lemma F_16348 : fetch_word Plain.M.loaded_segments (0x16444 : word) = Some W_16348.
Proof. vm_refl. Qed.
Lemma D_16348 : decode_any W_16348 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1634c : bv 32 := 0x18858e63.
Lemma F_1634c : fetch_word Plain.M.loaded_segments (0x16448 : word) = Some W_1634c.
Proof. vm_refl. Qed.
Lemma D_1634c : decode_any W_1634c = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16350 : bv 32 := 0x0044a503.
Lemma F_16350 : fetch_word Plain.M.loaded_segments (0x1644c : word) = Some W_16350.
Proof. vm_refl. Qed.
Lemma D_16350 : decode_any W_16350 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16354 : bv 32 := 0x0104a583.
Lemma F_16354 : fetch_word Plain.M.loaded_segments (0x16450 : word) = Some W_16354.
Proof. vm_refl. Qed.
Lemma D_16354 : decode_any W_16354 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16358 : bv 32 := 0x02a58533.
Lemma F_16358 : fetch_word Plain.M.loaded_segments (0x16454 : word) = Some W_16358.
Proof. vm_refl. Qed.
Lemma D_16358 : decode_any W_16358 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1635c : bv 32 := 0x0025191b.
Lemma F_1635c : fetch_word Plain.M.loaded_segments (0x16458 : word) = Some W_1635c.
Proof. vm_refl. Qed.
Lemma D_1635c : decode_any W_1635c = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16360 : bv 32 := 0x08040463.
Lemma F_16360 : fetch_word Plain.M.loaded_segments (0x1645c : word) = Some W_16360.
Proof. vm_refl. Qed.
Lemma D_16360 : decode_any W_16360 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1639c : bv 32 := 0x00000613.
Lemma F_1639c : fetch_word Plain.M.loaded_segments (0x16498 : word) = Some W_1639c.
Proof. vm_refl. Qed.
Lemma D_1639c : decode_any W_1639c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163a0 : bv 32 := 0x02c0006f.
Lemma F_163a0 : fetch_word Plain.M.loaded_segments (0x1649c : word) = Some W_163a0.
Proof. vm_refl. Qed.
Lemma D_163a0 : decode_any W_163a0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163cc : bv 32 := 0x02813083.
Lemma F_163cc : fetch_word Plain.M.loaded_segments (0x164c8 : word) = Some W_163cc.
Proof. vm_refl. Qed.
Lemma D_163cc : decode_any W_163cc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163d0 : bv 32 := 0x02013403.
Lemma F_163d0 : fetch_word Plain.M.loaded_segments (0x164cc : word) = Some W_163d0.
Proof. vm_refl. Qed.
Lemma D_163d0 : decode_any W_163d0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163d4 : bv 32 := 0x01813483.
Lemma F_163d4 : fetch_word Plain.M.loaded_segments (0x164d0 : word) = Some W_163d4.
Proof. vm_refl. Qed.
Lemma D_163d4 : decode_any W_163d4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163d8 : bv 32 := 0x01013903.
Lemma F_163d8 : fetch_word Plain.M.loaded_segments (0x164d4 : word) = Some W_163d8.
Proof. vm_refl. Qed.
Lemma D_163d8 : decode_any W_163d8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163dc : bv 32 := 0x00813983.
Lemma F_163dc : fetch_word Plain.M.loaded_segments (0x164d8 : word) = Some W_163dc.
Proof. vm_refl. Qed.
Lemma D_163dc : decode_any W_163dc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163e0 : bv 32 := 0x03010113.
Lemma F_163e0 : fetch_word Plain.M.loaded_segments (0x164dc : word) = Some W_163e0.
Proof. vm_refl. Qed.
Lemma D_163e0 : decode_any W_163e0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163e4 : bv 32 := 0xf5dfe06f.
Lemma F_163e4 : fetch_word Plain.M.loaded_segments (0x164e0 : word) = Some W_163e4.
Proof. vm_refl. Qed.
Lemma D_163e4 : decode_any W_163e4 = Some (Jal 0 2092892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163e8 : bv 32 := 0x00048513.
Lemma F_163e8 : fetch_word Plain.M.loaded_segments (0x164e4 : word) = Some W_163e8.
Proof. vm_refl. Qed.
Lemma D_163e8 : decode_any W_163e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163ec : bv 32 := 0x815ff0ef.
Lemma F_163ec : fetch_word Plain.M.loaded_segments (0x164e8 : word) = Some W_163ec.
Proof. vm_refl. Qed.
Lemma D_163ec : decode_any W_163ec = Some (Jal 1 2095124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163f0 : bv 32 := 0x04050263.
Lemma F_163f0 : fetch_word Plain.M.loaded_segments (0x164ec : word) = Some W_163f0.
Proof. vm_refl. Qed.
Lemma D_163f0 : decode_any W_163f0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163f4 : bv 32 := 0x00050413.
Lemma F_163f4 : fetch_word Plain.M.loaded_segments (0x164f0 : word) = Some W_163f4.
Proof. vm_refl. Qed.
Lemma D_163f4 : decode_any W_163f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163f8 : bv 32 := 0x00456583.
Lemma F_163f8 : fetch_word Plain.M.loaded_segments (0x164f4 : word) = Some W_163f8.
Proof. vm_refl. Qed.
Lemma D_163f8 : decode_any W_163f8 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_163fc : bv 32 := 0x01056603.
Lemma F_163fc : fetch_word Plain.M.loaded_segments (0x164f8 : word) = Some W_163fc.
Proof. vm_refl. Qed.
Lemma D_163fc : decode_any W_163fc = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16400 : bv 32 := 0x03853503.
Lemma F_16400 : fetch_word Plain.M.loaded_segments (0x164fc : word) = Some W_16400.
Proof. vm_refl. Qed.
Lemma D_16400 : decode_any W_16400 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16404 : bv 32 := 0x02b60633.
Lemma F_16404 : fetch_word Plain.M.loaded_segments (0x16500 : word) = Some W_16404.
Proof. vm_refl. Qed.
Lemma D_16404 : decode_any W_16404 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16408 : bv 32 := 0x00261613.
Lemma F_16408 : fetch_word Plain.M.loaded_segments (0x16504 : word) = Some W_16408.
Proof. vm_refl. Qed.
Lemma D_16408 : decode_any W_16408 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1640c : bv 32 := 0x00000593.
Lemma F_1640c : fetch_word Plain.M.loaded_segments (0x16508 : word) = Some W_1640c.
Proof. vm_refl. Qed.
Lemma D_1640c : decode_any W_1640c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16410 : bv 32 := 0x721120ef.
Lemma F_16410 : fetch_word Plain.M.loaded_segments (0x1650c : word) = Some W_16410.
Proof. vm_refl. Qed.
Lemma D_16410 : decode_any W_16410 = Some (Jal 1 77600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16414 : bv 32 := 0x0c40006f.
Lemma F_16414 : fetch_word Plain.M.loaded_segments (0x16510 : word) = Some W_16414.
Proof. vm_refl. Qed.
Lemma D_16414 : decode_any W_16414 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16434 : bv 32 := 0x00014517.
Lemma F_16434 : fetch_word Plain.M.loaded_segments (0x16530 : word) = Some W_16434.
Proof. vm_refl. Qed.
Lemma D_16434 : decode_any W_16434 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16438 : bv 32 := 0x51053983.
Lemma F_16438 : fetch_word Plain.M.loaded_segments (0x16534 : word) = Some W_16438.
Proof. vm_refl. Qed.
Lemma D_16438 : decode_any W_16438 = Some (Load SZ8 true 19 10 1296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1643c : bv 32 := 0x0009a503.
Lemma F_1643c : fetch_word Plain.M.loaded_segments (0x16538 : word) = Some W_1643c.
Proof. vm_refl. Qed.
Lemma D_1643c : decode_any W_1643c = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16440 : bv 32 := 0x00600593.
Lemma F_16440 : fetch_word Plain.M.loaded_segments (0x1653c : word) = Some W_16440.
Proof. vm_refl. Qed.
Lemma D_16440 : decode_any W_16440 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16444 : bv 32 := 0x04b55263.
Lemma F_16444 : fetch_word Plain.M.loaded_segments (0x16540 : word) = Some W_16444.
Proof. vm_refl. Qed.
Lemma D_16444 : decode_any W_16444 = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16448 : bv 32 := 0xffffa517.
Lemma F_16448 : fetch_word Plain.M.loaded_segments (0x16544 : word) = Some W_16448.
Proof. vm_refl. Qed.
Lemma D_16448 : decode_any W_16448 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1644c : bv 32 := 0xffffb597.
Lemma F_1644c : fetch_word Plain.M.loaded_segments (0x16548 : word) = Some W_1644c.
Proof. vm_refl. Qed.
Lemma D_1644c : decode_any W_1644c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16450 : bv 32 := 0xf7950513.
Lemma F_16450 : fetch_word Plain.M.loaded_segments (0x1654c : word) = Some W_16450.
Proof. vm_refl. Qed.
Lemma D_16450 : decode_any W_16450 = Some (OpImm ALU_ADD 10 10 3961, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16454 : bv 32 := 0x85c58593.
Lemma F_16454 : fetch_word Plain.M.loaded_segments (0x16550 : word) = Some W_16454.
Proof. vm_refl. Qed.
Lemma D_16454 : decode_any W_16454 = Some (OpImm ALU_ADD 11 11 2140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16458 : bv 32 := 0x00000613.
Lemma F_16458 : fetch_word Plain.M.loaded_segments (0x16554 : word) = Some W_16458.
Proof. vm_refl. Qed.
Lemma D_16458 : decode_any W_16458 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1645c : bv 32 := 0xee5fe0ef.
Lemma F_1645c : fetch_word Plain.M.loaded_segments (0x16558 : word) = Some W_1645c.
Proof. vm_refl. Qed.
Lemma D_1645c : decode_any W_1645c = Some (Jal 1 2092772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16460 : bv 32 := 0x00050413.
Lemma F_16460 : fetch_word Plain.M.loaded_segments (0x1655c : word) = Some W_16460.
Proof. vm_refl. Qed.
Lemma D_16460 : decode_any W_16460 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16464 : bv 32 := 0x06051a63.
Lemma F_16464 : fetch_word Plain.M.loaded_segments (0x16560 : word) = Some W_16464.
Proof. vm_refl. Qed.
Lemma D_16464 : decode_any W_16464 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16468 : bv 32 := 0x0009a503.
Lemma F_16468 : fetch_word Plain.M.loaded_segments (0x16564 : word) = Some W_16468.
Proof. vm_refl. Qed.
Lemma D_16468 : decode_any W_16468 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1646c : bv 32 := 0x00500593.
Lemma F_1646c : fetch_word Plain.M.loaded_segments (0x16568 : word) = Some W_1646c.
Proof. vm_refl. Qed.
Lemma D_1646c : decode_any W_1646c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16470 : bv 32 := 0x00a5cc63.
Lemma F_16470 : fetch_word Plain.M.loaded_segments (0x1656c : word) = Some W_16470.
Proof. vm_refl. Qed.
Lemma D_16470 : decode_any W_16470 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16474 : bv 32 := 0xffffa517.
Lemma F_16474 : fetch_word Plain.M.loaded_segments (0x16570 : word) = Some W_16474.
Proof. vm_refl. Qed.
Lemma D_16474 : decode_any W_16474 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16478 : bv 32 := 0xffffa597.
Lemma F_16478 : fetch_word Plain.M.loaded_segments (0x16574 : word) = Some W_16478.
Proof. vm_refl. Qed.
Lemma D_16478 : decode_any W_16478 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1647c : bv 32 := 0xf4d50513.
Lemma F_1647c : fetch_word Plain.M.loaded_segments (0x16578 : word) = Some W_1647c.
Proof. vm_refl. Qed.
Lemma D_1647c : decode_any W_1647c = Some (OpImm ALU_ADD 10 10 3917, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16480 : bv 32 := 0x7ed58593.
Lemma F_16480 : fetch_word Plain.M.loaded_segments (0x1657c : word) = Some W_16480.
Proof. vm_refl. Qed.
Lemma D_16480 : decode_any W_16480 = Some (OpImm ALU_ADD 11 11 2029, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16484 : bv 32 := 0xf19ff06f.
Lemma F_16484 : fetch_word Plain.M.loaded_segments (0x16580 : word) = Some W_16484.
Proof. vm_refl. Qed.
Lemma D_16484 : decode_any W_16484 = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164d8 : bv 32 := 0x03843503.
Lemma F_164d8 : fetch_word Plain.M.loaded_segments (0x165d4 : word) = Some W_164d8.
Proof. vm_refl. Qed.
Lemma D_164d8 : decode_any W_164d8 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164dc : bv 32 := 0x0384b583.
Lemma F_164dc : fetch_word Plain.M.loaded_segments (0x165d8 : word) = Some W_164dc.
Proof. vm_refl. Qed.
Lemma D_164dc : decode_any W_164dc = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164e0 : bv 32 := 0x00090613.
Lemma F_164e0 : fetch_word Plain.M.loaded_segments (0x165dc : word) = Some W_164e0.
Proof. vm_refl. Qed.
Lemma D_164e0 : decode_any W_164e0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164e4 : bv 32 := 0x249120ef.
Lemma F_164e4 : fetch_word Plain.M.loaded_segments (0x165e0 : word) = Some W_164e4.
Proof. vm_refl. Qed.
Lemma D_164e4 : decode_any W_164e4 = Some (Jal 1 76360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164e8 : bv 32 := 0x00040513.
Lemma F_164e8 : fetch_word Plain.M.loaded_segments (0x165e4 : word) = Some W_164e8.
Proof. vm_refl. Qed.
Lemma D_164e8 : decode_any W_164e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164ec : bv 32 := 0x02813083.
Lemma F_164ec : fetch_word Plain.M.loaded_segments (0x165e8 : word) = Some W_164ec.
Proof. vm_refl. Qed.
Lemma D_164ec : decode_any W_164ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164f0 : bv 32 := 0x02013403.
Lemma F_164f0 : fetch_word Plain.M.loaded_segments (0x165ec : word) = Some W_164f0.
Proof. vm_refl. Qed.
Lemma D_164f0 : decode_any W_164f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164f4 : bv 32 := 0x01813483.
Lemma F_164f4 : fetch_word Plain.M.loaded_segments (0x165f0 : word) = Some W_164f4.
Proof. vm_refl. Qed.
Lemma D_164f4 : decode_any W_164f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164f8 : bv 32 := 0x01013903.
Lemma F_164f8 : fetch_word Plain.M.loaded_segments (0x165f4 : word) = Some W_164f8.
Proof. vm_refl. Qed.
Lemma D_164f8 : decode_any W_164f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164fc : bv 32 := 0x00813983.
Lemma F_164fc : fetch_word Plain.M.loaded_segments (0x165f8 : word) = Some W_164fc.
Proof. vm_refl. Qed.
Lemma D_164fc : decode_any W_164fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16500 : bv 32 := 0x03010113.
Lemma F_16500 : fetch_word Plain.M.loaded_segments (0x165fc : word) = Some W_16500.
Proof. vm_refl. Qed.
Lemma D_16500 : decode_any W_16500 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16504 : bv 32 := 0x00008067.
Lemma F_16504 : fetch_word Plain.M.loaded_segments (0x16600 : word) = Some W_16504.
Proof. vm_refl. Qed.
Lemma D_16504 : decode_any W_16504 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
