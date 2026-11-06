(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushS16.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13124 : bv 32 := 0xfffff517.
Lemma F_13124 : fetch_word Plain.M.loaded_segments (0x13124 : word) = Some W_13124.
Proof. vm_refl. Qed.
Lemma D_13124 : decode_any W_13124 = Some (Auipc 10 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_13128 : bv 32 := 0x86450513.
Lemma F_13128 : fetch_word Plain.M.loaded_segments (0x13128 : word) = Some W_13128.
Proof. vm_refl. Qed.
Lemma D_13128 : decode_any W_13128 = Some (OpImm ALU_ADD 10 10 2148, 4%Z).
Proof. vm_refl. Qed.

Definition W_1312c : bv 32 := 0x0000d597.
Lemma F_1312c : fetch_word Plain.M.loaded_segments (0x1312c : word) = Some W_1312c.
Proof. vm_refl. Qed.
Lemma D_1312c : decode_any W_1312c = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13130 : bv 32 := 0x8dc58593.
Lemma F_13130 : fetch_word Plain.M.loaded_segments (0x13130 : word) = Some W_13130.
Proof. vm_refl. Qed.
Lemma D_13130 : decode_any W_13130 = Some (OpImm ALU_ADD 11 11 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_13134 : bv 32 := 0x000000ef.
Lemma F_13134 : fetch_word Plain.M.loaded_segments (0x13134 : word) = Some W_13134.
Proof. vm_refl. Qed.
Lemma D_13134 : decode_any W_13134 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13138 : bv 32 := 0x0040006f.
Lemma F_13138 : fetch_word Plain.M.loaded_segments (0x13138 : word) = Some W_13138.
Proof. vm_refl. Qed.
Lemma D_13138 : decode_any W_13138 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1313c : bv 32 := 0x00813083.
Lemma F_1313c : fetch_word Plain.M.loaded_segments (0x1313c : word) = Some W_1313c.
Proof. vm_refl. Qed.
Lemma D_1313c : decode_any W_1313c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13140 : bv 32 := 0x00013403.
Lemma F_13140 : fetch_word Plain.M.loaded_segments (0x13140 : word) = Some W_13140.
Proof. vm_refl. Qed.
Lemma D_13140 : decode_any W_13140 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13144 : bv 32 := 0x01010113.
Lemma F_13144 : fetch_word Plain.M.loaded_segments (0x13144 : word) = Some W_13144.
Proof. vm_refl. Qed.
Lemma D_13144 : decode_any W_13144 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13148 : bv 32 := 0x00008067.
Lemma F_13148 : fetch_word Plain.M.loaded_segments (0x13148 : word) = Some W_13148.
Proof. vm_refl. Qed.
Lemma D_13148 : decode_any W_13148 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1314c : bv 32 := 0xff010113.
Lemma F_1314c : fetch_word Plain.M.loaded_segments (0x1314c : word) = Some W_1314c.
Proof. vm_refl. Qed.
Lemma D_1314c : decode_any W_1314c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13150 : bv 32 := 0x00113423.
Lemma F_13150 : fetch_word Plain.M.loaded_segments (0x13150 : word) = Some W_13150.
Proof. vm_refl. Qed.
Lemma D_13150 : decode_any W_13150 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13154 : bv 32 := 0x00813023.
Lemma F_13154 : fetch_word Plain.M.loaded_segments (0x13154 : word) = Some W_13154.
Proof. vm_refl. Qed.
Lemma D_13154 : decode_any W_13154 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13158 : bv 32 := 0x01010413.
Lemma F_13158 : fetch_word Plain.M.loaded_segments (0x13158 : word) = Some W_13158.
Proof. vm_refl. Qed.
Lemma D_13158 : decode_any W_13158 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1315c : bv 32 := 0x0000d517.
Lemma F_1315c : fetch_word Plain.M.loaded_segments (0x1315c : word) = Some W_1315c.
Proof. vm_refl. Qed.
Lemma D_1315c : decode_any W_1315c = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13160 : bv 32 := 0x8ec50513.
Lemma F_13160 : fetch_word Plain.M.loaded_segments (0x13160 : word) = Some W_13160.
Proof. vm_refl. Qed.
Lemma D_13160 : decode_any W_13160 = Some (OpImm ALU_ADD 10 10 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_13164 : bv 32 := 0x00054503.
Lemma F_13164 : fetch_word Plain.M.loaded_segments (0x13164 : word) = Some W_13164.
Proof. vm_refl. Qed.
Lemma D_13164 : decode_any W_13164 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13168 : bv 32 := 0x00157513.
Lemma F_13168 : fetch_word Plain.M.loaded_segments (0x13168 : word) = Some W_13168.
Proof. vm_refl. Qed.
Lemma D_13168 : decode_any W_13168 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1316c : bv 32 := 0x00050663.
Lemma F_1316c : fetch_word Plain.M.loaded_segments (0x1316c : word) = Some W_1316c.
Proof. vm_refl. Qed.
Lemma D_1316c : decode_any W_1316c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13170 : bv 32 := 0x0040006f.
Lemma F_13170 : fetch_word Plain.M.loaded_segments (0x13170 : word) = Some W_13170.
Proof. vm_refl. Qed.
Lemma D_13170 : decode_any W_13170 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13174 : bv 32 := 0x0580006f.
Lemma F_13174 : fetch_word Plain.M.loaded_segments (0x13174 : word) = Some W_13174.
Proof. vm_refl. Qed.
Lemma D_13174 : decode_any W_13174 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_13178 : bv 32 := 0x0000d517.
Lemma F_13178 : fetch_word Plain.M.loaded_segments (0x13178 : word) = Some W_13178.
Proof. vm_refl. Qed.
Lemma D_13178 : decode_any W_13178 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1317c : bv 32 := 0x8d050593.
Lemma F_1317c : fetch_word Plain.M.loaded_segments (0x1317c : word) = Some W_1317c.
Proof. vm_refl. Qed.
Lemma D_1317c : decode_any W_1317c = Some (OpImm ALU_ADD 11 10 2256, 4%Z).
Proof. vm_refl. Qed.

Definition W_13180 : bv 32 := 0x00100513.
Lemma F_13180 : fetch_word Plain.M.loaded_segments (0x13180 : word) = Some W_13180.
Proof. vm_refl. Qed.
Lemma D_13180 : decode_any W_13180 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13184 : bv 32 := 0x00a58023.
Lemma F_13184 : fetch_word Plain.M.loaded_segments (0x13184 : word) = Some W_13184.
Proof. vm_refl. Qed.
Lemma D_13184 : decode_any W_13184 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13188 : bv 32 := 0x0000b517.
Lemma F_13188 : fetch_word Plain.M.loaded_segments (0x13188 : word) = Some W_13188.
Proof. vm_refl. Qed.
Lemma D_13188 : decode_any W_13188 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1318c : bv 32 := 0x5d053503.
Lemma F_1318c : fetch_word Plain.M.loaded_segments (0x1318c : word) = Some W_1318c.
Proof. vm_refl. Qed.
Lemma D_1318c : decode_any W_1318c = Some (Load SZ8 true 10 10 1488, 4%Z).
Proof. vm_refl. Qed.

Definition W_13190 : bv 32 := 0x00050e63.
Lemma F_13190 : fetch_word Plain.M.loaded_segments (0x13190 : word) = Some W_13190.
Proof. vm_refl. Qed.
Lemma D_13190 : decode_any W_13190 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_13194 : bv 32 := 0x0040006f.
Lemma F_13194 : fetch_word Plain.M.loaded_segments (0x13194 : word) = Some W_13194.
Proof. vm_refl. Qed.
Lemma D_13194 : decode_any W_13194 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13198 : bv 32 := 0x0000c517.
Lemma F_13198 : fetch_word Plain.M.loaded_segments (0x13198 : word) = Some W_13198.
Proof. vm_refl. Qed.
Lemma D_13198 : decode_any W_13198 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1319c : bv 32 := 0x63050513.
Lemma F_1319c : fetch_word Plain.M.loaded_segments (0x1319c : word) = Some W_1319c.
Proof. vm_refl. Qed.
Lemma D_1319c : decode_any W_1319c = Some (OpImm ALU_ADD 10 10 1584, 4%Z).
Proof. vm_refl. Qed.

Definition W_131a0 : bv 32 := 0x00053503.
Lemma F_131a0 : fetch_word Plain.M.loaded_segments (0x131a0 : word) = Some W_131a0.
Proof. vm_refl. Qed.
Lemma D_131a0 : decode_any W_131a0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131a4 : bv 32 := 0x638020ef.
Lemma F_131a4 : fetch_word Plain.M.loaded_segments (0x131a4 : word) = Some W_131a4.
Proof. vm_refl. Qed.
Lemma D_131a4 : decode_any W_131a4 = Some (Jal 1 9784, 4%Z).
Proof. vm_refl. Qed.

Definition W_131a8 : bv 32 := 0x0040006f.
Lemma F_131a8 : fetch_word Plain.M.loaded_segments (0x131a8 : word) = Some W_131a8.
Proof. vm_refl. Qed.
Lemma D_131a8 : decode_any W_131a8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_131ac : bv 32 := 0x0000b517.
Lemma F_131ac : fetch_word Plain.M.loaded_segments (0x131ac : word) = Some W_131ac.
Proof. vm_refl. Qed.
Lemma D_131ac : decode_any W_131ac = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_131b0 : bv 32 := 0x5b453503.
Lemma F_131b0 : fetch_word Plain.M.loaded_segments (0x131b0 : word) = Some W_131b0.
Proof. vm_refl. Qed.
Lemma D_131b0 : decode_any W_131b0 = Some (Load SZ8 true 10 10 1460, 4%Z).
Proof. vm_refl. Qed.

Definition W_131b4 : bv 32 := 0x00050c63.
Lemma F_131b4 : fetch_word Plain.M.loaded_segments (0x131b4 : word) = Some W_131b4.
Proof. vm_refl. Qed.
Lemma D_131b4 : decode_any W_131b4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_131b8 : bv 32 := 0x0040006f.
Lemma F_131b8 : fetch_word Plain.M.loaded_segments (0x131b8 : word) = Some W_131b8.
Proof. vm_refl. Qed.
Lemma D_131b8 : decode_any W_131b8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_131bc : bv 32 := 0xffffe517.
Lemma F_131bc : fetch_word Plain.M.loaded_segments (0x131bc : word) = Some W_131bc.
Proof. vm_refl. Qed.
Lemma D_131bc : decode_any W_131bc = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_131c0 : bv 32 := 0x7cc50513.
Lemma F_131c0 : fetch_word Plain.M.loaded_segments (0x131c0 : word) = Some W_131c0.
Proof. vm_refl. Qed.
Lemma D_131c0 : decode_any W_131c0 = Some (OpImm ALU_ADD 10 10 1996, 4%Z).
Proof. vm_refl. Qed.

Definition W_131c4 : bv 32 := 0x000000ef.
Lemma F_131c4 : fetch_word Plain.M.loaded_segments (0x131c4 : word) = Some W_131c4.
Proof. vm_refl. Qed.
Lemma D_131c4 : decode_any W_131c4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131c8 : bv 32 := 0x0040006f.
Lemma F_131c8 : fetch_word Plain.M.loaded_segments (0x131c8 : word) = Some W_131c8.
Proof. vm_refl. Qed.
Lemma D_131c8 : decode_any W_131c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_131cc : bv 32 := 0x00813083.
Lemma F_131cc : fetch_word Plain.M.loaded_segments (0x131cc : word) = Some W_131cc.
Proof. vm_refl. Qed.
Lemma D_131cc : decode_any W_131cc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_131d0 : bv 32 := 0x00013403.
Lemma F_131d0 : fetch_word Plain.M.loaded_segments (0x131d0 : word) = Some W_131d0.
Proof. vm_refl. Qed.
Lemma D_131d0 : decode_any W_131d0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131d4 : bv 32 := 0x01010113.
Lemma F_131d4 : fetch_word Plain.M.loaded_segments (0x131d4 : word) = Some W_131d4.
Proof. vm_refl. Qed.
Lemma D_131d4 : decode_any W_131d4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_131d8 : bv 32 := 0x00008067.
Lemma F_131d8 : fetch_word Plain.M.loaded_segments (0x131d8 : word) = Some W_131d8.
Proof. vm_refl. Qed.
Lemma D_131d8 : decode_any W_131d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13604 : bv 32 := 0x0001c517.
Lemma F_13604 : fetch_word Plain.M.loaded_segments (0x13604 : word) = Some W_13604.
Proof. vm_refl. Qed.
Lemma D_13604 : decode_any W_13604 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_13608 : bv 32 := 0x45054503.
Lemma F_13608 : fetch_word Plain.M.loaded_segments (0x13608 : word) = Some W_13608.
Proof. vm_refl. Qed.
Lemma D_13608 : decode_any W_13608 = Some (Load SZ1 false 10 10 1104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1360c : bv 32 := 0x00051463.
Lemma F_1360c : fetch_word Plain.M.loaded_segments (0x1360c : word) = Some W_1360c.
Proof. vm_refl. Qed.
Lemma D_1360c : decode_any W_1360c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13610 : bv 32 := 0x00008067.
Lemma F_13610 : fetch_word Plain.M.loaded_segments (0x13610 : word) = Some W_13610.
Proof. vm_refl. Qed.
Lemma D_13610 : decode_any W_13610 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13614 : bv 32 := 0xff010113.
Lemma F_13614 : fetch_word Plain.M.loaded_segments (0x13614 : word) = Some W_13614.
Proof. vm_refl. Qed.
Lemma D_13614 : decode_any W_13614 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13618 : bv 32 := 0x00113423.
Lemma F_13618 : fetch_word Plain.M.loaded_segments (0x13618 : word) = Some W_13618.
Proof. vm_refl. Qed.
Lemma D_13618 : decode_any W_13618 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1361c : bv 32 := 0x0000b517.
Lemma F_1361c : fetch_word Plain.M.loaded_segments (0x1361c : word) = Some W_1361c.
Proof. vm_refl. Qed.
Lemma D_1361c : decode_any W_1361c = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_13620 : bv 32 := 0x15c53503.
Lemma F_13620 : fetch_word Plain.M.loaded_segments (0x13620 : word) = Some W_13620.
Proof. vm_refl. Qed.
Lemma D_13620 : decode_any W_13620 = Some (Load SZ8 true 10 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_13624 : bv 32 := 0x00053503.
Lemma F_13624 : fetch_word Plain.M.loaded_segments (0x13624 : word) = Some W_13624.
Proof. vm_refl. Qed.
Lemma D_13624 : decode_any W_13624 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13628 : bv 32 := 0x328040ef.
Lemma F_13628 : fetch_word Plain.M.loaded_segments (0x13628 : word) = Some W_13628.
Proof. vm_refl. Qed.
Lemma D_13628 : decode_any W_13628 = Some (Jal 1 17192, 4%Z).
Proof. vm_refl. Qed.

Definition W_1362c : bv 32 := 0x04d00513.
Lemma F_1362c : fetch_word Plain.M.loaded_segments (0x1362c : word) = Some W_1362c.
Proof. vm_refl. Qed.
Lemma D_1362c : decode_any W_1362c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13630 : bv 32 := 0x0340a0ef.
Lemma F_13630 : fetch_word Plain.M.loaded_segments (0x13630 : word) = Some W_13630.
Proof. vm_refl. Qed.
Lemma D_13630 : decode_any W_13630 = Some (Jal 1 41012, 4%Z).
Proof. vm_refl. Qed.

Definition W_15714 : bv 32 := 0xfd010113.
Lemma F_15714 : fetch_word Plain.M.loaded_segments (0x15714 : word) = Some W_15714.
Proof. vm_refl. Qed.
Lemma D_15714 : decode_any W_15714 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15718 : bv 32 := 0x02113423.
Lemma F_15718 : fetch_word Plain.M.loaded_segments (0x15718 : word) = Some W_15718.
Proof. vm_refl. Qed.
Lemma D_15718 : decode_any W_15718 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1571c : bv 32 := 0x02813023.
Lemma F_1571c : fetch_word Plain.M.loaded_segments (0x1571c : word) = Some W_1571c.
Proof. vm_refl. Qed.
Lemma D_1571c : decode_any W_1571c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15720 : bv 32 := 0x00913c23.
Lemma F_15720 : fetch_word Plain.M.loaded_segments (0x15720 : word) = Some W_15720.
Proof. vm_refl. Qed.
Lemma D_15720 : decode_any W_15720 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15724 : bv 32 := 0x01213823.
Lemma F_15724 : fetch_word Plain.M.loaded_segments (0x15724 : word) = Some W_15724.
Proof. vm_refl. Qed.
Lemma D_15724 : decode_any W_15724 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15728 : bv 32 := 0x01313423.
Lemma F_15728 : fetch_word Plain.M.loaded_segments (0x15728 : word) = Some W_15728.
Proof. vm_refl. Qed.
Lemma D_15728 : decode_any W_15728 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1572c : bv 32 := 0x0003a517.
Lemma F_1572c : fetch_word Plain.M.loaded_segments (0x1572c : word) = Some W_1572c.
Proof. vm_refl. Qed.
Lemma D_1572c : decode_any W_1572c = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15730 : bv 32 := 0x46450913.
Lemma F_15730 : fetch_word Plain.M.loaded_segments (0x15730 : word) = Some W_15730.
Proof. vm_refl. Qed.
Lemma D_15730 : decode_any W_15730 = Some (OpImm ALU_ADD 18 10 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_15734 : bv 32 := 0x00490413.
Lemma F_15734 : fetch_word Plain.M.loaded_segments (0x15734 : word) = Some W_15734.
Proof. vm_refl. Qed.
Lemma D_15734 : decode_any W_15734 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15738 : bv 32 := 0x00040513.
Lemma F_15738 : fetch_word Plain.M.loaded_segments (0x15738 : word) = Some W_15738.
Proof. vm_refl. Qed.
Lemma D_15738 : decode_any W_15738 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1573c : bv 32 := 0x3f9070ef.
Lemma F_1573c : fetch_word Plain.M.loaded_segments (0x1573c : word) = Some W_1573c.
Proof. vm_refl. Qed.
Lemma D_1573c : decode_any W_1573c = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_15740 : bv 32 := 0x01093503.
Lemma F_15740 : fetch_word Plain.M.loaded_segments (0x15740 : word) = Some W_15740.
Proof. vm_refl. Qed.
Lemma D_15740 : decode_any W_15740 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15744 : bv 32 := 0x06050863.
Lemma F_15744 : fetch_word Plain.M.loaded_segments (0x15744 : word) = Some W_15744.
Proof. vm_refl. Qed.
Lemma D_15744 : decode_any W_15744 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_15748 : bv 32 := 0x00892583.
Lemma F_15748 : fetch_word Plain.M.loaded_segments (0x15748 : word) = Some W_15748.
Proof. vm_refl. Qed.
Lemma D_15748 : decode_any W_15748 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1574c : bv 32 := 0x0180006f.
Lemma F_1574c : fetch_word Plain.M.loaded_segments (0x1574c : word) = Some W_1574c.
Proof. vm_refl. Qed.
Lemma D_1574c : decode_any W_1574c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15750 : bv 32 := 0x00053503.
Lemma F_15750 : fetch_word Plain.M.loaded_segments (0x15750 : word) = Some W_15750.
Proof. vm_refl. Qed.
Lemma D_15750 : decode_any W_15750 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15754 : bv 32 := 0x02000593.
Lemma F_15754 : fetch_word Plain.M.loaded_segments (0x15754 : word) = Some W_15754.
Proof. vm_refl. Qed.
Lemma D_15754 : decode_any W_15754 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15758 : bv 32 := 0x00b92423.
Lemma F_15758 : fetch_word Plain.M.loaded_segments (0x15758 : word) = Some W_15758.
Proof. vm_refl. Qed.
Lemma D_15758 : decode_any W_15758 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1575c : bv 32 := 0x00a93823.
Lemma F_1575c : fetch_word Plain.M.loaded_segments (0x1575c : word) = Some W_1575c.
Proof. vm_refl. Qed.
Lemma D_1575c : decode_any W_1575c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15760 : bv 32 := 0x04050a63.
Lemma F_15760 : fetch_word Plain.M.loaded_segments (0x15760 : word) = Some W_15760.
Proof. vm_refl. Qed.
Lemma D_15760 : decode_any W_15760 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_15764 : bv 32 := 0xfff5861b.
Lemma F_15764 : fetch_word Plain.M.loaded_segments (0x15764 : word) = Some W_15764.
Proof. vm_refl. Qed.
Lemma D_15764 : decode_any W_15764 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15768 : bv 32 := 0x00c92423.
Lemma F_15768 : fetch_word Plain.M.loaded_segments (0x15768 : word) = Some W_15768.
Proof. vm_refl. Qed.
Lemma D_15768 : decode_any W_15768 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1576c : bv 32 := 0xfeb052e3.
Lemma F_1576c : fetch_word Plain.M.loaded_segments (0x1576c : word) = Some W_1576c.
Proof. vm_refl. Qed.
Lemma D_1576c : decode_any W_1576c = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_15770 : bv 32 := 0x01093503.
Lemma F_15770 : fetch_word Plain.M.loaded_segments (0x15770 : word) = Some W_15770.
Proof. vm_refl. Qed.
Lemma D_15770 : decode_any W_15770 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15774 : bv 32 := 0x00361613.
Lemma F_15774 : fetch_word Plain.M.loaded_segments (0x15774 : word) = Some W_15774.
Proof. vm_refl. Qed.
Lemma D_15774 : decode_any W_15774 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15778 : bv 32 := 0x00c50533.
Lemma F_15778 : fetch_word Plain.M.loaded_segments (0x15778 : word) = Some W_15778.
Proof. vm_refl. Qed.
Lemma D_15778 : decode_any W_15778 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1577c : bv 32 := 0x00853983.
Lemma F_1577c : fetch_word Plain.M.loaded_segments (0x1577c : word) = Some W_1577c.
Proof. vm_refl. Qed.
Lemma D_1577c : decode_any W_1577c = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15780 : bv 32 := 0x10853483.
Lemma F_15780 : fetch_word Plain.M.loaded_segments (0x15780 : word) = Some W_15780.
Proof. vm_refl. Qed.
Lemma D_15780 : decode_any W_15780 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_15784 : bv 32 := 0x00040513.
Lemma F_15784 : fetch_word Plain.M.loaded_segments (0x15784 : word) = Some W_15784.
Proof. vm_refl. Qed.
Lemma D_15784 : decode_any W_15784 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15788 : bv 32 := 0x635070ef.
Lemma F_15788 : fetch_word Plain.M.loaded_segments (0x15788 : word) = Some W_15788.
Proof. vm_refl. Qed.
Lemma D_15788 : decode_any W_15788 = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_1578c : bv 32 := 0x00048513.
Lemma F_1578c : fetch_word Plain.M.loaded_segments (0x1578c : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15790 : bv 32 := 0x000980e7.
Lemma F_15790 : fetch_word Plain.M.loaded_segments (0x15790 : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15794 : bv 32 := 0x00040513.
Lemma F_15794 : fetch_word Plain.M.loaded_segments (0x15794 : word) = Some W_15794.
Proof. vm_refl. Qed.
Lemma D_15794 : decode_any W_15794 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15798 : bv 32 := 0x39d070ef.
Lemma F_15798 : fetch_word Plain.M.loaded_segments (0x15798 : word) = Some W_15798.
Proof. vm_refl. Qed.
Lemma D_15798 : decode_any W_15798 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_1579c : bv 32 := 0x00892503.
Lemma F_1579c : fetch_word Plain.M.loaded_segments (0x1579c : word) = Some W_1579c.
Proof. vm_refl. Qed.
Lemma D_1579c : decode_any W_1579c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_157a0 : bv 32 := 0xfff5061b.
Lemma F_157a0 : fetch_word Plain.M.loaded_segments (0x157a0 : word) = Some W_157a0.
Proof. vm_refl. Qed.
Lemma D_157a0 : decode_any W_157a0 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_157a4 : bv 32 := 0x00c92423.
Lemma F_157a4 : fetch_word Plain.M.loaded_segments (0x157a4 : word) = Some W_157a4.
Proof. vm_refl. Qed.
Lemma D_157a4 : decode_any W_157a4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_157a8 : bv 32 := 0xfca044e3.
Lemma F_157a8 : fetch_word Plain.M.loaded_segments (0x157a8 : word) = Some W_157a8.
Proof. vm_refl. Qed.
Lemma D_157a8 : decode_any W_157a8 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_157ac : bv 32 := 0x01093503.
Lemma F_157ac : fetch_word Plain.M.loaded_segments (0x157ac : word) = Some W_157ac.
Proof. vm_refl. Qed.
Lemma D_157ac : decode_any W_157ac = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_157b0 : bv 32 := 0xfa1ff06f.
Lemma F_157b0 : fetch_word Plain.M.loaded_segments (0x157b0 : word) = Some W_157b0.
Proof. vm_refl. Qed.
Lemma D_157b0 : decode_any W_157b0 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_157b4 : bv 32 := 0x00100513.
Lemma F_157b4 : fetch_word Plain.M.loaded_segments (0x157b4 : word) = Some W_157b4.
Proof. vm_refl. Qed.
Lemma D_157b4 : decode_any W_157b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_157b8 : bv 32 := 0x00a90023.
Lemma F_157b8 : fetch_word Plain.M.loaded_segments (0x157b8 : word) = Some W_157b8.
Proof. vm_refl. Qed.
Lemma D_157b8 : decode_any W_157b8 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157bc : bv 32 := 0x00040513.
Lemma F_157bc : fetch_word Plain.M.loaded_segments (0x157bc : word) = Some W_157bc.
Proof. vm_refl. Qed.
Lemma D_157bc : decode_any W_157bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157c0 : bv 32 := 0x02813083.
Lemma F_157c0 : fetch_word Plain.M.loaded_segments (0x157c0 : word) = Some W_157c0.
Proof. vm_refl. Qed.
Lemma D_157c0 : decode_any W_157c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_157c4 : bv 32 := 0x02013403.
Lemma F_157c4 : fetch_word Plain.M.loaded_segments (0x157c4 : word) = Some W_157c4.
Proof. vm_refl. Qed.
Lemma D_157c4 : decode_any W_157c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_157c8 : bv 32 := 0x01813483.
Lemma F_157c8 : fetch_word Plain.M.loaded_segments (0x157c8 : word) = Some W_157c8.
Proof. vm_refl. Qed.
Lemma D_157c8 : decode_any W_157c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_157cc : bv 32 := 0x01013903.
Lemma F_157cc : fetch_word Plain.M.loaded_segments (0x157cc : word) = Some W_157cc.
Proof. vm_refl. Qed.
Lemma D_157cc : decode_any W_157cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_157d0 : bv 32 := 0x00813983.
Lemma F_157d0 : fetch_word Plain.M.loaded_segments (0x157d0 : word) = Some W_157d0.
Proof. vm_refl. Qed.
Lemma D_157d0 : decode_any W_157d0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_157d4 : bv 32 := 0x03010113.
Lemma F_157d4 : fetch_word Plain.M.loaded_segments (0x157d4 : word) = Some W_157d4.
Proof. vm_refl. Qed.
Lemma D_157d4 : decode_any W_157d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_157d8 : bv 32 := 0x5e50706f.
Lemma F_157d8 : fetch_word Plain.M.loaded_segments (0x157d8 : word) = Some W_157d8.
Proof. vm_refl. Qed.
Lemma D_157d8 : decode_any W_157d8 = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_157dc : bv 32 := 0x00008067.
Lemma F_157dc : fetch_word Plain.M.loaded_segments (0x157dc : word) = Some W_157dc.
Proof. vm_refl. Qed.
Lemma D_157dc : decode_any W_157dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157e0 : bv 32 := 0xfd010113.
Lemma F_157e0 : fetch_word Plain.M.loaded_segments (0x157e0 : word) = Some W_157e0.
Proof. vm_refl. Qed.
Lemma D_157e0 : decode_any W_157e0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_157e4 : bv 32 := 0x02113423.
Lemma F_157e4 : fetch_word Plain.M.loaded_segments (0x157e4 : word) = Some W_157e4.
Proof. vm_refl. Qed.
Lemma D_157e4 : decode_any W_157e4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_157e8 : bv 32 := 0x02813023.
Lemma F_157e8 : fetch_word Plain.M.loaded_segments (0x157e8 : word) = Some W_157e8.
Proof. vm_refl. Qed.
Lemma D_157e8 : decode_any W_157e8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_157ec : bv 32 := 0x00913c23.
Lemma F_157ec : fetch_word Plain.M.loaded_segments (0x157ec : word) = Some W_157ec.
Proof. vm_refl. Qed.
Lemma D_157ec : decode_any W_157ec = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_157f0 : bv 32 := 0x01213823.
Lemma F_157f0 : fetch_word Plain.M.loaded_segments (0x157f0 : word) = Some W_157f0.
Proof. vm_refl. Qed.
Lemma D_157f0 : decode_any W_157f0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_157f4 : bv 32 := 0x01313423.
Lemma F_157f4 : fetch_word Plain.M.loaded_segments (0x157f4 : word) = Some W_157f4.
Proof. vm_refl. Qed.
Lemma D_157f4 : decode_any W_157f4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_157f8 : bv 32 := 0x00050493.
Lemma F_157f8 : fetch_word Plain.M.loaded_segments (0x157f8 : word) = Some W_157f8.
Proof. vm_refl. Qed.
Lemma D_157f8 : decode_any W_157f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157fc : bv 32 := 0x0003a517.
Lemma F_157fc : fetch_word Plain.M.loaded_segments (0x157fc : word) = Some W_157fc.
Proof. vm_refl. Qed.
Lemma D_157fc : decode_any W_157fc = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15800 : bv 32 := 0x39450993.
Lemma F_15800 : fetch_word Plain.M.loaded_segments (0x15800 : word) = Some W_15800.
Proof. vm_refl. Qed.
Lemma D_15800 : decode_any W_15800 = Some (OpImm ALU_ADD 19 10 916, 4%Z).
Proof. vm_refl. Qed.

Definition W_15804 : bv 32 := 0x00498413.
Lemma F_15804 : fetch_word Plain.M.loaded_segments (0x15804 : word) = Some W_15804.
Proof. vm_refl. Qed.
Lemma D_15804 : decode_any W_15804 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15808 : bv 32 := 0x00040513.
Lemma F_15808 : fetch_word Plain.M.loaded_segments (0x15808 : word) = Some W_15808.
Proof. vm_refl. Qed.
Lemma D_15808 : decode_any W_15808 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1580c : bv 32 := 0x329070ef.
Lemma F_1580c : fetch_word Plain.M.loaded_segments (0x1580c : word) = Some W_1580c.
Proof. vm_refl. Qed.
Lemma D_1580c : decode_any W_1580c = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_15810 : bv 32 := 0x0009c503.
Lemma F_15810 : fetch_word Plain.M.loaded_segments (0x15810 : word) = Some W_15810.
Proof. vm_refl. Qed.
Lemma D_15810 : decode_any W_15810 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15814 : bv 32 := 0xfff00913.
Lemma F_15814 : fetch_word Plain.M.loaded_segments (0x15814 : word) = Some W_15814.
Proof. vm_refl. Qed.
Lemma D_15814 : decode_any W_15814 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15818 : bv 32 := 0x06051263.
Lemma F_15818 : fetch_word Plain.M.loaded_segments (0x15818 : word) = Some W_15818.
Proof. vm_refl. Qed.
Lemma D_15818 : decode_any W_15818 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1581c : bv 32 := 0x0109b503.
Lemma F_1581c : fetch_word Plain.M.loaded_segments (0x1581c : word) = Some W_1581c.
Proof. vm_refl. Qed.
Lemma D_1581c : decode_any W_1581c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15820 : bv 32 := 0x00051663.
Lemma F_15820 : fetch_word Plain.M.loaded_segments (0x15820 : word) = Some W_15820.
Proof. vm_refl. Qed.
Lemma D_15820 : decode_any W_15820 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15824 : bv 32 := 0x01898513.
Lemma F_15824 : fetch_word Plain.M.loaded_segments (0x15824 : word) = Some W_15824.
Proof. vm_refl. Qed.
Lemma D_15824 : decode_any W_15824 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15828 : bv 32 := 0x00a9b823.
Lemma F_15828 : fetch_word Plain.M.loaded_segments (0x15828 : word) = Some W_15828.
Proof. vm_refl. Qed.
Lemma D_15828 : decode_any W_15828 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1582c : bv 32 := 0x0089a583.
Lemma F_1582c : fetch_word Plain.M.loaded_segments (0x1582c : word) = Some W_1582c.
Proof. vm_refl. Qed.
Lemma D_1582c : decode_any W_1582c = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15830 : bv 32 := 0x02000613.
Lemma F_15830 : fetch_word Plain.M.loaded_segments (0x15830 : word) = Some W_15830.
Proof. vm_refl. Qed.
Lemma D_15830 : decode_any W_15830 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15834 : bv 32 := 0x02c59263.
Lemma F_15834 : fetch_word Plain.M.loaded_segments (0x15834 : word) = Some W_15834.
Proof. vm_refl. Qed.
Lemma D_15834 : decode_any W_15834 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15838 : bv 32 := 0x20800513.
Lemma F_15838 : fetch_word Plain.M.loaded_segments (0x15838 : word) = Some W_15838.
Proof. vm_refl. Qed.
Lemma D_15838 : decode_any W_15838 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_1583c : bv 32 := 0x00100593.
Lemma F_1583c : fetch_word Plain.M.loaded_segments (0x1583c : word) = Some W_1583c.
Proof. vm_refl. Qed.
Lemma D_1583c : decode_any W_1583c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15840 : bv 32 := 0x3f4000ef.
Lemma F_15840 : fetch_word Plain.M.loaded_segments (0x15840 : word) = Some W_15840.
Proof. vm_refl. Qed.
Lemma D_15840 : decode_any W_15840 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_15844 : bv 32 := 0x02050c63.
Lemma F_15844 : fetch_word Plain.M.loaded_segments (0x15844 : word) = Some W_15844.
Proof. vm_refl. Qed.
Lemma D_15844 : decode_any W_15844 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_15848 : bv 32 := 0x00000593.
Lemma F_15848 : fetch_word Plain.M.loaded_segments (0x15848 : word) = Some W_15848.
Proof. vm_refl. Qed.
Lemma D_15848 : decode_any W_15848 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1584c : bv 32 := 0x0109b603.
Lemma F_1584c : fetch_word Plain.M.loaded_segments (0x1584c : word) = Some W_1584c.
Proof. vm_refl. Qed.
Lemma D_1584c : decode_any W_1584c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15850 : bv 32 := 0x00c53023.
Lemma F_15850 : fetch_word Plain.M.loaded_segments (0x15850 : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15854 : bv 32 := 0x00a9b823.
Lemma F_15854 : fetch_word Plain.M.loaded_segments (0x15854 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15858 : bv 32 := 0x00000913.
Lemma F_15858 : fetch_word Plain.M.loaded_segments (0x15858 : word) = Some W_15858.
Proof. vm_refl. Qed.
Lemma D_15858 : decode_any W_15858 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1585c : bv 32 := 0x00359613.
Lemma F_1585c : fetch_word Plain.M.loaded_segments (0x1585c : word) = Some W_1585c.
Proof. vm_refl. Qed.
Lemma D_1585c : decode_any W_1585c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15860 : bv 32 := 0x00c50533.
Lemma F_15860 : fetch_word Plain.M.loaded_segments (0x15860 : word) = Some W_15860.
Proof. vm_refl. Qed.
Lemma D_15860 : decode_any W_15860 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15864 : bv 32 := 0x00000617.
Lemma F_15864 : fetch_word Plain.M.loaded_segments (0x15864 : word) = Some W_15864.
Proof. vm_refl. Qed.
Lemma D_15864 : decode_any W_15864 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15868 : bv 32 := 0x00158593.
Lemma F_15868 : fetch_word Plain.M.loaded_segments (0x15868 : word) = Some W_15868.
Proof. vm_refl. Qed.
Lemma D_15868 : decode_any W_15868 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1586c : bv 32 := 0x04060613.
Lemma F_1586c : fetch_word Plain.M.loaded_segments (0x1586c : word) = Some W_1586c.
Proof. vm_refl. Qed.
Lemma D_1586c : decode_any W_1586c = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_15870 : bv 32 := 0x00c53423.
Lemma F_15870 : fetch_word Plain.M.loaded_segments (0x15870 : word) = Some W_15870.
Proof. vm_refl. Qed.
Lemma D_15870 : decode_any W_15870 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15874 : bv 32 := 0x10953423.
Lemma F_15874 : fetch_word Plain.M.loaded_segments (0x15874 : word) = Some W_15874.
Proof. vm_refl. Qed.
Lemma D_15874 : decode_any W_15874 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_15878 : bv 32 := 0x00b9a423.
Lemma F_15878 : fetch_word Plain.M.loaded_segments (0x15878 : word) = Some W_15878.
Proof. vm_refl. Qed.
Lemma D_15878 : decode_any W_15878 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1587c : bv 32 := 0x00040513.
Lemma F_1587c : fetch_word Plain.M.loaded_segments (0x1587c : word) = Some W_1587c.
Proof. vm_refl. Qed.
Lemma D_1587c : decode_any W_1587c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15880 : bv 32 := 0x53d070ef.
Lemma F_15880 : fetch_word Plain.M.loaded_segments (0x15880 : word) = Some W_15880.
Proof. vm_refl. Qed.
Lemma D_15880 : decode_any W_15880 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_15884 : bv 32 := 0x00090513.
Lemma F_15884 : fetch_word Plain.M.loaded_segments (0x15884 : word) = Some W_15884.
Proof. vm_refl. Qed.
Lemma D_15884 : decode_any W_15884 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15888 : bv 32 := 0x02813083.
Lemma F_15888 : fetch_word Plain.M.loaded_segments (0x15888 : word) = Some W_15888.
Proof. vm_refl. Qed.
Lemma D_15888 : decode_any W_15888 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1588c : bv 32 := 0x02013403.
Lemma F_1588c : fetch_word Plain.M.loaded_segments (0x1588c : word) = Some W_1588c.
Proof. vm_refl. Qed.
Lemma D_1588c : decode_any W_1588c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15890 : bv 32 := 0x01813483.
Lemma F_15890 : fetch_word Plain.M.loaded_segments (0x15890 : word) = Some W_15890.
Proof. vm_refl. Qed.
Lemma D_15890 : decode_any W_15890 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15894 : bv 32 := 0x01013903.
Lemma F_15894 : fetch_word Plain.M.loaded_segments (0x15894 : word) = Some W_15894.
Proof. vm_refl. Qed.
Lemma D_15894 : decode_any W_15894 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15898 : bv 32 := 0x00813983.
Lemma F_15898 : fetch_word Plain.M.loaded_segments (0x15898 : word) = Some W_15898.
Proof. vm_refl. Qed.
Lemma D_15898 : decode_any W_15898 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1589c : bv 32 := 0x03010113.
Lemma F_1589c : fetch_word Plain.M.loaded_segments (0x1589c : word) = Some W_1589c.
Proof. vm_refl. Qed.
Lemma D_1589c : decode_any W_1589c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_158a0 : bv 32 := 0x00008067.
Lemma F_158a0 : fetch_word Plain.M.loaded_segments (0x158a0 : word) = Some W_158a0.
Proof. vm_refl. Qed.
Lemma D_158a0 : decode_any W_158a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158a4 : bv 32 := 0x00050067.
Lemma F_158a4 : fetch_word Plain.M.loaded_segments (0x158a4 : word) = Some W_158a4.
Proof. vm_refl. Qed.
Lemma D_158a4 : decode_any W_158a4 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158a8 : bv 32 := 0x00008067.
Lemma F_158a8 : fetch_word Plain.M.loaded_segments (0x158a8 : word) = Some W_158a8.
Proof. vm_refl. Qed.
Lemma D_158a8 : decode_any W_158a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158ac : bv 32 := 0xfe010113.
Lemma F_158ac : fetch_word Plain.M.loaded_segments (0x158ac : word) = Some W_158ac.
Proof. vm_refl. Qed.
Lemma D_158ac : decode_any W_158ac = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_158b0 : bv 32 := 0x00113c23.
Lemma F_158b0 : fetch_word Plain.M.loaded_segments (0x158b0 : word) = Some W_158b0.
Proof. vm_refl. Qed.
Lemma D_158b0 : decode_any W_158b0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_158b4 : bv 32 := 0x00813823.
Lemma F_158b4 : fetch_word Plain.M.loaded_segments (0x158b4 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_158b8 : bv 32 := 0x00913423.
Lemma F_158b8 : fetch_word Plain.M.loaded_segments (0x158b8 : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_158bc : bv 32 := 0x00009517.
Lemma F_158bc : fetch_word Plain.M.loaded_segments (0x158bc : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_158c0 : bv 32 := 0x00009597.
Lemma F_158c0 : fetch_word Plain.M.loaded_segments (0x158c0 : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_158c4 : bv 32 := 0xefc53503.
Lemma F_158c4 : fetch_word Plain.M.loaded_segments (0x158c4 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (Load SZ8 true 10 10 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_158c8 : bv 32 := 0xf005b403.
Lemma F_158c8 : fetch_word Plain.M.loaded_segments (0x158c8 : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (Load SZ8 true 8 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_158cc : bv 32 := 0x00a47c63.
Lemma F_158cc : fetch_word Plain.M.loaded_segments (0x158cc : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_158d0 : bv 32 := 0xff853583.
Lemma F_158d0 : fetch_word Plain.M.loaded_segments (0x158d0 : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_158d4 : bv 32 := 0xff850493.
Lemma F_158d4 : fetch_word Plain.M.loaded_segments (0x158d4 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_158d8 : bv 32 := 0x000580e7.
Lemma F_158d8 : fetch_word Plain.M.loaded_segments (0x158d8 : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158dc : bv 32 := 0x00048513.
Lemma F_158dc : fetch_word Plain.M.loaded_segments (0x158dc : word) = Some W_158dc.
Proof. vm_refl. Qed.
Lemma D_158dc : decode_any W_158dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158e0 : bv 32 := 0xfe9468e3.
Lemma F_158e0 : fetch_word Plain.M.loaded_segments (0x158e0 : word) = Some W_158e0.
Proof. vm_refl. Qed.
Lemma D_158e0 : decode_any W_158e0 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_158e4 : bv 32 := 0x01813083.
Lemma F_158e4 : fetch_word Plain.M.loaded_segments (0x158e4 : word) = Some W_158e4.
Proof. vm_refl. Qed.
Lemma D_158e4 : decode_any W_158e4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_158e8 : bv 32 := 0x01013403.
Lemma F_158e8 : fetch_word Plain.M.loaded_segments (0x158e8 : word) = Some W_158e8.
Proof. vm_refl. Qed.
Lemma D_158e8 : decode_any W_158e8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_158ec : bv 32 := 0x00813483.
Lemma F_158ec : fetch_word Plain.M.loaded_segments (0x158ec : word) = Some W_158ec.
Proof. vm_refl. Qed.
Lemma D_158ec : decode_any W_158ec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_158f0 : bv 32 := 0x02010113.
Lemma F_158f0 : fetch_word Plain.M.loaded_segments (0x158f0 : word) = Some W_158f0.
Proof. vm_refl. Qed.
Lemma D_158f0 : decode_any W_158f0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_158f4 : bv 32 := 0xfb5ff06f.
Lemma F_158f4 : fetch_word Plain.M.loaded_segments (0x158f4 : word) = Some W_158f4.
Proof. vm_refl. Qed.
Lemma D_158f4 : decode_any W_158f4 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_158f8 : bv 32 := 0xff010113.
Lemma F_158f8 : fetch_word Plain.M.loaded_segments (0x158f8 : word) = Some W_158f8.
Proof. vm_refl. Qed.
Lemma D_158f8 : decode_any W_158f8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_158fc : bv 32 := 0x00113423.
Lemma F_158fc : fetch_word Plain.M.loaded_segments (0x158fc : word) = Some W_158fc.
Proof. vm_refl. Qed.
Lemma D_158fc : decode_any W_158fc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15900 : bv 32 := 0x00813023.
Lemma F_15900 : fetch_word Plain.M.loaded_segments (0x15900 : word) = Some W_15900.
Proof. vm_refl. Qed.
Lemma D_15900 : decode_any W_15900 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15904 : bv 32 := 0x00000593.
Lemma F_15904 : fetch_word Plain.M.loaded_segments (0x15904 : word) = Some W_15904.
Proof. vm_refl. Qed.
Lemma D_15904 : decode_any W_15904 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15908 : bv 32 := 0x00020613.
Lemma F_15908 : fetch_word Plain.M.loaded_segments (0x15908 : word) = Some W_15908.
Proof. vm_refl. Qed.
Lemma D_15908 : decode_any W_15908 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1590c : bv 32 := 0xf5862603.
Lemma F_1590c : fetch_word Plain.M.loaded_segments (0x1590c : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_15910 : bv 32 := 0x0003a697.
Lemma F_15910 : fetch_word Plain.M.loaded_segments (0x15910 : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15914 : bv 32 := 0x4a068693.
Lemma F_15914 : fetch_word Plain.M.loaded_segments (0x15914 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (OpImm ALU_ADD 13 13 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_15918 : bv 32 := 0x1606a72f.
Lemma F_15918 : fetch_word Plain.M.loaded_segments (0x15918 : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1591c : bv 32 := 0x00b71663.
Lemma F_1591c : fetch_word Plain.M.loaded_segments (0x1591c : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15920 : bv 32 := 0x1ec6a7af.
Lemma F_15920 : fetch_word Plain.M.loaded_segments (0x15920 : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15924 : bv 32 := 0xfe079ae3.
Lemma F_15924 : fetch_word Plain.M.loaded_segments (0x15924 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_15928 : bv 32 := 0x0007059b.
Lemma F_15928 : fetch_word Plain.M.loaded_segments (0x15928 : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1592c : bv 32 := 0x02c58263.
Lemma F_1592c : fetch_word Plain.M.loaded_segments (0x1592c : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15930 : bv 32 := 0x02058263.
Lemma F_15930 : fetch_word Plain.M.loaded_segments (0x15930 : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15934 : bv 32 := 0x04900893.
Lemma F_15934 : fetch_word Plain.M.loaded_segments (0x15934 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_15938 : bv 32 := 0x00000593.
Lemma F_15938 : fetch_word Plain.M.loaded_segments (0x15938 : word) = Some W_15938.
Proof. vm_refl. Qed.
Lemma D_15938 : decode_any W_15938 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1593c : bv 32 := 0x00000613.
Lemma F_1593c : fetch_word Plain.M.loaded_segments (0x1593c : word) = Some W_1593c.
Proof. vm_refl. Qed.
Lemma D_1593c : decode_any W_1593c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15940 : bv 32 := 0x00000693.
Lemma F_15940 : fetch_word Plain.M.loaded_segments (0x15940 : word) = Some W_15940.
Proof. vm_refl. Qed.
Lemma D_15940 : decode_any W_15940 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15944 : bv 32 := 0x00000513.
Lemma F_15944 : fetch_word Plain.M.loaded_segments (0x15944 : word) = Some W_15944.
Proof. vm_refl. Qed.
Lemma D_15944 : decode_any W_15944 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15948 : bv 32 := 0x00000073.
Lemma F_15948 : fetch_word Plain.M.loaded_segments (0x15948 : word) = Some W_15948.
Proof. vm_refl. Qed.
Lemma E_15948 : is_ecall W_15948 = true.
Proof. vm_refl. Qed.

Definition W_1594c : bv 32 := 0xff9ff06f.
Lemma F_1594c : fetch_word Plain.M.loaded_segments (0x1594c : word) = Some W_1594c.
Proof. vm_refl. Qed.
Lemma D_1594c : decode_any W_1594c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_15950 : bv 32 := 0x00000023.
Lemma F_15950 : fetch_word Plain.M.loaded_segments (0x15950 : word) = Some W_15950.
Proof. vm_refl. Qed.
Lemma D_15950 : decode_any W_15950 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15954 : bv 32 := 0x00050413.
Lemma F_15954 : fetch_word Plain.M.loaded_segments (0x15954 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15958 : bv 32 := 0xdbdff0ef.
Lemma F_15958 : fetch_word Plain.M.loaded_segments (0x15958 : word) = Some W_15958.
Proof. vm_refl. Qed.
Lemma D_15958 : decode_any W_15958 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_1595c : bv 32 := 0xf51ff0ef.
Lemma F_1595c : fetch_word Plain.M.loaded_segments (0x1595c : word) = Some W_1595c.
Proof. vm_refl. Qed.
Lemma D_1595c : decode_any W_1595c = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_15960 : bv 32 := 0x160020ef.
Lemma F_15960 : fetch_word Plain.M.loaded_segments (0x15960 : word) = Some W_15960.
Proof. vm_refl. Qed.
Lemma D_15960 : decode_any W_15960 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_15964 : bv 32 := 0x00040513.
Lemma F_15964 : fetch_word Plain.M.loaded_segments (0x15964 : word) = Some W_15964.
Proof. vm_refl. Qed.
Lemma D_15964 : decode_any W_15964 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15968 : bv 32 := 0xd91ff0ef.
Lemma F_15968 : fetch_word Plain.M.loaded_segments (0x15968 : word) = Some W_15968.
Proof. vm_refl. Qed.
Lemma D_15968 : decode_any W_15968 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d334 : bv 32 := 0x00033597.
Lemma F_1d334 : fetch_word Plain.M.loaded_segments (0x1d334 : word) = Some W_1d334.
Proof. vm_refl. Qed.
Lemma D_1d334 : decode_any W_1d334 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d338 : bv 32 := 0xaa758683.
Lemma F_1d338 : fetch_word Plain.M.loaded_segments (0x1d338 : word) = Some W_1d338.
Proof. vm_refl. Qed.
Lemma D_1d338 : decode_any W_1d338 = Some (Load SZ1 true 13 11 2727, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d33c : bv 32 := 0x1e068863.
Lemma F_1d33c : fetch_word Plain.M.loaded_segments (0x1d33c : word) = Some W_1d33c.
Proof. vm_refl. Qed.
Lemma D_1d33c : decode_any W_1d33c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d52c : bv 32 := 0x00008067.
Lemma F_1d52c : fetch_word Plain.M.loaded_segments (0x1d52c : word) = Some W_1d52c.
Proof. vm_refl. Qed.
Lemma D_1d52c : decode_any W_1d52c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5bc : bv 32 := 0x00052583.
Lemma F_1d5bc : fetch_word Plain.M.loaded_segments (0x1d5bc : word) = Some W_1d5bc.
Proof. vm_refl. Qed.
Lemma D_1d5bc : decode_any W_1d5bc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5c0 : bv 32 := 0x0005c463.
Lemma F_1d5c0 : fetch_word Plain.M.loaded_segments (0x1d5c0 : word) = Some W_1d5c0.
Proof. vm_refl. Qed.
Lemma D_1d5c0 : decode_any W_1d5c0 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5c4 : bv 32 := 0x00008067.
Lemma F_1d5c4 : fetch_word Plain.M.loaded_segments (0x1d5c4 : word) = Some W_1d5c4.
Proof. vm_refl. Qed.
Lemma D_1d5c4 : decode_any W_1d5c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
