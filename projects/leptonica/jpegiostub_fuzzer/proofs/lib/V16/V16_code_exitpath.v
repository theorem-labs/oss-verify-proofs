(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushU16.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_131e0 : bv 32 := 0xfffff517.
Lemma F_131e0 : fetch_word Ubsan.M.loaded_segments (0x131e0 : word) = Some W_131e0.
Proof. vm_refl. Qed.
Lemma D_131e0 : decode_any W_131e0 = Some (Auipc 10 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e4 : bv 32 := 0x81850513.
Lemma F_131e4 : fetch_word Ubsan.M.loaded_segments (0x131e4 : word) = Some W_131e4.
Proof. vm_refl. Qed.
Lemma D_131e4 : decode_any W_131e4 = Some (OpImm ALU_ADD 10 10 2072, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e8 : bv 32 := 0x0000d597.
Lemma F_131e8 : fetch_word Ubsan.M.loaded_segments (0x131e8 : word) = Some W_131e8.
Proof. vm_refl. Qed.
Lemma D_131e8 : decode_any W_131e8 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_131ec : bv 32 := 0xe6058593.
Lemma F_131ec : fetch_word Ubsan.M.loaded_segments (0x131ec : word) = Some W_131ec.
Proof. vm_refl. Qed.
Lemma D_131ec : decode_any W_131ec = Some (OpImm ALU_ADD 11 11 3680, 4%Z).
Proof. vm_refl. Qed.

Definition W_131f0 : bv 32 := 0x000000ef.
Lemma F_131f0 : fetch_word Ubsan.M.loaded_segments (0x131f0 : word) = Some W_131f0.
Proof. vm_refl. Qed.
Lemma D_131f0 : decode_any W_131f0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131f4 : bv 32 := 0x0040006f.
Lemma F_131f4 : fetch_word Ubsan.M.loaded_segments (0x131f4 : word) = Some W_131f4.
Proof. vm_refl. Qed.
Lemma D_131f4 : decode_any W_131f4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_131f8 : bv 32 := 0x00813083.
Lemma F_131f8 : fetch_word Ubsan.M.loaded_segments (0x131f8 : word) = Some W_131f8.
Proof. vm_refl. Qed.
Lemma D_131f8 : decode_any W_131f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_131fc : bv 32 := 0x00013403.
Lemma F_131fc : fetch_word Ubsan.M.loaded_segments (0x131fc : word) = Some W_131fc.
Proof. vm_refl. Qed.
Lemma D_131fc : decode_any W_131fc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13200 : bv 32 := 0x01010113.
Lemma F_13200 : fetch_word Ubsan.M.loaded_segments (0x13200 : word) = Some W_13200.
Proof. vm_refl. Qed.
Lemma D_13200 : decode_any W_13200 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13204 : bv 32 := 0x00008067.
Lemma F_13204 : fetch_word Ubsan.M.loaded_segments (0x13204 : word) = Some W_13204.
Proof. vm_refl. Qed.
Lemma D_13204 : decode_any W_13204 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13208 : bv 32 := 0xff010113.
Lemma F_13208 : fetch_word Ubsan.M.loaded_segments (0x13208 : word) = Some W_13208.
Proof. vm_refl. Qed.
Lemma D_13208 : decode_any W_13208 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1320c : bv 32 := 0x00113423.
Lemma F_1320c : fetch_word Ubsan.M.loaded_segments (0x1320c : word) = Some W_1320c.
Proof. vm_refl. Qed.
Lemma D_1320c : decode_any W_1320c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13210 : bv 32 := 0x00813023.
Lemma F_13210 : fetch_word Ubsan.M.loaded_segments (0x13210 : word) = Some W_13210.
Proof. vm_refl. Qed.
Lemma D_13210 : decode_any W_13210 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13214 : bv 32 := 0x01010413.
Lemma F_13214 : fetch_word Ubsan.M.loaded_segments (0x13214 : word) = Some W_13214.
Proof. vm_refl. Qed.
Lemma D_13214 : decode_any W_13214 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13218 : bv 32 := 0x0000d517.
Lemma F_13218 : fetch_word Ubsan.M.loaded_segments (0x13218 : word) = Some W_13218.
Proof. vm_refl. Qed.
Lemma D_13218 : decode_any W_13218 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1321c : bv 32 := 0xe7050513.
Lemma F_1321c : fetch_word Ubsan.M.loaded_segments (0x1321c : word) = Some W_1321c.
Proof. vm_refl. Qed.
Lemma D_1321c : decode_any W_1321c = Some (OpImm ALU_ADD 10 10 3696, 4%Z).
Proof. vm_refl. Qed.

Definition W_13220 : bv 32 := 0x00054503.
Lemma F_13220 : fetch_word Ubsan.M.loaded_segments (0x13220 : word) = Some W_13220.
Proof. vm_refl. Qed.
Lemma D_13220 : decode_any W_13220 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13224 : bv 32 := 0x00157513.
Lemma F_13224 : fetch_word Ubsan.M.loaded_segments (0x13224 : word) = Some W_13224.
Proof. vm_refl. Qed.
Lemma D_13224 : decode_any W_13224 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13228 : bv 32 := 0x00050663.
Lemma F_13228 : fetch_word Ubsan.M.loaded_segments (0x13228 : word) = Some W_13228.
Proof. vm_refl. Qed.
Lemma D_13228 : decode_any W_13228 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1322c : bv 32 := 0x0040006f.
Lemma F_1322c : fetch_word Ubsan.M.loaded_segments (0x1322c : word) = Some W_1322c.
Proof. vm_refl. Qed.
Lemma D_1322c : decode_any W_1322c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13230 : bv 32 := 0x0580006f.
Lemma F_13230 : fetch_word Ubsan.M.loaded_segments (0x13230 : word) = Some W_13230.
Proof. vm_refl. Qed.
Lemma D_13230 : decode_any W_13230 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_13234 : bv 32 := 0x0000d517.
Lemma F_13234 : fetch_word Ubsan.M.loaded_segments (0x13234 : word) = Some W_13234.
Proof. vm_refl. Qed.
Lemma D_13234 : decode_any W_13234 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13238 : bv 32 := 0xe5450593.
Lemma F_13238 : fetch_word Ubsan.M.loaded_segments (0x13238 : word) = Some W_13238.
Proof. vm_refl. Qed.
Lemma D_13238 : decode_any W_13238 = Some (OpImm ALU_ADD 11 10 3668, 4%Z).
Proof. vm_refl. Qed.

Definition W_1323c : bv 32 := 0x00100513.
Lemma F_1323c : fetch_word Ubsan.M.loaded_segments (0x1323c : word) = Some W_1323c.
Proof. vm_refl. Qed.
Lemma D_1323c : decode_any W_1323c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13240 : bv 32 := 0x00a58023.
Lemma F_13240 : fetch_word Ubsan.M.loaded_segments (0x13240 : word) = Some W_13240.
Proof. vm_refl. Qed.
Lemma D_13240 : decode_any W_13240 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13244 : bv 32 := 0x0000c517.
Lemma F_13244 : fetch_word Ubsan.M.loaded_segments (0x13244 : word) = Some W_13244.
Proof. vm_refl. Qed.
Lemma D_13244 : decode_any W_13244 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13248 : bv 32 := 0xb5c53503.
Lemma F_13248 : fetch_word Ubsan.M.loaded_segments (0x13248 : word) = Some W_13248.
Proof. vm_refl. Qed.
Lemma D_13248 : decode_any W_13248 = Some (Load SZ8 true 10 10 2908, 4%Z).
Proof. vm_refl. Qed.

Definition W_1324c : bv 32 := 0x00050e63.
Lemma F_1324c : fetch_word Ubsan.M.loaded_segments (0x1324c : word) = Some W_1324c.
Proof. vm_refl. Qed.
Lemma D_1324c : decode_any W_1324c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_13250 : bv 32 := 0x0040006f.
Lemma F_13250 : fetch_word Ubsan.M.loaded_segments (0x13250 : word) = Some W_13250.
Proof. vm_refl. Qed.
Lemma D_13250 : decode_any W_13250 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13254 : bv 32 := 0x0000d517.
Lemma F_13254 : fetch_word Ubsan.M.loaded_segments (0x13254 : word) = Some W_13254.
Proof. vm_refl. Qed.
Lemma D_13254 : decode_any W_13254 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13258 : bv 32 := 0xbbc50513.
Lemma F_13258 : fetch_word Ubsan.M.loaded_segments (0x13258 : word) = Some W_13258.
Proof. vm_refl. Qed.
Lemma D_13258 : decode_any W_13258 = Some (OpImm ALU_ADD 10 10 3004, 4%Z).
Proof. vm_refl. Qed.

Definition W_1325c : bv 32 := 0x00053503.
Lemma F_1325c : fetch_word Ubsan.M.loaded_segments (0x1325c : word) = Some W_1325c.
Proof. vm_refl. Qed.
Lemma D_1325c : decode_any W_1325c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13260 : bv 32 := 0x3c5020ef.
Lemma F_13260 : fetch_word Ubsan.M.loaded_segments (0x13260 : word) = Some W_13260.
Proof. vm_refl. Qed.
Lemma D_13260 : decode_any W_13260 = Some (Jal 1 11204, 4%Z).
Proof. vm_refl. Qed.

Definition W_13264 : bv 32 := 0x0040006f.
Lemma F_13264 : fetch_word Ubsan.M.loaded_segments (0x13264 : word) = Some W_13264.
Proof. vm_refl. Qed.
Lemma D_13264 : decode_any W_13264 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13268 : bv 32 := 0x0000c517.
Lemma F_13268 : fetch_word Ubsan.M.loaded_segments (0x13268 : word) = Some W_13268.
Proof. vm_refl. Qed.
Lemma D_13268 : decode_any W_13268 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1326c : bv 32 := 0xb4053503.
Lemma F_1326c : fetch_word Ubsan.M.loaded_segments (0x1326c : word) = Some W_1326c.
Proof. vm_refl. Qed.
Lemma D_1326c : decode_any W_1326c = Some (Load SZ8 true 10 10 2880, 4%Z).
Proof. vm_refl. Qed.

Definition W_13270 : bv 32 := 0x00050c63.
Lemma F_13270 : fetch_word Ubsan.M.loaded_segments (0x13270 : word) = Some W_13270.
Proof. vm_refl. Qed.
Lemma D_13270 : decode_any W_13270 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13274 : bv 32 := 0x0040006f.
Lemma F_13274 : fetch_word Ubsan.M.loaded_segments (0x13274 : word) = Some W_13274.
Proof. vm_refl. Qed.
Lemma D_13274 : decode_any W_13274 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13278 : bv 32 := 0xffffe517.
Lemma F_13278 : fetch_word Ubsan.M.loaded_segments (0x13278 : word) = Some W_13278.
Proof. vm_refl. Qed.
Lemma D_13278 : decode_any W_13278 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_1327c : bv 32 := 0x78050513.
Lemma F_1327c : fetch_word Ubsan.M.loaded_segments (0x1327c : word) = Some W_1327c.
Proof. vm_refl. Qed.
Lemma D_1327c : decode_any W_1327c = Some (OpImm ALU_ADD 10 10 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_13280 : bv 32 := 0x000000ef.
Lemma F_13280 : fetch_word Ubsan.M.loaded_segments (0x13280 : word) = Some W_13280.
Proof. vm_refl. Qed.
Lemma D_13280 : decode_any W_13280 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13284 : bv 32 := 0x0040006f.
Lemma F_13284 : fetch_word Ubsan.M.loaded_segments (0x13284 : word) = Some W_13284.
Proof. vm_refl. Qed.
Lemma D_13284 : decode_any W_13284 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13288 : bv 32 := 0x00813083.
Lemma F_13288 : fetch_word Ubsan.M.loaded_segments (0x13288 : word) = Some W_13288.
Proof. vm_refl. Qed.
Lemma D_13288 : decode_any W_13288 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1328c : bv 32 := 0x00013403.
Lemma F_1328c : fetch_word Ubsan.M.loaded_segments (0x1328c : word) = Some W_1328c.
Proof. vm_refl. Qed.
Lemma D_1328c : decode_any W_1328c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13290 : bv 32 := 0x01010113.
Lemma F_13290 : fetch_word Ubsan.M.loaded_segments (0x13290 : word) = Some W_13290.
Proof. vm_refl. Qed.
Lemma D_13290 : decode_any W_13290 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13294 : bv 32 := 0x00008067.
Lemma F_13294 : fetch_word Ubsan.M.loaded_segments (0x13294 : word) = Some W_13294.
Proof. vm_refl. Qed.
Lemma D_13294 : decode_any W_13294 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136c0 : bv 32 := 0x0001d517.
Lemma F_136c0 : fetch_word Ubsan.M.loaded_segments (0x136c0 : word) = Some W_136c0.
Proof. vm_refl. Qed.
Lemma D_136c0 : decode_any W_136c0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_136c4 : bv 32 := 0x9d454503.
Lemma F_136c4 : fetch_word Ubsan.M.loaded_segments (0x136c4 : word) = Some W_136c4.
Proof. vm_refl. Qed.
Lemma D_136c4 : decode_any W_136c4 = Some (Load SZ1 false 10 10 2516, 4%Z).
Proof. vm_refl. Qed.

Definition W_136c8 : bv 32 := 0x00051463.
Lemma F_136c8 : fetch_word Ubsan.M.loaded_segments (0x136c8 : word) = Some W_136c8.
Proof. vm_refl. Qed.
Lemma D_136c8 : decode_any W_136c8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_136cc : bv 32 := 0x00008067.
Lemma F_136cc : fetch_word Ubsan.M.loaded_segments (0x136cc : word) = Some W_136cc.
Proof. vm_refl. Qed.
Lemma D_136cc : decode_any W_136cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136d0 : bv 32 := 0xff010113.
Lemma F_136d0 : fetch_word Ubsan.M.loaded_segments (0x136d0 : word) = Some W_136d0.
Proof. vm_refl. Qed.
Lemma D_136d0 : decode_any W_136d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_136d4 : bv 32 := 0x00113423.
Lemma F_136d4 : fetch_word Ubsan.M.loaded_segments (0x136d4 : word) = Some W_136d4.
Proof. vm_refl. Qed.
Lemma D_136d4 : decode_any W_136d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_136d8 : bv 32 := 0x0000b517.
Lemma F_136d8 : fetch_word Ubsan.M.loaded_segments (0x136d8 : word) = Some W_136d8.
Proof. vm_refl. Qed.
Lemma D_136d8 : decode_any W_136d8 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_136dc : bv 32 := 0x6e853503.
Lemma F_136dc : fetch_word Ubsan.M.loaded_segments (0x136dc : word) = Some W_136dc.
Proof. vm_refl. Qed.
Lemma D_136dc : decode_any W_136dc = Some (Load SZ8 true 10 10 1768, 4%Z).
Proof. vm_refl. Qed.

Definition W_136e0 : bv 32 := 0x00053503.
Lemma F_136e0 : fetch_word Ubsan.M.loaded_segments (0x136e0 : word) = Some W_136e0.
Proof. vm_refl. Qed.
Lemma D_136e0 : decode_any W_136e0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136e4 : bv 32 := 0x0b5040ef.
Lemma F_136e4 : fetch_word Ubsan.M.loaded_segments (0x136e4 : word) = Some W_136e4.
Proof. vm_refl. Qed.
Lemma D_136e4 : decode_any W_136e4 = Some (Jal 1 18612, 4%Z).
Proof. vm_refl. Qed.

Definition W_136e8 : bv 32 := 0x04d00513.
Lemma F_136e8 : fetch_word Ubsan.M.loaded_segments (0x136e8 : word) = Some W_136e8.
Proof. vm_refl. Qed.
Lemma D_136e8 : decode_any W_136e8 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_136ec : bv 32 := 0x5c00a0ef.
Lemma F_136ec : fetch_word Ubsan.M.loaded_segments (0x136ec : word) = Some W_136ec.
Proof. vm_refl. Qed.
Lemma D_136ec : decode_any W_136ec = Some (Jal 1 42432, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d5c : bv 32 := 0xfd010113.
Lemma F_15d5c : fetch_word Ubsan.M.loaded_segments (0x15d5c : word) = Some W_15d5c.
Proof. vm_refl. Qed.
Lemma D_15d5c : decode_any W_15d5c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d60 : bv 32 := 0x02113423.
Lemma F_15d60 : fetch_word Ubsan.M.loaded_segments (0x15d60 : word) = Some W_15d60.
Proof. vm_refl. Qed.
Lemma D_15d60 : decode_any W_15d60 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d64 : bv 32 := 0x02813023.
Lemma F_15d64 : fetch_word Ubsan.M.loaded_segments (0x15d64 : word) = Some W_15d64.
Proof. vm_refl. Qed.
Lemma D_15d64 : decode_any W_15d64 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d68 : bv 32 := 0x00913c23.
Lemma F_15d68 : fetch_word Ubsan.M.loaded_segments (0x15d68 : word) = Some W_15d68.
Proof. vm_refl. Qed.
Lemma D_15d68 : decode_any W_15d68 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d6c : bv 32 := 0x01213823.
Lemma F_15d6c : fetch_word Ubsan.M.loaded_segments (0x15d6c : word) = Some W_15d6c.
Proof. vm_refl. Qed.
Lemma D_15d6c : decode_any W_15d6c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d70 : bv 32 := 0x01313423.
Lemma F_15d70 : fetch_word Ubsan.M.loaded_segments (0x15d70 : word) = Some W_15d70.
Proof. vm_refl. Qed.
Lemma D_15d70 : decode_any W_15d70 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d74 : bv 32 := 0x0003a517.
Lemma F_15d74 : fetch_word Ubsan.M.loaded_segments (0x15d74 : word) = Some W_15d74.
Proof. vm_refl. Qed.
Lemma D_15d74 : decode_any W_15d74 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d78 : bv 32 := 0x45c50913.
Lemma F_15d78 : fetch_word Ubsan.M.loaded_segments (0x15d78 : word) = Some W_15d78.
Proof. vm_refl. Qed.
Lemma D_15d78 : decode_any W_15d78 = Some (OpImm ALU_ADD 18 10 1116, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d7c : bv 32 := 0x00490413.
Lemma F_15d7c : fetch_word Ubsan.M.loaded_segments (0x15d7c : word) = Some W_15d7c.
Proof. vm_refl. Qed.
Lemma D_15d7c : decode_any W_15d7c = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d80 : bv 32 := 0x00040513.
Lemma F_15d80 : fetch_word Ubsan.M.loaded_segments (0x15d80 : word) = Some W_15d80.
Proof. vm_refl. Qed.
Lemma D_15d80 : decode_any W_15d80 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d84 : bv 32 := 0x3f9070ef.
Lemma F_15d84 : fetch_word Ubsan.M.loaded_segments (0x15d84 : word) = Some W_15d84.
Proof. vm_refl. Qed.
Lemma D_15d84 : decode_any W_15d84 = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d88 : bv 32 := 0x01093503.
Lemma F_15d88 : fetch_word Ubsan.M.loaded_segments (0x15d88 : word) = Some W_15d88.
Proof. vm_refl. Qed.
Lemma D_15d88 : decode_any W_15d88 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d8c : bv 32 := 0x06050863.
Lemma F_15d8c : fetch_word Ubsan.M.loaded_segments (0x15d8c : word) = Some W_15d8c.
Proof. vm_refl. Qed.
Lemma D_15d8c : decode_any W_15d8c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d90 : bv 32 := 0x00892583.
Lemma F_15d90 : fetch_word Ubsan.M.loaded_segments (0x15d90 : word) = Some W_15d90.
Proof. vm_refl. Qed.
Lemma D_15d90 : decode_any W_15d90 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d94 : bv 32 := 0x0180006f.
Lemma F_15d94 : fetch_word Ubsan.M.loaded_segments (0x15d94 : word) = Some W_15d94.
Proof. vm_refl. Qed.
Lemma D_15d94 : decode_any W_15d94 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d98 : bv 32 := 0x00053503.
Lemma F_15d98 : fetch_word Ubsan.M.loaded_segments (0x15d98 : word) = Some W_15d98.
Proof. vm_refl. Qed.
Lemma D_15d98 : decode_any W_15d98 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d9c : bv 32 := 0x02000593.
Lemma F_15d9c : fetch_word Ubsan.M.loaded_segments (0x15d9c : word) = Some W_15d9c.
Proof. vm_refl. Qed.
Lemma D_15d9c : decode_any W_15d9c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15da0 : bv 32 := 0x00b92423.
Lemma F_15da0 : fetch_word Ubsan.M.loaded_segments (0x15da0 : word) = Some W_15da0.
Proof. vm_refl. Qed.
Lemma D_15da0 : decode_any W_15da0 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15da4 : bv 32 := 0x00a93823.
Lemma F_15da4 : fetch_word Ubsan.M.loaded_segments (0x15da4 : word) = Some W_15da4.
Proof. vm_refl. Qed.
Lemma D_15da4 : decode_any W_15da4 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15da8 : bv 32 := 0x04050a63.
Lemma F_15da8 : fetch_word Ubsan.M.loaded_segments (0x15da8 : word) = Some W_15da8.
Proof. vm_refl. Qed.
Lemma D_15da8 : decode_any W_15da8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dac : bv 32 := 0xfff5861b.
Lemma F_15dac : fetch_word Ubsan.M.loaded_segments (0x15dac : word) = Some W_15dac.
Proof. vm_refl. Qed.
Lemma D_15dac : decode_any W_15dac = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15db0 : bv 32 := 0x00c92423.
Lemma F_15db0 : fetch_word Ubsan.M.loaded_segments (0x15db0 : word) = Some W_15db0.
Proof. vm_refl. Qed.
Lemma D_15db0 : decode_any W_15db0 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15db4 : bv 32 := 0xfeb052e3.
Lemma F_15db4 : fetch_word Ubsan.M.loaded_segments (0x15db4 : word) = Some W_15db4.
Proof. vm_refl. Qed.
Lemma D_15db4 : decode_any W_15db4 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_15db8 : bv 32 := 0x01093503.
Lemma F_15db8 : fetch_word Ubsan.M.loaded_segments (0x15db8 : word) = Some W_15db8.
Proof. vm_refl. Qed.
Lemma D_15db8 : decode_any W_15db8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dbc : bv 32 := 0x00361613.
Lemma F_15dbc : fetch_word Ubsan.M.loaded_segments (0x15dbc : word) = Some W_15dbc.
Proof. vm_refl. Qed.
Lemma D_15dbc : decode_any W_15dbc = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dc0 : bv 32 := 0x00c50533.
Lemma F_15dc0 : fetch_word Ubsan.M.loaded_segments (0x15dc0 : word) = Some W_15dc0.
Proof. vm_refl. Qed.
Lemma D_15dc0 : decode_any W_15dc0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dc4 : bv 32 := 0x00853983.
Lemma F_15dc4 : fetch_word Ubsan.M.loaded_segments (0x15dc4 : word) = Some W_15dc4.
Proof. vm_refl. Qed.
Lemma D_15dc4 : decode_any W_15dc4 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dc8 : bv 32 := 0x10853483.
Lemma F_15dc8 : fetch_word Ubsan.M.loaded_segments (0x15dc8 : word) = Some W_15dc8.
Proof. vm_refl. Qed.
Lemma D_15dc8 : decode_any W_15dc8 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dcc : bv 32 := 0x00040513.
Lemma F_15dcc : fetch_word Ubsan.M.loaded_segments (0x15dcc : word) = Some W_15dcc.
Proof. vm_refl. Qed.
Lemma D_15dcc : decode_any W_15dcc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dd0 : bv 32 := 0x635070ef.
Lemma F_15dd0 : fetch_word Ubsan.M.loaded_segments (0x15dd0 : word) = Some W_15dd0.
Proof. vm_refl. Qed.
Lemma D_15dd0 : decode_any W_15dd0 = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dd4 : bv 32 := 0x00048513.
Lemma F_15dd4 : fetch_word Ubsan.M.loaded_segments (0x15dd4 : word) = Some W_15dd4.
Proof. vm_refl. Qed.
Lemma D_15dd4 : decode_any W_15dd4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dd8 : bv 32 := 0x000980e7.
Lemma F_15dd8 : fetch_word Ubsan.M.loaded_segments (0x15dd8 : word) = Some W_15dd8.
Proof. vm_refl. Qed.
Lemma D_15dd8 : decode_any W_15dd8 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ddc : bv 32 := 0x00040513.
Lemma F_15ddc : fetch_word Ubsan.M.loaded_segments (0x15ddc : word) = Some W_15ddc.
Proof. vm_refl. Qed.
Lemma D_15ddc : decode_any W_15ddc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15de0 : bv 32 := 0x39d070ef.
Lemma F_15de0 : fetch_word Ubsan.M.loaded_segments (0x15de0 : word) = Some W_15de0.
Proof. vm_refl. Qed.
Lemma D_15de0 : decode_any W_15de0 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_15de4 : bv 32 := 0x00892503.
Lemma F_15de4 : fetch_word Ubsan.M.loaded_segments (0x15de4 : word) = Some W_15de4.
Proof. vm_refl. Qed.
Lemma D_15de4 : decode_any W_15de4 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15de8 : bv 32 := 0xfff5061b.
Lemma F_15de8 : fetch_word Ubsan.M.loaded_segments (0x15de8 : word) = Some W_15de8.
Proof. vm_refl. Qed.
Lemma D_15de8 : decode_any W_15de8 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dec : bv 32 := 0x00c92423.
Lemma F_15dec : fetch_word Ubsan.M.loaded_segments (0x15dec : word) = Some W_15dec.
Proof. vm_refl. Qed.
Lemma D_15dec : decode_any W_15dec = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15df0 : bv 32 := 0xfca044e3.
Lemma F_15df0 : fetch_word Ubsan.M.loaded_segments (0x15df0 : word) = Some W_15df0.
Proof. vm_refl. Qed.
Lemma D_15df0 : decode_any W_15df0 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_15df4 : bv 32 := 0x01093503.
Lemma F_15df4 : fetch_word Ubsan.M.loaded_segments (0x15df4 : word) = Some W_15df4.
Proof. vm_refl. Qed.
Lemma D_15df4 : decode_any W_15df4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15df8 : bv 32 := 0xfa1ff06f.
Lemma F_15df8 : fetch_word Ubsan.M.loaded_segments (0x15df8 : word) = Some W_15df8.
Proof. vm_refl. Qed.
Lemma D_15df8 : decode_any W_15df8 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dfc : bv 32 := 0x00100513.
Lemma F_15dfc : fetch_word Ubsan.M.loaded_segments (0x15dfc : word) = Some W_15dfc.
Proof. vm_refl. Qed.
Lemma D_15dfc : decode_any W_15dfc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e00 : bv 32 := 0x00a90023.
Lemma F_15e00 : fetch_word Ubsan.M.loaded_segments (0x15e00 : word) = Some W_15e00.
Proof. vm_refl. Qed.
Lemma D_15e00 : decode_any W_15e00 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e04 : bv 32 := 0x00040513.
Lemma F_15e04 : fetch_word Ubsan.M.loaded_segments (0x15e04 : word) = Some W_15e04.
Proof. vm_refl. Qed.
Lemma D_15e04 : decode_any W_15e04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e08 : bv 32 := 0x02813083.
Lemma F_15e08 : fetch_word Ubsan.M.loaded_segments (0x15e08 : word) = Some W_15e08.
Proof. vm_refl. Qed.
Lemma D_15e08 : decode_any W_15e08 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e0c : bv 32 := 0x02013403.
Lemma F_15e0c : fetch_word Ubsan.M.loaded_segments (0x15e0c : word) = Some W_15e0c.
Proof. vm_refl. Qed.
Lemma D_15e0c : decode_any W_15e0c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e10 : bv 32 := 0x01813483.
Lemma F_15e10 : fetch_word Ubsan.M.loaded_segments (0x15e10 : word) = Some W_15e10.
Proof. vm_refl. Qed.
Lemma D_15e10 : decode_any W_15e10 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e14 : bv 32 := 0x01013903.
Lemma F_15e14 : fetch_word Ubsan.M.loaded_segments (0x15e14 : word) = Some W_15e14.
Proof. vm_refl. Qed.
Lemma D_15e14 : decode_any W_15e14 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e18 : bv 32 := 0x00813983.
Lemma F_15e18 : fetch_word Ubsan.M.loaded_segments (0x15e18 : word) = Some W_15e18.
Proof. vm_refl. Qed.
Lemma D_15e18 : decode_any W_15e18 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e1c : bv 32 := 0x03010113.
Lemma F_15e1c : fetch_word Ubsan.M.loaded_segments (0x15e1c : word) = Some W_15e1c.
Proof. vm_refl. Qed.
Lemma D_15e1c : decode_any W_15e1c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e20 : bv 32 := 0x5e50706f.
Lemma F_15e20 : fetch_word Ubsan.M.loaded_segments (0x15e20 : word) = Some W_15e20.
Proof. vm_refl. Qed.
Lemma D_15e20 : decode_any W_15e20 = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e24 : bv 32 := 0x00008067.
Lemma F_15e24 : fetch_word Ubsan.M.loaded_segments (0x15e24 : word) = Some W_15e24.
Proof. vm_refl. Qed.
Lemma D_15e24 : decode_any W_15e24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e28 : bv 32 := 0xfd010113.
Lemma F_15e28 : fetch_word Ubsan.M.loaded_segments (0x15e28 : word) = Some W_15e28.
Proof. vm_refl. Qed.
Lemma D_15e28 : decode_any W_15e28 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e2c : bv 32 := 0x02113423.
Lemma F_15e2c : fetch_word Ubsan.M.loaded_segments (0x15e2c : word) = Some W_15e2c.
Proof. vm_refl. Qed.
Lemma D_15e2c : decode_any W_15e2c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e30 : bv 32 := 0x02813023.
Lemma F_15e30 : fetch_word Ubsan.M.loaded_segments (0x15e30 : word) = Some W_15e30.
Proof. vm_refl. Qed.
Lemma D_15e30 : decode_any W_15e30 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e34 : bv 32 := 0x00913c23.
Lemma F_15e34 : fetch_word Ubsan.M.loaded_segments (0x15e34 : word) = Some W_15e34.
Proof. vm_refl. Qed.
Lemma D_15e34 : decode_any W_15e34 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e38 : bv 32 := 0x01213823.
Lemma F_15e38 : fetch_word Ubsan.M.loaded_segments (0x15e38 : word) = Some W_15e38.
Proof. vm_refl. Qed.
Lemma D_15e38 : decode_any W_15e38 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e3c : bv 32 := 0x01313423.
Lemma F_15e3c : fetch_word Ubsan.M.loaded_segments (0x15e3c : word) = Some W_15e3c.
Proof. vm_refl. Qed.
Lemma D_15e3c : decode_any W_15e3c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e40 : bv 32 := 0x00050493.
Lemma F_15e40 : fetch_word Ubsan.M.loaded_segments (0x15e40 : word) = Some W_15e40.
Proof. vm_refl. Qed.
Lemma D_15e40 : decode_any W_15e40 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e44 : bv 32 := 0x0003a517.
Lemma F_15e44 : fetch_word Ubsan.M.loaded_segments (0x15e44 : word) = Some W_15e44.
Proof. vm_refl. Qed.
Lemma D_15e44 : decode_any W_15e44 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e48 : bv 32 := 0x38c50993.
Lemma F_15e48 : fetch_word Ubsan.M.loaded_segments (0x15e48 : word) = Some W_15e48.
Proof. vm_refl. Qed.
Lemma D_15e48 : decode_any W_15e48 = Some (OpImm ALU_ADD 19 10 908, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e4c : bv 32 := 0x00498413.
Lemma F_15e4c : fetch_word Ubsan.M.loaded_segments (0x15e4c : word) = Some W_15e4c.
Proof. vm_refl. Qed.
Lemma D_15e4c : decode_any W_15e4c = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e50 : bv 32 := 0x00040513.
Lemma F_15e50 : fetch_word Ubsan.M.loaded_segments (0x15e50 : word) = Some W_15e50.
Proof. vm_refl. Qed.
Lemma D_15e50 : decode_any W_15e50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e54 : bv 32 := 0x329070ef.
Lemma F_15e54 : fetch_word Ubsan.M.loaded_segments (0x15e54 : word) = Some W_15e54.
Proof. vm_refl. Qed.
Lemma D_15e54 : decode_any W_15e54 = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e58 : bv 32 := 0x0009c503.
Lemma F_15e58 : fetch_word Ubsan.M.loaded_segments (0x15e58 : word) = Some W_15e58.
Proof. vm_refl. Qed.
Lemma D_15e58 : decode_any W_15e58 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e5c : bv 32 := 0xfff00913.
Lemma F_15e5c : fetch_word Ubsan.M.loaded_segments (0x15e5c : word) = Some W_15e5c.
Proof. vm_refl. Qed.
Lemma D_15e5c : decode_any W_15e5c = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e60 : bv 32 := 0x06051263.
Lemma F_15e60 : fetch_word Ubsan.M.loaded_segments (0x15e60 : word) = Some W_15e60.
Proof. vm_refl. Qed.
Lemma D_15e60 : decode_any W_15e60 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e64 : bv 32 := 0x0109b503.
Lemma F_15e64 : fetch_word Ubsan.M.loaded_segments (0x15e64 : word) = Some W_15e64.
Proof. vm_refl. Qed.
Lemma D_15e64 : decode_any W_15e64 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e68 : bv 32 := 0x00051663.
Lemma F_15e68 : fetch_word Ubsan.M.loaded_segments (0x15e68 : word) = Some W_15e68.
Proof. vm_refl. Qed.
Lemma D_15e68 : decode_any W_15e68 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e6c : bv 32 := 0x01898513.
Lemma F_15e6c : fetch_word Ubsan.M.loaded_segments (0x15e6c : word) = Some W_15e6c.
Proof. vm_refl. Qed.
Lemma D_15e6c : decode_any W_15e6c = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e70 : bv 32 := 0x00a9b823.
Lemma F_15e70 : fetch_word Ubsan.M.loaded_segments (0x15e70 : word) = Some W_15e70.
Proof. vm_refl. Qed.
Lemma D_15e70 : decode_any W_15e70 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e74 : bv 32 := 0x0089a583.
Lemma F_15e74 : fetch_word Ubsan.M.loaded_segments (0x15e74 : word) = Some W_15e74.
Proof. vm_refl. Qed.
Lemma D_15e74 : decode_any W_15e74 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e78 : bv 32 := 0x02000613.
Lemma F_15e78 : fetch_word Ubsan.M.loaded_segments (0x15e78 : word) = Some W_15e78.
Proof. vm_refl. Qed.
Lemma D_15e78 : decode_any W_15e78 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e7c : bv 32 := 0x02c59263.
Lemma F_15e7c : fetch_word Ubsan.M.loaded_segments (0x15e7c : word) = Some W_15e7c.
Proof. vm_refl. Qed.
Lemma D_15e7c : decode_any W_15e7c = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e80 : bv 32 := 0x20800513.
Lemma F_15e80 : fetch_word Ubsan.M.loaded_segments (0x15e80 : word) = Some W_15e80.
Proof. vm_refl. Qed.
Lemma D_15e80 : decode_any W_15e80 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e84 : bv 32 := 0x00100593.
Lemma F_15e84 : fetch_word Ubsan.M.loaded_segments (0x15e84 : word) = Some W_15e84.
Proof. vm_refl. Qed.
Lemma D_15e84 : decode_any W_15e84 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e88 : bv 32 := 0x3f4000ef.
Lemma F_15e88 : fetch_word Ubsan.M.loaded_segments (0x15e88 : word) = Some W_15e88.
Proof. vm_refl. Qed.
Lemma D_15e88 : decode_any W_15e88 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e8c : bv 32 := 0x02050c63.
Lemma F_15e8c : fetch_word Ubsan.M.loaded_segments (0x15e8c : word) = Some W_15e8c.
Proof. vm_refl. Qed.
Lemma D_15e8c : decode_any W_15e8c = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e90 : bv 32 := 0x00000593.
Lemma F_15e90 : fetch_word Ubsan.M.loaded_segments (0x15e90 : word) = Some W_15e90.
Proof. vm_refl. Qed.
Lemma D_15e90 : decode_any W_15e90 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e94 : bv 32 := 0x0109b603.
Lemma F_15e94 : fetch_word Ubsan.M.loaded_segments (0x15e94 : word) = Some W_15e94.
Proof. vm_refl. Qed.
Lemma D_15e94 : decode_any W_15e94 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e98 : bv 32 := 0x00c53023.
Lemma F_15e98 : fetch_word Ubsan.M.loaded_segments (0x15e98 : word) = Some W_15e98.
Proof. vm_refl. Qed.
Lemma D_15e98 : decode_any W_15e98 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e9c : bv 32 := 0x00a9b823.
Lemma F_15e9c : fetch_word Ubsan.M.loaded_segments (0x15e9c : word) = Some W_15e9c.
Proof. vm_refl. Qed.
Lemma D_15e9c : decode_any W_15e9c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ea0 : bv 32 := 0x00000913.
Lemma F_15ea0 : fetch_word Ubsan.M.loaded_segments (0x15ea0 : word) = Some W_15ea0.
Proof. vm_refl. Qed.
Lemma D_15ea0 : decode_any W_15ea0 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ea4 : bv 32 := 0x00359613.
Lemma F_15ea4 : fetch_word Ubsan.M.loaded_segments (0x15ea4 : word) = Some W_15ea4.
Proof. vm_refl. Qed.
Lemma D_15ea4 : decode_any W_15ea4 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ea8 : bv 32 := 0x00c50533.
Lemma F_15ea8 : fetch_word Ubsan.M.loaded_segments (0x15ea8 : word) = Some W_15ea8.
Proof. vm_refl. Qed.
Lemma D_15ea8 : decode_any W_15ea8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eac : bv 32 := 0x00000617.
Lemma F_15eac : fetch_word Ubsan.M.loaded_segments (0x15eac : word) = Some W_15eac.
Proof. vm_refl. Qed.
Lemma D_15eac : decode_any W_15eac = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eb0 : bv 32 := 0x00158593.
Lemma F_15eb0 : fetch_word Ubsan.M.loaded_segments (0x15eb0 : word) = Some W_15eb0.
Proof. vm_refl. Qed.
Lemma D_15eb0 : decode_any W_15eb0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eb4 : bv 32 := 0x04060613.
Lemma F_15eb4 : fetch_word Ubsan.M.loaded_segments (0x15eb4 : word) = Some W_15eb4.
Proof. vm_refl. Qed.
Lemma D_15eb4 : decode_any W_15eb4 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eb8 : bv 32 := 0x00c53423.
Lemma F_15eb8 : fetch_word Ubsan.M.loaded_segments (0x15eb8 : word) = Some W_15eb8.
Proof. vm_refl. Qed.
Lemma D_15eb8 : decode_any W_15eb8 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ebc : bv 32 := 0x10953423.
Lemma F_15ebc : fetch_word Ubsan.M.loaded_segments (0x15ebc : word) = Some W_15ebc.
Proof. vm_refl. Qed.
Lemma D_15ebc : decode_any W_15ebc = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec0 : bv 32 := 0x00b9a423.
Lemma F_15ec0 : fetch_word Ubsan.M.loaded_segments (0x15ec0 : word) = Some W_15ec0.
Proof. vm_refl. Qed.
Lemma D_15ec0 : decode_any W_15ec0 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec4 : bv 32 := 0x00040513.
Lemma F_15ec4 : fetch_word Ubsan.M.loaded_segments (0x15ec4 : word) = Some W_15ec4.
Proof. vm_refl. Qed.
Lemma D_15ec4 : decode_any W_15ec4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec8 : bv 32 := 0x53d070ef.
Lemma F_15ec8 : fetch_word Ubsan.M.loaded_segments (0x15ec8 : word) = Some W_15ec8.
Proof. vm_refl. Qed.
Lemma D_15ec8 : decode_any W_15ec8 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ecc : bv 32 := 0x00090513.
Lemma F_15ecc : fetch_word Ubsan.M.loaded_segments (0x15ecc : word) = Some W_15ecc.
Proof. vm_refl. Qed.
Lemma D_15ecc : decode_any W_15ecc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed0 : bv 32 := 0x02813083.
Lemma F_15ed0 : fetch_word Ubsan.M.loaded_segments (0x15ed0 : word) = Some W_15ed0.
Proof. vm_refl. Qed.
Lemma D_15ed0 : decode_any W_15ed0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed4 : bv 32 := 0x02013403.
Lemma F_15ed4 : fetch_word Ubsan.M.loaded_segments (0x15ed4 : word) = Some W_15ed4.
Proof. vm_refl. Qed.
Lemma D_15ed4 : decode_any W_15ed4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed8 : bv 32 := 0x01813483.
Lemma F_15ed8 : fetch_word Ubsan.M.loaded_segments (0x15ed8 : word) = Some W_15ed8.
Proof. vm_refl. Qed.
Lemma D_15ed8 : decode_any W_15ed8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15edc : bv 32 := 0x01013903.
Lemma F_15edc : fetch_word Ubsan.M.loaded_segments (0x15edc : word) = Some W_15edc.
Proof. vm_refl. Qed.
Lemma D_15edc : decode_any W_15edc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee0 : bv 32 := 0x00813983.
Lemma F_15ee0 : fetch_word Ubsan.M.loaded_segments (0x15ee0 : word) = Some W_15ee0.
Proof. vm_refl. Qed.
Lemma D_15ee0 : decode_any W_15ee0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee4 : bv 32 := 0x03010113.
Lemma F_15ee4 : fetch_word Ubsan.M.loaded_segments (0x15ee4 : word) = Some W_15ee4.
Proof. vm_refl. Qed.
Lemma D_15ee4 : decode_any W_15ee4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee8 : bv 32 := 0x00008067.
Lemma F_15ee8 : fetch_word Ubsan.M.loaded_segments (0x15ee8 : word) = Some W_15ee8.
Proof. vm_refl. Qed.
Lemma D_15ee8 : decode_any W_15ee8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eec : bv 32 := 0x00050067.
Lemma F_15eec : fetch_word Ubsan.M.loaded_segments (0x15eec : word) = Some W_15eec.
Proof. vm_refl. Qed.
Lemma D_15eec : decode_any W_15eec = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef0 : bv 32 := 0x00008067.
Lemma F_15ef0 : fetch_word Ubsan.M.loaded_segments (0x15ef0 : word) = Some W_15ef0.
Proof. vm_refl. Qed.
Lemma D_15ef0 : decode_any W_15ef0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef4 : bv 32 := 0xfe010113.
Lemma F_15ef4 : fetch_word Ubsan.M.loaded_segments (0x15ef4 : word) = Some W_15ef4.
Proof. vm_refl. Qed.
Lemma D_15ef4 : decode_any W_15ef4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef8 : bv 32 := 0x00113c23.
Lemma F_15ef8 : fetch_word Ubsan.M.loaded_segments (0x15ef8 : word) = Some W_15ef8.
Proof. vm_refl. Qed.
Lemma D_15ef8 : decode_any W_15ef8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15efc : bv 32 := 0x00813823.
Lemma F_15efc : fetch_word Ubsan.M.loaded_segments (0x15efc : word) = Some W_15efc.
Proof. vm_refl. Qed.
Lemma D_15efc : decode_any W_15efc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f00 : bv 32 := 0x00913423.
Lemma F_15f00 : fetch_word Ubsan.M.loaded_segments (0x15f00 : word) = Some W_15f00.
Proof. vm_refl. Qed.
Lemma D_15f00 : decode_any W_15f00 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f04 : bv 32 := 0x00009517.
Lemma F_15f04 : fetch_word Ubsan.M.loaded_segments (0x15f04 : word) = Some W_15f04.
Proof. vm_refl. Qed.
Lemma D_15f04 : decode_any W_15f04 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f08 : bv 32 := 0x00009597.
Lemma F_15f08 : fetch_word Ubsan.M.loaded_segments (0x15f08 : word) = Some W_15f08.
Proof. vm_refl. Qed.
Lemma D_15f08 : decode_any W_15f08 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f0c : bv 32 := 0xefc53503.
Lemma F_15f0c : fetch_word Ubsan.M.loaded_segments (0x15f0c : word) = Some W_15f0c.
Proof. vm_refl. Qed.
Lemma D_15f0c : decode_any W_15f0c = Some (Load SZ8 true 10 10 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f10 : bv 32 := 0xf005b403.
Lemma F_15f10 : fetch_word Ubsan.M.loaded_segments (0x15f10 : word) = Some W_15f10.
Proof. vm_refl. Qed.
Lemma D_15f10 : decode_any W_15f10 = Some (Load SZ8 true 8 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f14 : bv 32 := 0x00a47c63.
Lemma F_15f14 : fetch_word Ubsan.M.loaded_segments (0x15f14 : word) = Some W_15f14.
Proof. vm_refl. Qed.
Lemma D_15f14 : decode_any W_15f14 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f18 : bv 32 := 0xff853583.
Lemma F_15f18 : fetch_word Ubsan.M.loaded_segments (0x15f18 : word) = Some W_15f18.
Proof. vm_refl. Qed.
Lemma D_15f18 : decode_any W_15f18 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f1c : bv 32 := 0xff850493.
Lemma F_15f1c : fetch_word Ubsan.M.loaded_segments (0x15f1c : word) = Some W_15f1c.
Proof. vm_refl. Qed.
Lemma D_15f1c : decode_any W_15f1c = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f20 : bv 32 := 0x000580e7.
Lemma F_15f20 : fetch_word Ubsan.M.loaded_segments (0x15f20 : word) = Some W_15f20.
Proof. vm_refl. Qed.
Lemma D_15f20 : decode_any W_15f20 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f24 : bv 32 := 0x00048513.
Lemma F_15f24 : fetch_word Ubsan.M.loaded_segments (0x15f24 : word) = Some W_15f24.
Proof. vm_refl. Qed.
Lemma D_15f24 : decode_any W_15f24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f28 : bv 32 := 0xfe9468e3.
Lemma F_15f28 : fetch_word Ubsan.M.loaded_segments (0x15f28 : word) = Some W_15f28.
Proof. vm_refl. Qed.
Lemma D_15f28 : decode_any W_15f28 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f2c : bv 32 := 0x01813083.
Lemma F_15f2c : fetch_word Ubsan.M.loaded_segments (0x15f2c : word) = Some W_15f2c.
Proof. vm_refl. Qed.
Lemma D_15f2c : decode_any W_15f2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f30 : bv 32 := 0x01013403.
Lemma F_15f30 : fetch_word Ubsan.M.loaded_segments (0x15f30 : word) = Some W_15f30.
Proof. vm_refl. Qed.
Lemma D_15f30 : decode_any W_15f30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f34 : bv 32 := 0x00813483.
Lemma F_15f34 : fetch_word Ubsan.M.loaded_segments (0x15f34 : word) = Some W_15f34.
Proof. vm_refl. Qed.
Lemma D_15f34 : decode_any W_15f34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f38 : bv 32 := 0x02010113.
Lemma F_15f38 : fetch_word Ubsan.M.loaded_segments (0x15f38 : word) = Some W_15f38.
Proof. vm_refl. Qed.
Lemma D_15f38 : decode_any W_15f38 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f3c : bv 32 := 0xfb5ff06f.
Lemma F_15f3c : fetch_word Ubsan.M.loaded_segments (0x15f3c : word) = Some W_15f3c.
Proof. vm_refl. Qed.
Lemma D_15f3c : decode_any W_15f3c = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f40 : bv 32 := 0xff010113.
Lemma F_15f40 : fetch_word Ubsan.M.loaded_segments (0x15f40 : word) = Some W_15f40.
Proof. vm_refl. Qed.
Lemma D_15f40 : decode_any W_15f40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f44 : bv 32 := 0x00113423.
Lemma F_15f44 : fetch_word Ubsan.M.loaded_segments (0x15f44 : word) = Some W_15f44.
Proof. vm_refl. Qed.
Lemma D_15f44 : decode_any W_15f44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f48 : bv 32 := 0x00813023.
Lemma F_15f48 : fetch_word Ubsan.M.loaded_segments (0x15f48 : word) = Some W_15f48.
Proof. vm_refl. Qed.
Lemma D_15f48 : decode_any W_15f48 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f4c : bv 32 := 0x00000593.
Lemma F_15f4c : fetch_word Ubsan.M.loaded_segments (0x15f4c : word) = Some W_15f4c.
Proof. vm_refl. Qed.
Lemma D_15f4c : decode_any W_15f4c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f50 : bv 32 := 0x00020613.
Lemma F_15f50 : fetch_word Ubsan.M.loaded_segments (0x15f50 : word) = Some W_15f50.
Proof. vm_refl. Qed.
Lemma D_15f50 : decode_any W_15f50 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f54 : bv 32 := 0xf5862603.
Lemma F_15f54 : fetch_word Ubsan.M.loaded_segments (0x15f54 : word) = Some W_15f54.
Proof. vm_refl. Qed.
Lemma D_15f54 : decode_any W_15f54 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f58 : bv 32 := 0x0003a697.
Lemma F_15f58 : fetch_word Ubsan.M.loaded_segments (0x15f58 : word) = Some W_15f58.
Proof. vm_refl. Qed.
Lemma D_15f58 : decode_any W_15f58 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f5c : bv 32 := 0x49868693.
Lemma F_15f5c : fetch_word Ubsan.M.loaded_segments (0x15f5c : word) = Some W_15f5c.
Proof. vm_refl. Qed.
Lemma D_15f5c : decode_any W_15f5c = Some (OpImm ALU_ADD 13 13 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f60 : bv 32 := 0x1606a72f.
Lemma F_15f60 : fetch_word Ubsan.M.loaded_segments (0x15f60 : word) = Some W_15f60.
Proof. vm_refl. Qed.
Lemma D_15f60 : decode_any W_15f60 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f64 : bv 32 := 0x00b71663.
Lemma F_15f64 : fetch_word Ubsan.M.loaded_segments (0x15f64 : word) = Some W_15f64.
Proof. vm_refl. Qed.
Lemma D_15f64 : decode_any W_15f64 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f68 : bv 32 := 0x1ec6a7af.
Lemma F_15f68 : fetch_word Ubsan.M.loaded_segments (0x15f68 : word) = Some W_15f68.
Proof. vm_refl. Qed.
Lemma D_15f68 : decode_any W_15f68 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f6c : bv 32 := 0xfe079ae3.
Lemma F_15f6c : fetch_word Ubsan.M.loaded_segments (0x15f6c : word) = Some W_15f6c.
Proof. vm_refl. Qed.
Lemma D_15f6c : decode_any W_15f6c = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f70 : bv 32 := 0x0007059b.
Lemma F_15f70 : fetch_word Ubsan.M.loaded_segments (0x15f70 : word) = Some W_15f70.
Proof. vm_refl. Qed.
Lemma D_15f70 : decode_any W_15f70 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f74 : bv 32 := 0x02c58263.
Lemma F_15f74 : fetch_word Ubsan.M.loaded_segments (0x15f74 : word) = Some W_15f74.
Proof. vm_refl. Qed.
Lemma D_15f74 : decode_any W_15f74 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f78 : bv 32 := 0x02058263.
Lemma F_15f78 : fetch_word Ubsan.M.loaded_segments (0x15f78 : word) = Some W_15f78.
Proof. vm_refl. Qed.
Lemma D_15f78 : decode_any W_15f78 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f7c : bv 32 := 0x04900893.
Lemma F_15f7c : fetch_word Ubsan.M.loaded_segments (0x15f7c : word) = Some W_15f7c.
Proof. vm_refl. Qed.
Lemma D_15f7c : decode_any W_15f7c = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f80 : bv 32 := 0x00000593.
Lemma F_15f80 : fetch_word Ubsan.M.loaded_segments (0x15f80 : word) = Some W_15f80.
Proof. vm_refl. Qed.
Lemma D_15f80 : decode_any W_15f80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f84 : bv 32 := 0x00000613.
Lemma F_15f84 : fetch_word Ubsan.M.loaded_segments (0x15f84 : word) = Some W_15f84.
Proof. vm_refl. Qed.
Lemma D_15f84 : decode_any W_15f84 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f88 : bv 32 := 0x00000693.
Lemma F_15f88 : fetch_word Ubsan.M.loaded_segments (0x15f88 : word) = Some W_15f88.
Proof. vm_refl. Qed.
Lemma D_15f88 : decode_any W_15f88 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f8c : bv 32 := 0x00000513.
Lemma F_15f8c : fetch_word Ubsan.M.loaded_segments (0x15f8c : word) = Some W_15f8c.
Proof. vm_refl. Qed.
Lemma D_15f8c : decode_any W_15f8c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f90 : bv 32 := 0x00000073.
Lemma F_15f90 : fetch_word Ubsan.M.loaded_segments (0x15f90 : word) = Some W_15f90.
Proof. vm_refl. Qed.
Lemma E_15f90 : is_ecall W_15f90 = true.
Proof. vm_refl. Qed.

Definition W_15f94 : bv 32 := 0xff9ff06f.
Lemma F_15f94 : fetch_word Ubsan.M.loaded_segments (0x15f94 : word) = Some W_15f94.
Proof. vm_refl. Qed.
Lemma D_15f94 : decode_any W_15f94 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f98 : bv 32 := 0x00000023.
Lemma F_15f98 : fetch_word Ubsan.M.loaded_segments (0x15f98 : word) = Some W_15f98.
Proof. vm_refl. Qed.
Lemma D_15f98 : decode_any W_15f98 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f9c : bv 32 := 0x00050413.
Lemma F_15f9c : fetch_word Ubsan.M.loaded_segments (0x15f9c : word) = Some W_15f9c.
Proof. vm_refl. Qed.
Lemma D_15f9c : decode_any W_15f9c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15fa0 : bv 32 := 0xdbdff0ef.
Lemma F_15fa0 : fetch_word Ubsan.M.loaded_segments (0x15fa0 : word) = Some W_15fa0.
Proof. vm_refl. Qed.
Lemma D_15fa0 : decode_any W_15fa0 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_15fa4 : bv 32 := 0xf51ff0ef.
Lemma F_15fa4 : fetch_word Ubsan.M.loaded_segments (0x15fa4 : word) = Some W_15fa4.
Proof. vm_refl. Qed.
Lemma D_15fa4 : decode_any W_15fa4 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_15fa8 : bv 32 := 0x160020ef.
Lemma F_15fa8 : fetch_word Ubsan.M.loaded_segments (0x15fa8 : word) = Some W_15fa8.
Proof. vm_refl. Qed.
Lemma D_15fa8 : decode_any W_15fa8 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_15fac : bv 32 := 0x00040513.
Lemma F_15fac : fetch_word Ubsan.M.loaded_segments (0x15fac : word) = Some W_15fac.
Proof. vm_refl. Qed.
Lemma D_15fac : decode_any W_15fac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15fb0 : bv 32 := 0xd91ff0ef.
Lemma F_15fb0 : fetch_word Ubsan.M.loaded_segments (0x15fb0 : word) = Some W_15fb0.
Proof. vm_refl. Qed.
Lemma D_15fb0 : decode_any W_15fb0 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d97c : bv 32 := 0x00033597.
Lemma F_1d97c : fetch_word Ubsan.M.loaded_segments (0x1d97c : word) = Some W_1d97c.
Proof. vm_refl. Qed.
Lemma D_1d97c : decode_any W_1d97c = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d980 : bv 32 := 0xa9f58683.
Lemma F_1d980 : fetch_word Ubsan.M.loaded_segments (0x1d980 : word) = Some W_1d980.
Proof. vm_refl. Qed.
Lemma D_1d980 : decode_any W_1d980 = Some (Load SZ1 true 13 11 2719, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d984 : bv 32 := 0x1e068863.
Lemma F_1d984 : fetch_word Ubsan.M.loaded_segments (0x1d984 : word) = Some W_1d984.
Proof. vm_refl. Qed.
Lemma D_1d984 : decode_any W_1d984 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1db74 : bv 32 := 0x00008067.
Lemma F_1db74 : fetch_word Ubsan.M.loaded_segments (0x1db74 : word) = Some W_1db74.
Proof. vm_refl. Qed.
Lemma D_1db74 : decode_any W_1db74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1dc04 : bv 32 := 0x00052583.
Lemma F_1dc04 : fetch_word Ubsan.M.loaded_segments (0x1dc04 : word) = Some W_1dc04.
Proof. vm_refl. Qed.
Lemma D_1dc04 : decode_any W_1dc04 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1dc08 : bv 32 := 0x0005c463.
Lemma F_1dc08 : fetch_word Ubsan.M.loaded_segments (0x1dc08 : word) = Some W_1dc08.
Proof. vm_refl. Qed.
Lemma D_1dc08 : decode_any W_1dc08 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1dc0c : bv 32 := 0x00008067.
Lemma F_1dc0c : fetch_word Ubsan.M.loaded_segments (0x1dc0c : word) = Some W_1dc0c.
Proof. vm_refl. Qed.
Lemma D_1dc0c : decode_any W_1dc0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
