(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.H Require GcFlushS17.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_133fc : bv 32 := 0xffffe517.
Lemma F_133fc : fetch_word Plain.M.loaded_segments (0x133fc : word) = Some W_133fc.
Proof. vm_refl. Qed.
Lemma D_133fc : decode_any W_133fc = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13400 : bv 32 := 0x79c50513.
Lemma F_13400 : fetch_word Plain.M.loaded_segments (0x13400 : word) = Some W_13400.
Proof. vm_refl. Qed.
Lemma D_13400 : decode_any W_13400 = Some (OpImm ALU_ADD 10 10 1948, 4%Z).
Proof. vm_refl. Qed.

Definition W_13404 : bv 32 := 0x0000d597.
Lemma F_13404 : fetch_word Plain.M.loaded_segments (0x13404 : word) = Some W_13404.
Proof. vm_refl. Qed.
Lemma D_13404 : decode_any W_13404 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13408 : bv 32 := 0xfd458593.
Lemma F_13408 : fetch_word Plain.M.loaded_segments (0x13408 : word) = Some W_13408.
Proof. vm_refl. Qed.
Lemma D_13408 : decode_any W_13408 = Some (OpImm ALU_ADD 11 11 4052, 4%Z).
Proof. vm_refl. Qed.

Definition W_1340c : bv 32 := 0x000000ef.
Lemma F_1340c : fetch_word Plain.M.loaded_segments (0x1340c : word) = Some W_1340c.
Proof. vm_refl. Qed.
Lemma D_1340c : decode_any W_1340c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13410 : bv 32 := 0x0040006f.
Lemma F_13410 : fetch_word Plain.M.loaded_segments (0x13410 : word) = Some W_13410.
Proof. vm_refl. Qed.
Lemma D_13410 : decode_any W_13410 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13414 : bv 32 := 0x00813083.
Lemma F_13414 : fetch_word Plain.M.loaded_segments (0x13414 : word) = Some W_13414.
Proof. vm_refl. Qed.
Lemma D_13414 : decode_any W_13414 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13418 : bv 32 := 0x00013403.
Lemma F_13418 : fetch_word Plain.M.loaded_segments (0x13418 : word) = Some W_13418.
Proof. vm_refl. Qed.
Lemma D_13418 : decode_any W_13418 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341c : bv 32 := 0x01010113.
Lemma F_1341c : fetch_word Plain.M.loaded_segments (0x1341c : word) = Some W_1341c.
Proof. vm_refl. Qed.
Lemma D_1341c : decode_any W_1341c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13420 : bv 32 := 0x00008067.
Lemma F_13420 : fetch_word Plain.M.loaded_segments (0x13420 : word) = Some W_13420.
Proof. vm_refl. Qed.
Lemma D_13420 : decode_any W_13420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13424 : bv 32 := 0xff010113.
Lemma F_13424 : fetch_word Plain.M.loaded_segments (0x13424 : word) = Some W_13424.
Proof. vm_refl. Qed.
Lemma D_13424 : decode_any W_13424 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13428 : bv 32 := 0x00113423.
Lemma F_13428 : fetch_word Plain.M.loaded_segments (0x13428 : word) = Some W_13428.
Proof. vm_refl. Qed.
Lemma D_13428 : decode_any W_13428 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1342c : bv 32 := 0x00813023.
Lemma F_1342c : fetch_word Plain.M.loaded_segments (0x1342c : word) = Some W_1342c.
Proof. vm_refl. Qed.
Lemma D_1342c : decode_any W_1342c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13430 : bv 32 := 0x01010413.
Lemma F_13430 : fetch_word Plain.M.loaded_segments (0x13430 : word) = Some W_13430.
Proof. vm_refl. Qed.
Lemma D_13430 : decode_any W_13430 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13434 : bv 32 := 0x0000d517.
Lemma F_13434 : fetch_word Plain.M.loaded_segments (0x13434 : word) = Some W_13434.
Proof. vm_refl. Qed.
Lemma D_13434 : decode_any W_13434 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13438 : bv 32 := 0xfe450513.
Lemma F_13438 : fetch_word Plain.M.loaded_segments (0x13438 : word) = Some W_13438.
Proof. vm_refl. Qed.
Lemma D_13438 : decode_any W_13438 = Some (OpImm ALU_ADD 10 10 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_1343c : bv 32 := 0x00054503.
Lemma F_1343c : fetch_word Plain.M.loaded_segments (0x1343c : word) = Some W_1343c.
Proof. vm_refl. Qed.
Lemma D_1343c : decode_any W_1343c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13440 : bv 32 := 0x00157513.
Lemma F_13440 : fetch_word Plain.M.loaded_segments (0x13440 : word) = Some W_13440.
Proof. vm_refl. Qed.
Lemma D_13440 : decode_any W_13440 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13444 : bv 32 := 0x00050663.
Lemma F_13444 : fetch_word Plain.M.loaded_segments (0x13444 : word) = Some W_13444.
Proof. vm_refl. Qed.
Lemma D_13444 : decode_any W_13444 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13448 : bv 32 := 0x0040006f.
Lemma F_13448 : fetch_word Plain.M.loaded_segments (0x13448 : word) = Some W_13448.
Proof. vm_refl. Qed.
Lemma D_13448 : decode_any W_13448 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1344c : bv 32 := 0x0580006f.
Lemma F_1344c : fetch_word Plain.M.loaded_segments (0x1344c : word) = Some W_1344c.
Proof. vm_refl. Qed.
Lemma D_1344c : decode_any W_1344c = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_13450 : bv 32 := 0x0000d517.
Lemma F_13450 : fetch_word Plain.M.loaded_segments (0x13450 : word) = Some W_13450.
Proof. vm_refl. Qed.
Lemma D_13450 : decode_any W_13450 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13454 : bv 32 := 0xfc850593.
Lemma F_13454 : fetch_word Plain.M.loaded_segments (0x13454 : word) = Some W_13454.
Proof. vm_refl. Qed.
Lemma D_13454 : decode_any W_13454 = Some (OpImm ALU_ADD 11 10 4040, 4%Z).
Proof. vm_refl. Qed.

Definition W_13458 : bv 32 := 0x00100513.
Lemma F_13458 : fetch_word Plain.M.loaded_segments (0x13458 : word) = Some W_13458.
Proof. vm_refl. Qed.
Lemma D_13458 : decode_any W_13458 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1345c : bv 32 := 0x00a58023.
Lemma F_1345c : fetch_word Plain.M.loaded_segments (0x1345c : word) = Some W_1345c.
Proof. vm_refl. Qed.
Lemma D_1345c : decode_any W_1345c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13460 : bv 32 := 0x0000c517.
Lemma F_13460 : fetch_word Plain.M.loaded_segments (0x13460 : word) = Some W_13460.
Proof. vm_refl. Qed.
Lemma D_13460 : decode_any W_13460 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13464 : bv 32 := 0xcc853503.
Lemma F_13464 : fetch_word Plain.M.loaded_segments (0x13464 : word) = Some W_13464.
Proof. vm_refl. Qed.
Lemma D_13464 : decode_any W_13464 = Some (Load SZ8 true 10 10 3272, 4%Z).
Proof. vm_refl. Qed.

Definition W_13468 : bv 32 := 0x00050e63.
Lemma F_13468 : fetch_word Plain.M.loaded_segments (0x13468 : word) = Some W_13468.
Proof. vm_refl. Qed.
Lemma D_13468 : decode_any W_13468 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1346c : bv 32 := 0x0040006f.
Lemma F_1346c : fetch_word Plain.M.loaded_segments (0x1346c : word) = Some W_1346c.
Proof. vm_refl. Qed.
Lemma D_1346c : decode_any W_1346c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13470 : bv 32 := 0x0000d517.
Lemma F_13470 : fetch_word Plain.M.loaded_segments (0x13470 : word) = Some W_13470.
Proof. vm_refl. Qed.
Lemma D_13470 : decode_any W_13470 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13474 : bv 32 := 0xd2850513.
Lemma F_13474 : fetch_word Plain.M.loaded_segments (0x13474 : word) = Some W_13474.
Proof. vm_refl. Qed.
Lemma D_13474 : decode_any W_13474 = Some (OpImm ALU_ADD 10 10 3368, 4%Z).
Proof. vm_refl. Qed.

Definition W_13478 : bv 32 := 0x00053503.
Lemma F_13478 : fetch_word Plain.M.loaded_segments (0x13478 : word) = Some W_13478.
Proof. vm_refl. Qed.
Lemma D_13478 : decode_any W_13478 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1347c : bv 32 := 0x535020ef.
Lemma F_1347c : fetch_word Plain.M.loaded_segments (0x1347c : word) = Some W_1347c.
Proof. vm_refl. Qed.
Lemma D_1347c : decode_any W_1347c = Some (Jal 1 11572, 4%Z).
Proof. vm_refl. Qed.

Definition W_13480 : bv 32 := 0x0040006f.
Lemma F_13480 : fetch_word Plain.M.loaded_segments (0x13480 : word) = Some W_13480.
Proof. vm_refl. Qed.
Lemma D_13480 : decode_any W_13480 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13484 : bv 32 := 0x0000c517.
Lemma F_13484 : fetch_word Plain.M.loaded_segments (0x13484 : word) = Some W_13484.
Proof. vm_refl. Qed.
Lemma D_13484 : decode_any W_13484 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13488 : bv 32 := 0xcac53503.
Lemma F_13488 : fetch_word Plain.M.loaded_segments (0x13488 : word) = Some W_13488.
Proof. vm_refl. Qed.
Lemma D_13488 : decode_any W_13488 = Some (Load SZ8 true 10 10 3244, 4%Z).
Proof. vm_refl. Qed.

Definition W_1348c : bv 32 := 0x00050c63.
Lemma F_1348c : fetch_word Plain.M.loaded_segments (0x1348c : word) = Some W_1348c.
Proof. vm_refl. Qed.
Lemma D_1348c : decode_any W_1348c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13490 : bv 32 := 0x0040006f.
Lemma F_13490 : fetch_word Plain.M.loaded_segments (0x13490 : word) = Some W_13490.
Proof. vm_refl. Qed.
Lemma D_13490 : decode_any W_13490 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13494 : bv 32 := 0xffffe517.
Lemma F_13494 : fetch_word Plain.M.loaded_segments (0x13494 : word) = Some W_13494.
Proof. vm_refl. Qed.
Lemma D_13494 : decode_any W_13494 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13498 : bv 32 := 0x70450513.
Lemma F_13498 : fetch_word Plain.M.loaded_segments (0x13498 : word) = Some W_13498.
Proof. vm_refl. Qed.
Lemma D_13498 : decode_any W_13498 = Some (OpImm ALU_ADD 10 10 1796, 4%Z).
Proof. vm_refl. Qed.

Definition W_1349c : bv 32 := 0x000000ef.
Lemma F_1349c : fetch_word Plain.M.loaded_segments (0x1349c : word) = Some W_1349c.
Proof. vm_refl. Qed.
Lemma D_1349c : decode_any W_1349c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_134a0 : bv 32 := 0x0040006f.
Lemma F_134a0 : fetch_word Plain.M.loaded_segments (0x134a0 : word) = Some W_134a0.
Proof. vm_refl. Qed.
Lemma D_134a0 : decode_any W_134a0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_134a4 : bv 32 := 0x00813083.
Lemma F_134a4 : fetch_word Plain.M.loaded_segments (0x134a4 : word) = Some W_134a4.
Proof. vm_refl. Qed.
Lemma D_134a4 : decode_any W_134a4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_134a8 : bv 32 := 0x00013403.
Lemma F_134a8 : fetch_word Plain.M.loaded_segments (0x134a8 : word) = Some W_134a8.
Proof. vm_refl. Qed.
Lemma D_134a8 : decode_any W_134a8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_134ac : bv 32 := 0x01010113.
Lemma F_134ac : fetch_word Plain.M.loaded_segments (0x134ac : word) = Some W_134ac.
Proof. vm_refl. Qed.
Lemma D_134ac : decode_any W_134ac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_134b0 : bv 32 := 0x00008067.
Lemma F_134b0 : fetch_word Plain.M.loaded_segments (0x134b0 : word) = Some W_134b0.
Proof. vm_refl. Qed.
Lemma D_134b0 : decode_any W_134b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138dc : bv 32 := 0x0001d517.
Lemma F_138dc : fetch_word Plain.M.loaded_segments (0x138dc : word) = Some W_138dc.
Proof. vm_refl. Qed.
Lemma D_138dc : decode_any W_138dc = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_138e0 : bv 32 := 0xb4854503.
Lemma F_138e0 : fetch_word Plain.M.loaded_segments (0x138e0 : word) = Some W_138e0.
Proof. vm_refl. Qed.
Lemma D_138e0 : decode_any W_138e0 = Some (Load SZ1 false 10 10 2888, 4%Z).
Proof. vm_refl. Qed.

Definition W_138e4 : bv 32 := 0x00051463.
Lemma F_138e4 : fetch_word Plain.M.loaded_segments (0x138e4 : word) = Some W_138e4.
Proof. vm_refl. Qed.
Lemma D_138e4 : decode_any W_138e4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_138e8 : bv 32 := 0x00008067.
Lemma F_138e8 : fetch_word Plain.M.loaded_segments (0x138e8 : word) = Some W_138e8.
Proof. vm_refl. Qed.
Lemma D_138e8 : decode_any W_138e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138ec : bv 32 := 0xff010113.
Lemma F_138ec : fetch_word Plain.M.loaded_segments (0x138ec : word) = Some W_138ec.
Proof. vm_refl. Qed.
Lemma D_138ec : decode_any W_138ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_138f0 : bv 32 := 0x00113423.
Lemma F_138f0 : fetch_word Plain.M.loaded_segments (0x138f0 : word) = Some W_138f0.
Proof. vm_refl. Qed.
Lemma D_138f0 : decode_any W_138f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_138f4 : bv 32 := 0x0000c517.
Lemma F_138f4 : fetch_word Plain.M.loaded_segments (0x138f4 : word) = Some W_138f4.
Proof. vm_refl. Qed.
Lemma D_138f4 : decode_any W_138f4 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_138f8 : bv 32 := 0x85453503.
Lemma F_138f8 : fetch_word Plain.M.loaded_segments (0x138f8 : word) = Some W_138f8.
Proof. vm_refl. Qed.
Lemma D_138f8 : decode_any W_138f8 = Some (Load SZ8 true 10 10 2132, 4%Z).
Proof. vm_refl. Qed.

Definition W_138fc : bv 32 := 0x00053503.
Lemma F_138fc : fetch_word Plain.M.loaded_segments (0x138fc : word) = Some W_138fc.
Proof. vm_refl. Qed.
Lemma D_138fc : decode_any W_138fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13900 : bv 32 := 0x225040ef.
Lemma F_13900 : fetch_word Plain.M.loaded_segments (0x13900 : word) = Some W_13900.
Proof. vm_refl. Qed.
Lemma D_13900 : decode_any W_13900 = Some (Jal 1 18980, 4%Z).
Proof. vm_refl. Qed.

Definition W_13904 : bv 32 := 0x04d00513.
Lemma F_13904 : fetch_word Plain.M.loaded_segments (0x13904 : word) = Some W_13904.
Proof. vm_refl. Qed.
Lemma D_13904 : decode_any W_13904 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13908 : bv 32 := 0x7300a0ef.
Lemma F_13908 : fetch_word Plain.M.loaded_segments (0x13908 : word) = Some W_13908.
Proof. vm_refl. Qed.
Lemma D_13908 : decode_any W_13908 = Some (Jal 1 42800, 4%Z).
Proof. vm_refl. Qed.

Definition W_160e8 : bv 32 := 0xfd010113.
Lemma F_160e8 : fetch_word Plain.M.loaded_segments (0x160e8 : word) = Some W_160e8.
Proof. vm_refl. Qed.
Lemma D_160e8 : decode_any W_160e8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_160ec : bv 32 := 0x02113423.
Lemma F_160ec : fetch_word Plain.M.loaded_segments (0x160ec : word) = Some W_160ec.
Proof. vm_refl. Qed.
Lemma D_160ec : decode_any W_160ec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_160f0 : bv 32 := 0x02813023.
Lemma F_160f0 : fetch_word Plain.M.loaded_segments (0x160f0 : word) = Some W_160f0.
Proof. vm_refl. Qed.
Lemma D_160f0 : decode_any W_160f0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_160f4 : bv 32 := 0x00913c23.
Lemma F_160f4 : fetch_word Plain.M.loaded_segments (0x160f4 : word) = Some W_160f4.
Proof. vm_refl. Qed.
Lemma D_160f4 : decode_any W_160f4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_160f8 : bv 32 := 0x01213823.
Lemma F_160f8 : fetch_word Plain.M.loaded_segments (0x160f8 : word) = Some W_160f8.
Proof. vm_refl. Qed.
Lemma D_160f8 : decode_any W_160f8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_160fc : bv 32 := 0x01313423.
Lemma F_160fc : fetch_word Plain.M.loaded_segments (0x160fc : word) = Some W_160fc.
Proof. vm_refl. Qed.
Lemma D_160fc : decode_any W_160fc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16100 : bv 32 := 0x0003a517.
Lemma F_16100 : fetch_word Plain.M.loaded_segments (0x16100 : word) = Some W_16100.
Proof. vm_refl. Qed.
Lemma D_16100 : decode_any W_16100 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16104 : bv 32 := 0x46050913.
Lemma F_16104 : fetch_word Plain.M.loaded_segments (0x16104 : word) = Some W_16104.
Proof. vm_refl. Qed.
Lemma D_16104 : decode_any W_16104 = Some (OpImm ALU_ADD 18 10 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_16108 : bv 32 := 0x00490413.
Lemma F_16108 : fetch_word Plain.M.loaded_segments (0x16108 : word) = Some W_16108.
Proof. vm_refl. Qed.
Lemma D_16108 : decode_any W_16108 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1610c : bv 32 := 0x00040513.
Lemma F_1610c : fetch_word Plain.M.loaded_segments (0x1610c : word) = Some W_1610c.
Proof. vm_refl. Qed.
Lemma D_1610c : decode_any W_1610c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16110 : bv 32 := 0x3f9070ef.
Lemma F_16110 : fetch_word Plain.M.loaded_segments (0x16110 : word) = Some W_16110.
Proof. vm_refl. Qed.
Lemma D_16110 : decode_any W_16110 = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_16114 : bv 32 := 0x01093503.
Lemma F_16114 : fetch_word Plain.M.loaded_segments (0x16114 : word) = Some W_16114.
Proof. vm_refl. Qed.
Lemma D_16114 : decode_any W_16114 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16118 : bv 32 := 0x06050863.
Lemma F_16118 : fetch_word Plain.M.loaded_segments (0x16118 : word) = Some W_16118.
Proof. vm_refl. Qed.
Lemma D_16118 : decode_any W_16118 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1611c : bv 32 := 0x00892583.
Lemma F_1611c : fetch_word Plain.M.loaded_segments (0x1611c : word) = Some W_1611c.
Proof. vm_refl. Qed.
Lemma D_1611c : decode_any W_1611c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16120 : bv 32 := 0x0180006f.
Lemma F_16120 : fetch_word Plain.M.loaded_segments (0x16120 : word) = Some W_16120.
Proof. vm_refl. Qed.
Lemma D_16120 : decode_any W_16120 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16124 : bv 32 := 0x00053503.
Lemma F_16124 : fetch_word Plain.M.loaded_segments (0x16124 : word) = Some W_16124.
Proof. vm_refl. Qed.
Lemma D_16124 : decode_any W_16124 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16128 : bv 32 := 0x02000593.
Lemma F_16128 : fetch_word Plain.M.loaded_segments (0x16128 : word) = Some W_16128.
Proof. vm_refl. Qed.
Lemma D_16128 : decode_any W_16128 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1612c : bv 32 := 0x00b92423.
Lemma F_1612c : fetch_word Plain.M.loaded_segments (0x1612c : word) = Some W_1612c.
Proof. vm_refl. Qed.
Lemma D_1612c : decode_any W_1612c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16130 : bv 32 := 0x00a93823.
Lemma F_16130 : fetch_word Plain.M.loaded_segments (0x16130 : word) = Some W_16130.
Proof. vm_refl. Qed.
Lemma D_16130 : decode_any W_16130 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16134 : bv 32 := 0x04050a63.
Lemma F_16134 : fetch_word Plain.M.loaded_segments (0x16134 : word) = Some W_16134.
Proof. vm_refl. Qed.
Lemma D_16134 : decode_any W_16134 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_16138 : bv 32 := 0xfff5861b.
Lemma F_16138 : fetch_word Plain.M.loaded_segments (0x16138 : word) = Some W_16138.
Proof. vm_refl. Qed.
Lemma D_16138 : decode_any W_16138 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1613c : bv 32 := 0x00c92423.
Lemma F_1613c : fetch_word Plain.M.loaded_segments (0x1613c : word) = Some W_1613c.
Proof. vm_refl. Qed.
Lemma D_1613c : decode_any W_1613c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16140 : bv 32 := 0xfeb052e3.
Lemma F_16140 : fetch_word Plain.M.loaded_segments (0x16140 : word) = Some W_16140.
Proof. vm_refl. Qed.
Lemma D_16140 : decode_any W_16140 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_16144 : bv 32 := 0x01093503.
Lemma F_16144 : fetch_word Plain.M.loaded_segments (0x16144 : word) = Some W_16144.
Proof. vm_refl. Qed.
Lemma D_16144 : decode_any W_16144 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16148 : bv 32 := 0x00361613.
Lemma F_16148 : fetch_word Plain.M.loaded_segments (0x16148 : word) = Some W_16148.
Proof. vm_refl. Qed.
Lemma D_16148 : decode_any W_16148 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1614c : bv 32 := 0x00c50533.
Lemma F_1614c : fetch_word Plain.M.loaded_segments (0x1614c : word) = Some W_1614c.
Proof. vm_refl. Qed.
Lemma D_1614c : decode_any W_1614c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16150 : bv 32 := 0x00853983.
Lemma F_16150 : fetch_word Plain.M.loaded_segments (0x16150 : word) = Some W_16150.
Proof. vm_refl. Qed.
Lemma D_16150 : decode_any W_16150 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16154 : bv 32 := 0x10853483.
Lemma F_16154 : fetch_word Plain.M.loaded_segments (0x16154 : word) = Some W_16154.
Proof. vm_refl. Qed.
Lemma D_16154 : decode_any W_16154 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_16158 : bv 32 := 0x00040513.
Lemma F_16158 : fetch_word Plain.M.loaded_segments (0x16158 : word) = Some W_16158.
Proof. vm_refl. Qed.
Lemma D_16158 : decode_any W_16158 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1615c : bv 32 := 0x635070ef.
Lemma F_1615c : fetch_word Plain.M.loaded_segments (0x1615c : word) = Some W_1615c.
Proof. vm_refl. Qed.
Lemma D_1615c : decode_any W_1615c = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_16160 : bv 32 := 0x00048513.
Lemma F_16160 : fetch_word Plain.M.loaded_segments (0x16160 : word) = Some W_16160.
Proof. vm_refl. Qed.
Lemma D_16160 : decode_any W_16160 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16164 : bv 32 := 0x000980e7.
Lemma F_16164 : fetch_word Plain.M.loaded_segments (0x16164 : word) = Some W_16164.
Proof. vm_refl. Qed.
Lemma D_16164 : decode_any W_16164 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16168 : bv 32 := 0x00040513.
Lemma F_16168 : fetch_word Plain.M.loaded_segments (0x16168 : word) = Some W_16168.
Proof. vm_refl. Qed.
Lemma D_16168 : decode_any W_16168 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1616c : bv 32 := 0x39d070ef.
Lemma F_1616c : fetch_word Plain.M.loaded_segments (0x1616c : word) = Some W_1616c.
Proof. vm_refl. Qed.
Lemma D_1616c : decode_any W_1616c = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_16170 : bv 32 := 0x00892503.
Lemma F_16170 : fetch_word Plain.M.loaded_segments (0x16170 : word) = Some W_16170.
Proof. vm_refl. Qed.
Lemma D_16170 : decode_any W_16170 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16174 : bv 32 := 0xfff5061b.
Lemma F_16174 : fetch_word Plain.M.loaded_segments (0x16174 : word) = Some W_16174.
Proof. vm_refl. Qed.
Lemma D_16174 : decode_any W_16174 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_16178 : bv 32 := 0x00c92423.
Lemma F_16178 : fetch_word Plain.M.loaded_segments (0x16178 : word) = Some W_16178.
Proof. vm_refl. Qed.
Lemma D_16178 : decode_any W_16178 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1617c : bv 32 := 0xfca044e3.
Lemma F_1617c : fetch_word Plain.M.loaded_segments (0x1617c : word) = Some W_1617c.
Proof. vm_refl. Qed.
Lemma D_1617c : decode_any W_1617c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_16180 : bv 32 := 0x01093503.
Lemma F_16180 : fetch_word Plain.M.loaded_segments (0x16180 : word) = Some W_16180.
Proof. vm_refl. Qed.
Lemma D_16180 : decode_any W_16180 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16184 : bv 32 := 0xfa1ff06f.
Lemma F_16184 : fetch_word Plain.M.loaded_segments (0x16184 : word) = Some W_16184.
Proof. vm_refl. Qed.
Lemma D_16184 : decode_any W_16184 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_16188 : bv 32 := 0x00100513.
Lemma F_16188 : fetch_word Plain.M.loaded_segments (0x16188 : word) = Some W_16188.
Proof. vm_refl. Qed.
Lemma D_16188 : decode_any W_16188 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1618c : bv 32 := 0x00a90023.
Lemma F_1618c : fetch_word Plain.M.loaded_segments (0x1618c : word) = Some W_1618c.
Proof. vm_refl. Qed.
Lemma D_1618c : decode_any W_1618c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16190 : bv 32 := 0x00040513.
Lemma F_16190 : fetch_word Plain.M.loaded_segments (0x16190 : word) = Some W_16190.
Proof. vm_refl. Qed.
Lemma D_16190 : decode_any W_16190 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16194 : bv 32 := 0x02813083.
Lemma F_16194 : fetch_word Plain.M.loaded_segments (0x16194 : word) = Some W_16194.
Proof. vm_refl. Qed.
Lemma D_16194 : decode_any W_16194 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16198 : bv 32 := 0x02013403.
Lemma F_16198 : fetch_word Plain.M.loaded_segments (0x16198 : word) = Some W_16198.
Proof. vm_refl. Qed.
Lemma D_16198 : decode_any W_16198 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1619c : bv 32 := 0x01813483.
Lemma F_1619c : fetch_word Plain.M.loaded_segments (0x1619c : word) = Some W_1619c.
Proof. vm_refl. Qed.
Lemma D_1619c : decode_any W_1619c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_161a0 : bv 32 := 0x01013903.
Lemma F_161a0 : fetch_word Plain.M.loaded_segments (0x161a0 : word) = Some W_161a0.
Proof. vm_refl. Qed.
Lemma D_161a0 : decode_any W_161a0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_161a4 : bv 32 := 0x00813983.
Lemma F_161a4 : fetch_word Plain.M.loaded_segments (0x161a4 : word) = Some W_161a4.
Proof. vm_refl. Qed.
Lemma D_161a4 : decode_any W_161a4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_161a8 : bv 32 := 0x03010113.
Lemma F_161a8 : fetch_word Plain.M.loaded_segments (0x161a8 : word) = Some W_161a8.
Proof. vm_refl. Qed.
Lemma D_161a8 : decode_any W_161a8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_161ac : bv 32 := 0x5e50706f.
Lemma F_161ac : fetch_word Plain.M.loaded_segments (0x161ac : word) = Some W_161ac.
Proof. vm_refl. Qed.
Lemma D_161ac : decode_any W_161ac = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_161b0 : bv 32 := 0x00008067.
Lemma F_161b0 : fetch_word Plain.M.loaded_segments (0x161b0 : word) = Some W_161b0.
Proof. vm_refl. Qed.
Lemma D_161b0 : decode_any W_161b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_161b4 : bv 32 := 0xfd010113.
Lemma F_161b4 : fetch_word Plain.M.loaded_segments (0x161b4 : word) = Some W_161b4.
Proof. vm_refl. Qed.
Lemma D_161b4 : decode_any W_161b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_161b8 : bv 32 := 0x02113423.
Lemma F_161b8 : fetch_word Plain.M.loaded_segments (0x161b8 : word) = Some W_161b8.
Proof. vm_refl. Qed.
Lemma D_161b8 : decode_any W_161b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_161bc : bv 32 := 0x02813023.
Lemma F_161bc : fetch_word Plain.M.loaded_segments (0x161bc : word) = Some W_161bc.
Proof. vm_refl. Qed.
Lemma D_161bc : decode_any W_161bc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_161c0 : bv 32 := 0x00913c23.
Lemma F_161c0 : fetch_word Plain.M.loaded_segments (0x161c0 : word) = Some W_161c0.
Proof. vm_refl. Qed.
Lemma D_161c0 : decode_any W_161c0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_161c4 : bv 32 := 0x01213823.
Lemma F_161c4 : fetch_word Plain.M.loaded_segments (0x161c4 : word) = Some W_161c4.
Proof. vm_refl. Qed.
Lemma D_161c4 : decode_any W_161c4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_161c8 : bv 32 := 0x01313423.
Lemma F_161c8 : fetch_word Plain.M.loaded_segments (0x161c8 : word) = Some W_161c8.
Proof. vm_refl. Qed.
Lemma D_161c8 : decode_any W_161c8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_161cc : bv 32 := 0x00050493.
Lemma F_161cc : fetch_word Plain.M.loaded_segments (0x161cc : word) = Some W_161cc.
Proof. vm_refl. Qed.
Lemma D_161cc : decode_any W_161cc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_161d0 : bv 32 := 0x0003a517.
Lemma F_161d0 : fetch_word Plain.M.loaded_segments (0x161d0 : word) = Some W_161d0.
Proof. vm_refl. Qed.
Lemma D_161d0 : decode_any W_161d0 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_161d4 : bv 32 := 0x39050993.
Lemma F_161d4 : fetch_word Plain.M.loaded_segments (0x161d4 : word) = Some W_161d4.
Proof. vm_refl. Qed.
Lemma D_161d4 : decode_any W_161d4 = Some (OpImm ALU_ADD 19 10 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_161d8 : bv 32 := 0x00498413.
Lemma F_161d8 : fetch_word Plain.M.loaded_segments (0x161d8 : word) = Some W_161d8.
Proof. vm_refl. Qed.
Lemma D_161d8 : decode_any W_161d8 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_161dc : bv 32 := 0x00040513.
Lemma F_161dc : fetch_word Plain.M.loaded_segments (0x161dc : word) = Some W_161dc.
Proof. vm_refl. Qed.
Lemma D_161dc : decode_any W_161dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_161e0 : bv 32 := 0x329070ef.
Lemma F_161e0 : fetch_word Plain.M.loaded_segments (0x161e0 : word) = Some W_161e0.
Proof. vm_refl. Qed.
Lemma D_161e0 : decode_any W_161e0 = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_161e4 : bv 32 := 0x0009c503.
Lemma F_161e4 : fetch_word Plain.M.loaded_segments (0x161e4 : word) = Some W_161e4.
Proof. vm_refl. Qed.
Lemma D_161e4 : decode_any W_161e4 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_161e8 : bv 32 := 0xfff00913.
Lemma F_161e8 : fetch_word Plain.M.loaded_segments (0x161e8 : word) = Some W_161e8.
Proof. vm_refl. Qed.
Lemma D_161e8 : decode_any W_161e8 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_161ec : bv 32 := 0x06051263.
Lemma F_161ec : fetch_word Plain.M.loaded_segments (0x161ec : word) = Some W_161ec.
Proof. vm_refl. Qed.
Lemma D_161ec : decode_any W_161ec = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_161f0 : bv 32 := 0x0109b503.
Lemma F_161f0 : fetch_word Plain.M.loaded_segments (0x161f0 : word) = Some W_161f0.
Proof. vm_refl. Qed.
Lemma D_161f0 : decode_any W_161f0 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_161f4 : bv 32 := 0x00051663.
Lemma F_161f4 : fetch_word Plain.M.loaded_segments (0x161f4 : word) = Some W_161f4.
Proof. vm_refl. Qed.
Lemma D_161f4 : decode_any W_161f4 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_161f8 : bv 32 := 0x01898513.
Lemma F_161f8 : fetch_word Plain.M.loaded_segments (0x161f8 : word) = Some W_161f8.
Proof. vm_refl. Qed.
Lemma D_161f8 : decode_any W_161f8 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_161fc : bv 32 := 0x00a9b823.
Lemma F_161fc : fetch_word Plain.M.loaded_segments (0x161fc : word) = Some W_161fc.
Proof. vm_refl. Qed.
Lemma D_161fc : decode_any W_161fc = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16200 : bv 32 := 0x0089a583.
Lemma F_16200 : fetch_word Plain.M.loaded_segments (0x16200 : word) = Some W_16200.
Proof. vm_refl. Qed.
Lemma D_16200 : decode_any W_16200 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16204 : bv 32 := 0x02000613.
Lemma F_16204 : fetch_word Plain.M.loaded_segments (0x16204 : word) = Some W_16204.
Proof. vm_refl. Qed.
Lemma D_16204 : decode_any W_16204 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16208 : bv 32 := 0x02c59263.
Lemma F_16208 : fetch_word Plain.M.loaded_segments (0x16208 : word) = Some W_16208.
Proof. vm_refl. Qed.
Lemma D_16208 : decode_any W_16208 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1620c : bv 32 := 0x20800513.
Lemma F_1620c : fetch_word Plain.M.loaded_segments (0x1620c : word) = Some W_1620c.
Proof. vm_refl. Qed.
Lemma D_1620c : decode_any W_1620c = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_16210 : bv 32 := 0x00100593.
Lemma F_16210 : fetch_word Plain.M.loaded_segments (0x16210 : word) = Some W_16210.
Proof. vm_refl. Qed.
Lemma D_16210 : decode_any W_16210 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16214 : bv 32 := 0x3f4000ef.
Lemma F_16214 : fetch_word Plain.M.loaded_segments (0x16214 : word) = Some W_16214.
Proof. vm_refl. Qed.
Lemma D_16214 : decode_any W_16214 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_16218 : bv 32 := 0x02050c63.
Lemma F_16218 : fetch_word Plain.M.loaded_segments (0x16218 : word) = Some W_16218.
Proof. vm_refl. Qed.
Lemma D_16218 : decode_any W_16218 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1621c : bv 32 := 0x00000593.
Lemma F_1621c : fetch_word Plain.M.loaded_segments (0x1621c : word) = Some W_1621c.
Proof. vm_refl. Qed.
Lemma D_1621c : decode_any W_1621c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16220 : bv 32 := 0x0109b603.
Lemma F_16220 : fetch_word Plain.M.loaded_segments (0x16220 : word) = Some W_16220.
Proof. vm_refl. Qed.
Lemma D_16220 : decode_any W_16220 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16224 : bv 32 := 0x00c53023.
Lemma F_16224 : fetch_word Plain.M.loaded_segments (0x16224 : word) = Some W_16224.
Proof. vm_refl. Qed.
Lemma D_16224 : decode_any W_16224 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16228 : bv 32 := 0x00a9b823.
Lemma F_16228 : fetch_word Plain.M.loaded_segments (0x16228 : word) = Some W_16228.
Proof. vm_refl. Qed.
Lemma D_16228 : decode_any W_16228 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1622c : bv 32 := 0x00000913.
Lemma F_1622c : fetch_word Plain.M.loaded_segments (0x1622c : word) = Some W_1622c.
Proof. vm_refl. Qed.
Lemma D_1622c : decode_any W_1622c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16230 : bv 32 := 0x00359613.
Lemma F_16230 : fetch_word Plain.M.loaded_segments (0x16230 : word) = Some W_16230.
Proof. vm_refl. Qed.
Lemma D_16230 : decode_any W_16230 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_16234 : bv 32 := 0x00c50533.
Lemma F_16234 : fetch_word Plain.M.loaded_segments (0x16234 : word) = Some W_16234.
Proof. vm_refl. Qed.
Lemma D_16234 : decode_any W_16234 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16238 : bv 32 := 0x00000617.
Lemma F_16238 : fetch_word Plain.M.loaded_segments (0x16238 : word) = Some W_16238.
Proof. vm_refl. Qed.
Lemma D_16238 : decode_any W_16238 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1623c : bv 32 := 0x00158593.
Lemma F_1623c : fetch_word Plain.M.loaded_segments (0x1623c : word) = Some W_1623c.
Proof. vm_refl. Qed.
Lemma D_1623c : decode_any W_1623c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16240 : bv 32 := 0x04060613.
Lemma F_16240 : fetch_word Plain.M.loaded_segments (0x16240 : word) = Some W_16240.
Proof. vm_refl. Qed.
Lemma D_16240 : decode_any W_16240 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_16244 : bv 32 := 0x00c53423.
Lemma F_16244 : fetch_word Plain.M.loaded_segments (0x16244 : word) = Some W_16244.
Proof. vm_refl. Qed.
Lemma D_16244 : decode_any W_16244 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16248 : bv 32 := 0x10953423.
Lemma F_16248 : fetch_word Plain.M.loaded_segments (0x16248 : word) = Some W_16248.
Proof. vm_refl. Qed.
Lemma D_16248 : decode_any W_16248 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1624c : bv 32 := 0x00b9a423.
Lemma F_1624c : fetch_word Plain.M.loaded_segments (0x1624c : word) = Some W_1624c.
Proof. vm_refl. Qed.
Lemma D_1624c : decode_any W_1624c = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16250 : bv 32 := 0x00040513.
Lemma F_16250 : fetch_word Plain.M.loaded_segments (0x16250 : word) = Some W_16250.
Proof. vm_refl. Qed.
Lemma D_16250 : decode_any W_16250 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16254 : bv 32 := 0x53d070ef.
Lemma F_16254 : fetch_word Plain.M.loaded_segments (0x16254 : word) = Some W_16254.
Proof. vm_refl. Qed.
Lemma D_16254 : decode_any W_16254 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_16258 : bv 32 := 0x00090513.
Lemma F_16258 : fetch_word Plain.M.loaded_segments (0x16258 : word) = Some W_16258.
Proof. vm_refl. Qed.
Lemma D_16258 : decode_any W_16258 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1625c : bv 32 := 0x02813083.
Lemma F_1625c : fetch_word Plain.M.loaded_segments (0x1625c : word) = Some W_1625c.
Proof. vm_refl. Qed.
Lemma D_1625c : decode_any W_1625c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16260 : bv 32 := 0x02013403.
Lemma F_16260 : fetch_word Plain.M.loaded_segments (0x16260 : word) = Some W_16260.
Proof. vm_refl. Qed.
Lemma D_16260 : decode_any W_16260 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16264 : bv 32 := 0x01813483.
Lemma F_16264 : fetch_word Plain.M.loaded_segments (0x16264 : word) = Some W_16264.
Proof. vm_refl. Qed.
Lemma D_16264 : decode_any W_16264 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16268 : bv 32 := 0x01013903.
Lemma F_16268 : fetch_word Plain.M.loaded_segments (0x16268 : word) = Some W_16268.
Proof. vm_refl. Qed.
Lemma D_16268 : decode_any W_16268 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1626c : bv 32 := 0x00813983.
Lemma F_1626c : fetch_word Plain.M.loaded_segments (0x1626c : word) = Some W_1626c.
Proof. vm_refl. Qed.
Lemma D_1626c : decode_any W_1626c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16270 : bv 32 := 0x03010113.
Lemma F_16270 : fetch_word Plain.M.loaded_segments (0x16270 : word) = Some W_16270.
Proof. vm_refl. Qed.
Lemma D_16270 : decode_any W_16270 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16274 : bv 32 := 0x00008067.
Lemma F_16274 : fetch_word Plain.M.loaded_segments (0x16274 : word) = Some W_16274.
Proof. vm_refl. Qed.
Lemma D_16274 : decode_any W_16274 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16278 : bv 32 := 0x00050067.
Lemma F_16278 : fetch_word Plain.M.loaded_segments (0x16278 : word) = Some W_16278.
Proof. vm_refl. Qed.
Lemma D_16278 : decode_any W_16278 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1627c : bv 32 := 0x00008067.
Lemma F_1627c : fetch_word Plain.M.loaded_segments (0x1627c : word) = Some W_1627c.
Proof. vm_refl. Qed.
Lemma D_1627c : decode_any W_1627c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16280 : bv 32 := 0xfe010113.
Lemma F_16280 : fetch_word Plain.M.loaded_segments (0x16280 : word) = Some W_16280.
Proof. vm_refl. Qed.
Lemma D_16280 : decode_any W_16280 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_16284 : bv 32 := 0x00113c23.
Lemma F_16284 : fetch_word Plain.M.loaded_segments (0x16284 : word) = Some W_16284.
Proof. vm_refl. Qed.
Lemma D_16284 : decode_any W_16284 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16288 : bv 32 := 0x00813823.
Lemma F_16288 : fetch_word Plain.M.loaded_segments (0x16288 : word) = Some W_16288.
Proof. vm_refl. Qed.
Lemma D_16288 : decode_any W_16288 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1628c : bv 32 := 0x00913423.
Lemma F_1628c : fetch_word Plain.M.loaded_segments (0x1628c : word) = Some W_1628c.
Proof. vm_refl. Qed.
Lemma D_1628c : decode_any W_1628c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16290 : bv 32 := 0x00009517.
Lemma F_16290 : fetch_word Plain.M.loaded_segments (0x16290 : word) = Some W_16290.
Proof. vm_refl. Qed.
Lemma D_16290 : decode_any W_16290 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16294 : bv 32 := 0x00009597.
Lemma F_16294 : fetch_word Plain.M.loaded_segments (0x16294 : word) = Some W_16294.
Proof. vm_refl. Qed.
Lemma D_16294 : decode_any W_16294 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16298 : bv 32 := 0xef853503.
Lemma F_16298 : fetch_word Plain.M.loaded_segments (0x16298 : word) = Some W_16298.
Proof. vm_refl. Qed.
Lemma D_16298 : decode_any W_16298 = Some (Load SZ8 true 10 10 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_1629c : bv 32 := 0xefc5b403.
Lemma F_1629c : fetch_word Plain.M.loaded_segments (0x1629c : word) = Some W_1629c.
Proof. vm_refl. Qed.
Lemma D_1629c : decode_any W_1629c = Some (Load SZ8 true 8 11 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_162a0 : bv 32 := 0x00a47c63.
Lemma F_162a0 : fetch_word Plain.M.loaded_segments (0x162a0 : word) = Some W_162a0.
Proof. vm_refl. Qed.
Lemma D_162a0 : decode_any W_162a0 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_162a4 : bv 32 := 0xff853583.
Lemma F_162a4 : fetch_word Plain.M.loaded_segments (0x162a4 : word) = Some W_162a4.
Proof. vm_refl. Qed.
Lemma D_162a4 : decode_any W_162a4 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_162a8 : bv 32 := 0xff850493.
Lemma F_162a8 : fetch_word Plain.M.loaded_segments (0x162a8 : word) = Some W_162a8.
Proof. vm_refl. Qed.
Lemma D_162a8 : decode_any W_162a8 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_162ac : bv 32 := 0x000580e7.
Lemma F_162ac : fetch_word Plain.M.loaded_segments (0x162ac : word) = Some W_162ac.
Proof. vm_refl. Qed.
Lemma D_162ac : decode_any W_162ac = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_162b0 : bv 32 := 0x00048513.
Lemma F_162b0 : fetch_word Plain.M.loaded_segments (0x162b0 : word) = Some W_162b0.
Proof. vm_refl. Qed.
Lemma D_162b0 : decode_any W_162b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_162b4 : bv 32 := 0xfe9468e3.
Lemma F_162b4 : fetch_word Plain.M.loaded_segments (0x162b4 : word) = Some W_162b4.
Proof. vm_refl. Qed.
Lemma D_162b4 : decode_any W_162b4 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_162b8 : bv 32 := 0x01813083.
Lemma F_162b8 : fetch_word Plain.M.loaded_segments (0x162b8 : word) = Some W_162b8.
Proof. vm_refl. Qed.
Lemma D_162b8 : decode_any W_162b8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_162bc : bv 32 := 0x01013403.
Lemma F_162bc : fetch_word Plain.M.loaded_segments (0x162bc : word) = Some W_162bc.
Proof. vm_refl. Qed.
Lemma D_162bc : decode_any W_162bc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_162c0 : bv 32 := 0x00813483.
Lemma F_162c0 : fetch_word Plain.M.loaded_segments (0x162c0 : word) = Some W_162c0.
Proof. vm_refl. Qed.
Lemma D_162c0 : decode_any W_162c0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_162c4 : bv 32 := 0x02010113.
Lemma F_162c4 : fetch_word Plain.M.loaded_segments (0x162c4 : word) = Some W_162c4.
Proof. vm_refl. Qed.
Lemma D_162c4 : decode_any W_162c4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_162c8 : bv 32 := 0xfb5ff06f.
Lemma F_162c8 : fetch_word Plain.M.loaded_segments (0x162c8 : word) = Some W_162c8.
Proof. vm_refl. Qed.
Lemma D_162c8 : decode_any W_162c8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_162cc : bv 32 := 0xff010113.
Lemma F_162cc : fetch_word Plain.M.loaded_segments (0x162cc : word) = Some W_162cc.
Proof. vm_refl. Qed.
Lemma D_162cc : decode_any W_162cc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_162d0 : bv 32 := 0x00113423.
Lemma F_162d0 : fetch_word Plain.M.loaded_segments (0x162d0 : word) = Some W_162d0.
Proof. vm_refl. Qed.
Lemma D_162d0 : decode_any W_162d0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_162d4 : bv 32 := 0x00813023.
Lemma F_162d4 : fetch_word Plain.M.loaded_segments (0x162d4 : word) = Some W_162d4.
Proof. vm_refl. Qed.
Lemma D_162d4 : decode_any W_162d4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_162d8 : bv 32 := 0x00000593.
Lemma F_162d8 : fetch_word Plain.M.loaded_segments (0x162d8 : word) = Some W_162d8.
Proof. vm_refl. Qed.
Lemma D_162d8 : decode_any W_162d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_162dc : bv 32 := 0x00020613.
Lemma F_162dc : fetch_word Plain.M.loaded_segments (0x162dc : word) = Some W_162dc.
Proof. vm_refl. Qed.
Lemma D_162dc : decode_any W_162dc = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_162e0 : bv 32 := 0xf5862603.
Lemma F_162e0 : fetch_word Plain.M.loaded_segments (0x162e0 : word) = Some W_162e0.
Proof. vm_refl. Qed.
Lemma D_162e0 : decode_any W_162e0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_162e4 : bv 32 := 0x0003a697.
Lemma F_162e4 : fetch_word Plain.M.loaded_segments (0x162e4 : word) = Some W_162e4.
Proof. vm_refl. Qed.
Lemma D_162e4 : decode_any W_162e4 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_162e8 : bv 32 := 0x49c68693.
Lemma F_162e8 : fetch_word Plain.M.loaded_segments (0x162e8 : word) = Some W_162e8.
Proof. vm_refl. Qed.
Lemma D_162e8 : decode_any W_162e8 = Some (OpImm ALU_ADD 13 13 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_162ec : bv 32 := 0x1606a72f.
Lemma F_162ec : fetch_word Plain.M.loaded_segments (0x162ec : word) = Some W_162ec.
Proof. vm_refl. Qed.
Lemma D_162ec : decode_any W_162ec = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_162f0 : bv 32 := 0x00b71663.
Lemma F_162f0 : fetch_word Plain.M.loaded_segments (0x162f0 : word) = Some W_162f0.
Proof. vm_refl. Qed.
Lemma D_162f0 : decode_any W_162f0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_162f4 : bv 32 := 0x1ec6a7af.
Lemma F_162f4 : fetch_word Plain.M.loaded_segments (0x162f4 : word) = Some W_162f4.
Proof. vm_refl. Qed.
Lemma D_162f4 : decode_any W_162f4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_162f8 : bv 32 := 0xfe079ae3.
Lemma F_162f8 : fetch_word Plain.M.loaded_segments (0x162f8 : word) = Some W_162f8.
Proof. vm_refl. Qed.
Lemma D_162f8 : decode_any W_162f8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_162fc : bv 32 := 0x0007059b.
Lemma F_162fc : fetch_word Plain.M.loaded_segments (0x162fc : word) = Some W_162fc.
Proof. vm_refl. Qed.
Lemma D_162fc : decode_any W_162fc = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16300 : bv 32 := 0x02c58263.
Lemma F_16300 : fetch_word Plain.M.loaded_segments (0x16300 : word) = Some W_16300.
Proof. vm_refl. Qed.
Lemma D_16300 : decode_any W_16300 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_16304 : bv 32 := 0x02058263.
Lemma F_16304 : fetch_word Plain.M.loaded_segments (0x16304 : word) = Some W_16304.
Proof. vm_refl. Qed.
Lemma D_16304 : decode_any W_16304 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_16308 : bv 32 := 0x04900893.
Lemma F_16308 : fetch_word Plain.M.loaded_segments (0x16308 : word) = Some W_16308.
Proof. vm_refl. Qed.
Lemma D_16308 : decode_any W_16308 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630c : bv 32 := 0x00000593.
Lemma F_1630c : fetch_word Plain.M.loaded_segments (0x1630c : word) = Some W_1630c.
Proof. vm_refl. Qed.
Lemma D_1630c : decode_any W_1630c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16310 : bv 32 := 0x00000613.
Lemma F_16310 : fetch_word Plain.M.loaded_segments (0x16310 : word) = Some W_16310.
Proof. vm_refl. Qed.
Lemma D_16310 : decode_any W_16310 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16314 : bv 32 := 0x00000693.
Lemma F_16314 : fetch_word Plain.M.loaded_segments (0x16314 : word) = Some W_16314.
Proof. vm_refl. Qed.
Lemma D_16314 : decode_any W_16314 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16318 : bv 32 := 0x00000513.
Lemma F_16318 : fetch_word Plain.M.loaded_segments (0x16318 : word) = Some W_16318.
Proof. vm_refl. Qed.
Lemma D_16318 : decode_any W_16318 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1631c : bv 32 := 0x00000073.
Lemma F_1631c : fetch_word Plain.M.loaded_segments (0x1631c : word) = Some W_1631c.
Proof. vm_refl. Qed.
Lemma E_1631c : is_ecall W_1631c = true.
Proof. vm_refl. Qed.

Definition W_16320 : bv 32 := 0xff9ff06f.
Lemma F_16320 : fetch_word Plain.M.loaded_segments (0x16320 : word) = Some W_16320.
Proof. vm_refl. Qed.
Lemma D_16320 : decode_any W_16320 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_16324 : bv 32 := 0x00000023.
Lemma F_16324 : fetch_word Plain.M.loaded_segments (0x16324 : word) = Some W_16324.
Proof. vm_refl. Qed.
Lemma D_16324 : decode_any W_16324 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16328 : bv 32 := 0x00050413.
Lemma F_16328 : fetch_word Plain.M.loaded_segments (0x16328 : word) = Some W_16328.
Proof. vm_refl. Qed.
Lemma D_16328 : decode_any W_16328 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1632c : bv 32 := 0xdbdff0ef.
Lemma F_1632c : fetch_word Plain.M.loaded_segments (0x1632c : word) = Some W_1632c.
Proof. vm_refl. Qed.
Lemma D_1632c : decode_any W_1632c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_16330 : bv 32 := 0xf51ff0ef.
Lemma F_16330 : fetch_word Plain.M.loaded_segments (0x16330 : word) = Some W_16330.
Proof. vm_refl. Qed.
Lemma D_16330 : decode_any W_16330 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_16334 : bv 32 := 0x160020ef.
Lemma F_16334 : fetch_word Plain.M.loaded_segments (0x16334 : word) = Some W_16334.
Proof. vm_refl. Qed.
Lemma D_16334 : decode_any W_16334 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_16338 : bv 32 := 0x00040513.
Lemma F_16338 : fetch_word Plain.M.loaded_segments (0x16338 : word) = Some W_16338.
Proof. vm_refl. Qed.
Lemma D_16338 : decode_any W_16338 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1633c : bv 32 := 0xd91ff0ef.
Lemma F_1633c : fetch_word Plain.M.loaded_segments (0x1633c : word) = Some W_1633c.
Proof. vm_refl. Qed.
Lemma D_1633c : decode_any W_1633c = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1dd08 : bv 32 := 0x00033597.
Lemma F_1dd08 : fetch_word Plain.M.loaded_segments (0x1dd08 : word) = Some W_1dd08.
Proof. vm_refl. Qed.
Lemma D_1dd08 : decode_any W_1dd08 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1dd0c : bv 32 := 0xaa358683.
Lemma F_1dd0c : fetch_word Plain.M.loaded_segments (0x1dd0c : word) = Some W_1dd0c.
Proof. vm_refl. Qed.
Lemma D_1dd0c : decode_any W_1dd0c = Some (Load SZ1 true 13 11 2723, 4%Z).
Proof. vm_refl. Qed.

Definition W_1dd10 : bv 32 := 0x1e068863.
Lemma F_1dd10 : fetch_word Plain.M.loaded_segments (0x1dd10 : word) = Some W_1dd10.
Proof. vm_refl. Qed.
Lemma D_1dd10 : decode_any W_1dd10 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1df00 : bv 32 := 0x00008067.
Lemma F_1df00 : fetch_word Plain.M.loaded_segments (0x1df00 : word) = Some W_1df00.
Proof. vm_refl. Qed.
Lemma D_1df00 : decode_any W_1df00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1df90 : bv 32 := 0x00052583.
Lemma F_1df90 : fetch_word Plain.M.loaded_segments (0x1df90 : word) = Some W_1df90.
Proof. vm_refl. Qed.
Lemma D_1df90 : decode_any W_1df90 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1df94 : bv 32 := 0x0005c463.
Lemma F_1df94 : fetch_word Plain.M.loaded_segments (0x1df94 : word) = Some W_1df94.
Proof. vm_refl. Qed.
Lemma D_1df94 : decode_any W_1df94 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1df98 : bv 32 := 0x00008067.
Lemma F_1df98 : fetch_word Plain.M.loaded_segments (0x1df98 : word) = Some W_1df98.
Proof. vm_refl. Qed.
Lemma D_1df98 : decode_any W_1df98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
