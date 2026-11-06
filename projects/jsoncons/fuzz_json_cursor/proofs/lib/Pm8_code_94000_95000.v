(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9465c : bv 32 := 0xfd010113.
Lemma F_9465c : fetch_word Asan.M.loaded_segments (0x946ac : word) = Some W_9465c.
Proof. vm_refl. Qed.
Lemma D_9465c : decode_any W_9465c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_94660 : bv 32 := 0x02113423.
Lemma F_94660 : fetch_word Asan.M.loaded_segments (0x946b0 : word) = Some W_94660.
Proof. vm_refl. Qed.
Lemma D_94660 : decode_any W_94660 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94664 : bv 32 := 0x02813023.
Lemma F_94664 : fetch_word Asan.M.loaded_segments (0x946b4 : word) = Some W_94664.
Proof. vm_refl. Qed.
Lemma D_94664 : decode_any W_94664 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_94668 : bv 32 := 0x00913c23.
Lemma F_94668 : fetch_word Asan.M.loaded_segments (0x946b8 : word) = Some W_94668.
Proof. vm_refl. Qed.
Lemma D_94668 : decode_any W_94668 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9466c : bv 32 := 0x01213823.
Lemma F_9466c : fetch_word Asan.M.loaded_segments (0x946bc : word) = Some W_9466c.
Proof. vm_refl. Qed.
Lemma D_9466c : decode_any W_9466c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94670 : bv 32 := 0x02050e63.
Lemma F_94670 : fetch_word Asan.M.loaded_segments (0x946c0 : word) = Some W_94670.
Proof. vm_refl. Qed.
Lemma D_94670 : decode_any W_94670 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_94674 : bv 32 := 0x00058413.
Lemma F_94674 : fetch_word Asan.M.loaded_segments (0x946c4 : word) = Some W_94674.
Proof. vm_refl. Qed.
Lemma D_94674 : decode_any W_94674 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94678 : bv 32 := 0x02058a63.
Lemma F_94678 : fetch_word Asan.M.loaded_segments (0x946c8 : word) = Some W_94678.
Proof. vm_refl. Qed.
Lemma D_94678 : decode_any W_94678 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9467c : bv 32 := 0x00060493.
Lemma F_9467c : fetch_word Asan.M.loaded_segments (0x946cc : word) = Some W_9467c.
Proof. vm_refl. Qed.
Lemma D_9467c : decode_any W_9467c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94680 : bv 32 := 0x00050913.
Lemma F_94680 : fetch_word Asan.M.loaded_segments (0x946d0 : word) = Some W_94680.
Proof. vm_refl. Qed.
Lemma D_94680 : decode_any W_94680 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94684 : bv 32 := 0x00040593.
Lemma F_94684 : fetch_word Asan.M.loaded_segments (0x946d4 : word) = Some W_94684.
Proof. vm_refl. Qed.
Lemma D_94684 : decode_any W_94684 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94688 : bv 32 := 0xf90fe0ef.
Lemma F_94688 : fetch_word Asan.M.loaded_segments (0x946d8 : word) = Some W_94688.
Proof. vm_refl. Qed.
Lemma D_94688 : decode_any W_94688 = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_9468c : bv 32 := 0xaaaab5b7.
Lemma F_9468c : fetch_word Asan.M.loaded_segments (0x946dc : word) = Some W_9468c.
Proof. vm_refl. Qed.
Lemma D_9468c : decode_any W_9468c = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94690 : bv 32 := 0xaaa58593.
Lemma F_94690 : fetch_word Asan.M.loaded_segments (0x946e0 : word) = Some W_94690.
Proof. vm_refl. Qed.
Lemma D_94690 : decode_any W_94690 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_94694 : bv 32 := 0x00b12623.
Lemma F_94694 : fetch_word Asan.M.loaded_segments (0x946e4 : word) = Some W_94694.
Proof. vm_refl. Qed.
Lemma D_94694 : decode_any W_94694 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94698 : bv 32 := 0x00c10593.
Lemma F_94698 : fetch_word Asan.M.loaded_segments (0x946e8 : word) = Some W_94698.
Proof. vm_refl. Qed.
Lemma D_94698 : decode_any W_94698 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9469c : bv 32 := 0xf50fe0ef.
Lemma F_9469c : fetch_word Asan.M.loaded_segments (0x946ec : word) = Some W_9469c.
Proof. vm_refl. Qed.
Lemma D_9469c : decode_any W_9469c = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_946a0 : bv 32 := 0x02051263.
Lemma F_946a0 : fetch_word Asan.M.loaded_segments (0x946f0 : word) = Some W_946a0.
Proof. vm_refl. Qed.
Lemma D_946a0 : decode_any W_946a0 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_946a4 : bv 32 := 0x00040513.
Lemma F_946a4 : fetch_word Asan.M.loaded_segments (0x946f4 : word) = Some W_946a4.
Proof. vm_refl. Qed.
Lemma D_946a4 : decode_any W_946a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_946a8 : bv 32 := 0xe70fa0ef.
Lemma F_946a8 : fetch_word Asan.M.loaded_segments (0x946f8 : word) = Some W_946a8.
Proof. vm_refl. Qed.
Lemma D_946a8 : decode_any W_946a8 = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

Definition W_946ac : bv 32 := 0x02813083.
Lemma F_946ac : fetch_word Asan.M.loaded_segments (0x946fc : word) = Some W_946ac.
Proof. vm_refl. Qed.
Lemma D_946ac : decode_any W_946ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_946b0 : bv 32 := 0x02013403.
Lemma F_946b0 : fetch_word Asan.M.loaded_segments (0x94700 : word) = Some W_946b0.
Proof. vm_refl. Qed.
Lemma D_946b0 : decode_any W_946b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_946b4 : bv 32 := 0x01813483.
Lemma F_946b4 : fetch_word Asan.M.loaded_segments (0x94704 : word) = Some W_946b4.
Proof. vm_refl. Qed.
Lemma D_946b4 : decode_any W_946b4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_946b8 : bv 32 := 0x01013903.
Lemma F_946b8 : fetch_word Asan.M.loaded_segments (0x94708 : word) = Some W_946b8.
Proof. vm_refl. Qed.
Lemma D_946b8 : decode_any W_946b8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_946bc : bv 32 := 0x03010113.
Lemma F_946bc : fetch_word Asan.M.loaded_segments (0x9470c : word) = Some W_946bc.
Proof. vm_refl. Qed.
Lemma D_946bc : decode_any W_946bc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_946c0 : bv 32 := 0x00008067.
Lemma F_946c0 : fetch_word Asan.M.loaded_segments (0x94710 : word) = Some W_946c0.
Proof. vm_refl. Qed.
Lemma D_946c0 : decode_any W_946c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_946d8 : bv 32 := 0xfd010113.
Lemma F_946d8 : fetch_word Asan.M.loaded_segments (0x94728 : word) = Some W_946d8.
Proof. vm_refl. Qed.
Lemma D_946d8 : decode_any W_946d8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_946dc : bv 32 := 0x02113423.
Lemma F_946dc : fetch_word Asan.M.loaded_segments (0x9472c : word) = Some W_946dc.
Proof. vm_refl. Qed.
Lemma D_946dc : decode_any W_946dc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_946e0 : bv 32 := 0x02813023.
Lemma F_946e0 : fetch_word Asan.M.loaded_segments (0x94730 : word) = Some W_946e0.
Proof. vm_refl. Qed.
Lemma D_946e0 : decode_any W_946e0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_946e4 : bv 32 := 0x00913c23.
Lemma F_946e4 : fetch_word Asan.M.loaded_segments (0x94734 : word) = Some W_946e4.
Proof. vm_refl. Qed.
Lemma D_946e4 : decode_any W_946e4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_946e8 : bv 32 := 0x01213823.
Lemma F_946e8 : fetch_word Asan.M.loaded_segments (0x94738 : word) = Some W_946e8.
Proof. vm_refl. Qed.
Lemma D_946e8 : decode_any W_946e8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_946ec : bv 32 := 0x00058413.
Lemma F_946ec : fetch_word Asan.M.loaded_segments (0x9473c : word) = Some W_946ec.
Proof. vm_refl. Qed.
Lemma D_946ec : decode_any W_946ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_946f0 : bv 32 := 0x000bf597.
Lemma F_946f0 : fetch_word Asan.M.loaded_segments (0x94740 : word) = Some W_946f0.
Proof. vm_refl. Qed.
Lemma D_946f0 : decode_any W_946f0 = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_946f4 : bv 32 := 0x9d85b903.
Lemma F_946f4 : fetch_word Asan.M.loaded_segments (0x94744 : word) = Some W_946f4.
Proof. vm_refl. Qed.
Lemma D_946f4 : decode_any W_946f4 = Some (Load SZ8 true 18 11 2520, 4%Z).
Proof. vm_refl. Qed.

Definition W_946f8 : bv 32 := 0x00093583.
Lemma F_946f8 : fetch_word Asan.M.loaded_segments (0x94748 : word) = Some W_946f8.
Proof. vm_refl. Qed.
Lemma D_946f8 : decode_any W_946f8 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_946fc : bv 32 := 0x00050493.
Lemma F_946fc : fetch_word Asan.M.loaded_segments (0x9474c : word) = Some W_946fc.
Proof. vm_refl. Qed.
Lemma D_946fc : decode_any W_946fc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94700 : bv 32 := 0x00059863.
Lemma F_94700 : fetch_word Asan.M.loaded_segments (0x94750 : word) = Some W_94700.
Proof. vm_refl. Qed.
Lemma D_94700 : decode_any W_94700 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94710 : bv 32 := 0xfff58513.
Lemma F_94710 : fetch_word Asan.M.loaded_segments (0x94760 : word) = Some W_94710.
Proof. vm_refl. Qed.
Lemma D_94710 : decode_any W_94710 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94714 : bv 32 := 0x00a5f533.
Lemma F_94714 : fetch_word Asan.M.loaded_segments (0x94764 : word) = Some W_94714.
Proof. vm_refl. Qed.
Lemma D_94714 : decode_any W_94714 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94718 : bv 32 := 0x08051a63.
Lemma F_94718 : fetch_word Asan.M.loaded_segments (0x94768 : word) = Some W_94718.
Proof. vm_refl. Qed.
Lemma D_94718 : decode_any W_94718 = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_9471c : bv 32 := 0x00b484b3.
Lemma F_9471c : fetch_word Asan.M.loaded_segments (0x9476c : word) = Some W_9471c.
Proof. vm_refl. Qed.
Lemma D_9471c : decode_any W_9471c = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94720 : bv 32 := 0x40b00533.
Lemma F_94720 : fetch_word Asan.M.loaded_segments (0x94770 : word) = Some W_94720.
Proof. vm_refl. Qed.
Lemma D_94720 : decode_any W_94720 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94724 : bv 32 := 0xfff48493.
Lemma F_94724 : fetch_word Asan.M.loaded_segments (0x94774 : word) = Some W_94724.
Proof. vm_refl. Qed.
Lemma D_94724 : decode_any W_94724 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94728 : bv 32 := 0x00a4f4b3.
Lemma F_94728 : fetch_word Asan.M.loaded_segments (0x94778 : word) = Some W_94728.
Proof. vm_refl. Qed.
Lemma D_94728 : decode_any W_94728 = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9472c : bv 32 := 0x02200513.
Lemma F_9472c : fetch_word Asan.M.loaded_segments (0x9477c : word) = Some W_9472c.
Proof. vm_refl. Qed.
Lemma D_9472c : decode_any W_9472c = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_94730 : bv 32 := 0x00a12623.
Lemma F_94730 : fetch_word Asan.M.loaded_segments (0x94780 : word) = Some W_94730.
Proof. vm_refl. Qed.
Lemma D_94730 : decode_any W_94730 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94734 : bv 32 := 0x00c10613.
Lemma F_94734 : fetch_word Asan.M.loaded_segments (0x94784 : word) = Some W_94734.
Proof. vm_refl. Qed.
Lemma D_94734 : decode_any W_94734 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94738 : bv 32 := 0x00040513.
Lemma F_94738 : fetch_word Asan.M.loaded_segments (0x94788 : word) = Some W_94738.
Proof. vm_refl. Qed.
Lemma D_94738 : decode_any W_94738 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9473c : bv 32 := 0x00048593.
Lemma F_9473c : fetch_word Asan.M.loaded_segments (0x9478c : word) = Some W_9473c.
Proof. vm_refl. Qed.
Lemma D_9473c : decode_any W_9473c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94740 : bv 32 := 0x279000ef.
Lemma F_94740 : fetch_word Asan.M.loaded_segments (0x94790 : word) = Some W_94740.
Proof. vm_refl. Qed.
Lemma D_94740 : decode_any W_94740 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_94744 : bv 32 := 0x00c12683.
Lemma F_94744 : fetch_word Asan.M.loaded_segments (0x94794 : word) = Some W_94744.
Proof. vm_refl. Qed.
Lemma D_94744 : decode_any W_94744 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94748 : bv 32 := 0x00050713.
Lemma F_94748 : fetch_word Asan.M.loaded_segments (0x94798 : word) = Some W_94748.
Proof. vm_refl. Qed.
Lemma D_94748 : decode_any W_94748 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9474c : bv 32 := 0x00300613.
Lemma F_9474c : fetch_word Asan.M.loaded_segments (0x9479c : word) = Some W_9474c.
Proof. vm_refl. Qed.
Lemma D_9474c : decode_any W_9474c = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94750 : bv 32 := 0x00000513.
Lemma F_94750 : fetch_word Asan.M.loaded_segments (0x947a0 : word) = Some W_94750.
Proof. vm_refl. Qed.
Lemma D_94750 : decode_any W_94750 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94754 : bv 32 := 0x00048593.
Lemma F_94754 : fetch_word Asan.M.loaded_segments (0x947a4 : word) = Some W_94754.
Proof. vm_refl. Qed.
Lemma D_94754 : decode_any W_94754 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94758 : bv 32 := 0x00000793.
Lemma F_94758 : fetch_word Asan.M.loaded_segments (0x947a8 : word) = Some W_94758.
Proof. vm_refl. Qed.
Lemma D_94758 : decode_any W_94758 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9475c : bv 32 := 0xeb0fe0ef.
Lemma F_9475c : fetch_word Asan.M.loaded_segments (0x947ac : word) = Some W_9475c.
Proof. vm_refl. Qed.
Lemma D_9475c : decode_any W_9475c = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_94760 : bv 32 := 0x00050913.
Lemma F_94760 : fetch_word Asan.M.loaded_segments (0x947b0 : word) = Some W_94760.
Proof. vm_refl. Qed.
Lemma D_94760 : decode_any W_94760 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94764 : bv 32 := 0x00000593.
Lemma F_94764 : fetch_word Asan.M.loaded_segments (0x947b4 : word) = Some W_94764.
Proof. vm_refl. Qed.
Lemma D_94764 : decode_any W_94764 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94768 : bv 32 := 0xe84fe0ef.
Lemma F_94768 : fetch_word Asan.M.loaded_segments (0x947b8 : word) = Some W_94768.
Proof. vm_refl. Qed.
Lemma D_94768 : decode_any W_94768 = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_9476c : bv 32 := 0xaaaab537.
Lemma F_9476c : fetch_word Asan.M.loaded_segments (0x947bc : word) = Some W_9476c.
Proof. vm_refl. Qed.
Lemma D_9476c : decode_any W_9476c = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94770 : bv 32 := 0xaaa50513.
Lemma F_94770 : fetch_word Asan.M.loaded_segments (0x947c0 : word) = Some W_94770.
Proof. vm_refl. Qed.
Lemma D_94770 : decode_any W_94770 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_94774 : bv 32 := 0x00a12423.
Lemma F_94774 : fetch_word Asan.M.loaded_segments (0x947c4 : word) = Some W_94774.
Proof. vm_refl. Qed.
Lemma D_94774 : decode_any W_94774 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94778 : bv 32 := 0x00810593.
Lemma F_94778 : fetch_word Asan.M.loaded_segments (0x947c8 : word) = Some W_94778.
Proof. vm_refl. Qed.
Lemma D_94778 : decode_any W_94778 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9477c : bv 32 := 0x00090513.
Lemma F_9477c : fetch_word Asan.M.loaded_segments (0x947cc : word) = Some W_9477c.
Proof. vm_refl. Qed.
Lemma D_9477c : decode_any W_9477c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94780 : bv 32 := 0xe6cfe0ef.
Lemma F_94780 : fetch_word Asan.M.loaded_segments (0x947d0 : word) = Some W_94780.
Proof. vm_refl. Qed.
Lemma D_94780 : decode_any W_94780 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_94784 : bv 32 := 0x02051c63.
Lemma F_94784 : fetch_word Asan.M.loaded_segments (0x947d4 : word) = Some W_94784.
Proof. vm_refl. Qed.
Lemma D_94784 : decode_any W_94784 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94788 : bv 32 := 0x00048513.
Lemma F_94788 : fetch_word Asan.M.loaded_segments (0x947d8 : word) = Some W_94788.
Proof. vm_refl. Qed.
Lemma D_94788 : decode_any W_94788 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9478c : bv 32 := 0xd48fa0ef.
Lemma F_9478c : fetch_word Asan.M.loaded_segments (0x947dc : word) = Some W_9478c.
Proof. vm_refl. Qed.
Lemma D_9478c : decode_any W_9478c = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

Definition W_94790 : bv 32 := 0x00090513.
Lemma F_94790 : fetch_word Asan.M.loaded_segments (0x947e0 : word) = Some W_94790.
Proof. vm_refl. Qed.
Lemma D_94790 : decode_any W_94790 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94794 : bv 32 := 0x02813083.
Lemma F_94794 : fetch_word Asan.M.loaded_segments (0x947e4 : word) = Some W_94794.
Proof. vm_refl. Qed.
Lemma D_94794 : decode_any W_94794 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94798 : bv 32 := 0x02013403.
Lemma F_94798 : fetch_word Asan.M.loaded_segments (0x947e8 : word) = Some W_94798.
Proof. vm_refl. Qed.
Lemma D_94798 : decode_any W_94798 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9479c : bv 32 := 0x01813483.
Lemma F_9479c : fetch_word Asan.M.loaded_segments (0x947ec : word) = Some W_9479c.
Proof. vm_refl. Qed.
Lemma D_9479c : decode_any W_9479c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_947a0 : bv 32 := 0x01013903.
Lemma F_947a0 : fetch_word Asan.M.loaded_segments (0x947f0 : word) = Some W_947a0.
Proof. vm_refl. Qed.
Lemma D_947a0 : decode_any W_947a0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_947a4 : bv 32 := 0x03010113.
Lemma F_947a4 : fetch_word Asan.M.loaded_segments (0x947f4 : word) = Some W_947a4.
Proof. vm_refl. Qed.
Lemma D_947a4 : decode_any W_947a4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_947a8 : bv 32 := 0x00008067.
Lemma F_947a8 : fetch_word Asan.M.loaded_segments (0x947f8 : word) = Some W_947a8.
Proof. vm_refl. Qed.
Lemma D_947a8 : decode_any W_947a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b18 : bv 32 := 0x00060693.
Lemma F_94b18 : fetch_word Asan.M.loaded_segments (0x94b68 : word) = Some W_94b18.
Proof. vm_refl. Qed.
Lemma D_94b18 : decode_any W_94b18 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b1c : bv 32 := 0x00000613.
Lemma F_94b1c : fetch_word Asan.M.loaded_segments (0x94b6c : word) = Some W_94b1c.
Proof. vm_refl. Qed.
Lemma D_94b1c : decode_any W_94b1c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b20 : bv 32 := 0x0040006f.
Lemma F_94b20 : fetch_word Asan.M.loaded_segments (0x94b70 : word) = Some W_94b20.
Proof. vm_refl. Qed.
Lemma D_94b20 : decode_any W_94b20 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b24 : bv 32 := 0xfa010113.
Lemma F_94b24 : fetch_word Asan.M.loaded_segments (0x94b74 : word) = Some W_94b24.
Proof. vm_refl. Qed.
Lemma D_94b24 : decode_any W_94b24 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b28 : bv 32 := 0x04113c23.
Lemma F_94b28 : fetch_word Asan.M.loaded_segments (0x94b78 : word) = Some W_94b28.
Proof. vm_refl. Qed.
Lemma D_94b28 : decode_any W_94b28 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b2c : bv 32 := 0x04813823.
Lemma F_94b2c : fetch_word Asan.M.loaded_segments (0x94b7c : word) = Some W_94b2c.
Proof. vm_refl. Qed.
Lemma D_94b2c : decode_any W_94b2c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b30 : bv 32 := 0x04913423.
Lemma F_94b30 : fetch_word Asan.M.loaded_segments (0x94b80 : word) = Some W_94b30.
Proof. vm_refl. Qed.
Lemma D_94b30 : decode_any W_94b30 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b34 : bv 32 := 0x05213023.
Lemma F_94b34 : fetch_word Asan.M.loaded_segments (0x94b84 : word) = Some W_94b34.
Proof. vm_refl. Qed.
Lemma D_94b34 : decode_any W_94b34 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b38 : bv 32 := 0x03313c23.
Lemma F_94b38 : fetch_word Asan.M.loaded_segments (0x94b88 : word) = Some W_94b38.
Proof. vm_refl. Qed.
Lemma D_94b38 : decode_any W_94b38 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b3c : bv 32 := 0x03413823.
Lemma F_94b3c : fetch_word Asan.M.loaded_segments (0x94b8c : word) = Some W_94b3c.
Proof. vm_refl. Qed.
Lemma D_94b3c : decode_any W_94b3c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b40 : bv 32 := 0x00068993.
Lemma F_94b40 : fetch_word Asan.M.loaded_segments (0x94b90 : word) = Some W_94b40.
Proof. vm_refl. Qed.
Lemma D_94b40 : decode_any W_94b40 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b44 : bv 32 := 0x00060493.
Lemma F_94b44 : fetch_word Asan.M.loaded_segments (0x94b94 : word) = Some W_94b44.
Proof. vm_refl. Qed.
Lemma D_94b44 : decode_any W_94b44 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b48 : bv 32 := 0x00058413.
Lemma F_94b48 : fetch_word Asan.M.loaded_segments (0x94b98 : word) = Some W_94b48.
Proof. vm_refl. Qed.
Lemma D_94b48 : decode_any W_94b48 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b4c : bv 32 := 0x000be597.
Lemma F_94b4c : fetch_word Asan.M.loaded_segments (0x94b9c : word) = Some W_94b4c.
Proof. vm_refl. Qed.
Lemma D_94b4c : decode_any W_94b4c = Some (Auipc 11 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b50 : bv 32 := 0x57c5ba03.
Lemma F_94b50 : fetch_word Asan.M.loaded_segments (0x94ba0 : word) = Some W_94b50.
Proof. vm_refl. Qed.
Lemma D_94b50 : decode_any W_94b50 = Some (Load SZ8 true 20 11 1404, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b54 : bv 32 := 0x000a3583.
Lemma F_94b54 : fetch_word Asan.M.loaded_segments (0x94ba4 : word) = Some W_94b54.
Proof. vm_refl. Qed.
Lemma D_94b54 : decode_any W_94b54 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b58 : bv 32 := 0x00050913.
Lemma F_94b58 : fetch_word Asan.M.loaded_segments (0x94ba8 : word) = Some W_94b58.
Proof. vm_refl. Qed.
Lemma D_94b58 : decode_any W_94b58 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b5c : bv 32 := 0x00059863.
Lemma F_94b5c : fetch_word Asan.M.loaded_segments (0x94bac : word) = Some W_94b5c.
Proof. vm_refl. Qed.
Lemma D_94b5c : decode_any W_94b5c = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b6c : bv 32 := 0xfff58513.
Lemma F_94b6c : fetch_word Asan.M.loaded_segments (0x94bbc : word) = Some W_94b6c.
Proof. vm_refl. Qed.
Lemma D_94b6c : decode_any W_94b6c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b70 : bv 32 := 0x00a5f533.
Lemma F_94b70 : fetch_word Asan.M.loaded_segments (0x94bc0 : word) = Some W_94b70.
Proof. vm_refl. Qed.
Lemma D_94b70 : decode_any W_94b70 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b74 : bv 32 := 0x0a051863.
Lemma F_94b74 : fetch_word Asan.M.loaded_segments (0x94bc4 : word) = Some W_94b74.
Proof. vm_refl. Qed.
Lemma D_94b74 : decode_any W_94b74 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b78 : bv 32 := 0x00b40433.
Lemma F_94b78 : fetch_word Asan.M.loaded_segments (0x94bc8 : word) = Some W_94b78.
Proof. vm_refl. Qed.
Lemma D_94b78 : decode_any W_94b78 = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b7c : bv 32 := 0xfff40413.
Lemma F_94b7c : fetch_word Asan.M.loaded_segments (0x94bcc : word) = Some W_94b7c.
Proof. vm_refl. Qed.
Lemma D_94b7c : decode_any W_94b7c = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b80 : bv 32 := 0x40b00533.
Lemma F_94b80 : fetch_word Asan.M.loaded_segments (0x94bd0 : word) = Some W_94b80.
Proof. vm_refl. Qed.
Lemma D_94b80 : decode_any W_94b80 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b84 : bv 32 := 0x00a47433.
Lemma F_94b84 : fetch_word Asan.M.loaded_segments (0x94bd4 : word) = Some W_94b84.
Proof. vm_refl. Qed.
Lemma D_94b84 : decode_any W_94b84 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b88 : bv 32 := 0x00059863.
Lemma F_94b88 : fetch_word Asan.M.loaded_segments (0x94bd8 : word) = Some W_94b88.
Proof. vm_refl. Qed.
Lemma D_94b88 : decode_any W_94b88 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b98 : bv 32 := 0x00a97933.
Lemma F_94b98 : fetch_word Asan.M.loaded_segments (0x94be8 : word) = Some W_94b98.
Proof. vm_refl. Qed.
Lemma D_94b98 : decode_any W_94b98 = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b9c : bv 32 := 0x03200513.
Lemma F_94b9c : fetch_word Asan.M.loaded_segments (0x94bec : word) = Some W_94b9c.
Proof. vm_refl. Qed.
Lemma D_94b9c : decode_any W_94b9c = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ba0 : bv 32 := 0x00a12023.
Lemma F_94ba0 : fetch_word Asan.M.loaded_segments (0x94bf0 : word) = Some W_94ba0.
Proof. vm_refl. Qed.
Lemma D_94ba0 : decode_any W_94ba0 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ba4 : bv 32 := 0x00010613.
Lemma F_94ba4 : fetch_word Asan.M.loaded_segments (0x94bf4 : word) = Some W_94ba4.
Proof. vm_refl. Qed.
Lemma D_94ba4 : decode_any W_94ba4 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ba8 : bv 32 := 0x00098513.
Lemma F_94ba8 : fetch_word Asan.M.loaded_segments (0x94bf8 : word) = Some W_94ba8.
Proof. vm_refl. Qed.
Lemma D_94ba8 : decode_any W_94ba8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bac : bv 32 := 0x00040593.
Lemma F_94bac : fetch_word Asan.M.loaded_segments (0x94bfc : word) = Some W_94bac.
Proof. vm_refl. Qed.
Lemma D_94bac : decode_any W_94bac = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bb0 : bv 32 := 0x608000ef.
Lemma F_94bb0 : fetch_word Asan.M.loaded_segments (0x94c00 : word) = Some W_94bb0.
Proof. vm_refl. Qed.
Lemma D_94bb0 : decode_any W_94bb0 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bb4 : bv 32 := 0x00012683.
Lemma F_94bb4 : fetch_word Asan.M.loaded_segments (0x94c04 : word) = Some W_94bb4.
Proof. vm_refl. Qed.
Lemma D_94bb4 : decode_any W_94bb4 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bb8 : bv 32 := 0x00050713.
Lemma F_94bb8 : fetch_word Asan.M.loaded_segments (0x94c08 : word) = Some W_94bb8.
Proof. vm_refl. Qed.
Lemma D_94bb8 : decode_any W_94bb8 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bbc : bv 32 := 0x00300613.
Lemma F_94bbc : fetch_word Asan.M.loaded_segments (0x94c0c : word) = Some W_94bbc.
Proof. vm_refl. Qed.
Lemma D_94bbc : decode_any W_94bbc = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bc0 : bv 32 := 0x00090513.
Lemma F_94bc0 : fetch_word Asan.M.loaded_segments (0x94c10 : word) = Some W_94bc0.
Proof. vm_refl. Qed.
Lemma D_94bc0 : decode_any W_94bc0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bc4 : bv 32 := 0x00040593.
Lemma F_94bc4 : fetch_word Asan.M.loaded_segments (0x94c14 : word) = Some W_94bc4.
Proof. vm_refl. Qed.
Lemma D_94bc4 : decode_any W_94bc4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bc8 : bv 32 := 0x00000793.
Lemma F_94bc8 : fetch_word Asan.M.loaded_segments (0x94c18 : word) = Some W_94bc8.
Proof. vm_refl. Qed.
Lemma D_94bc8 : decode_any W_94bc8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bcc : bv 32 := 0xa40fe0ef.
Lemma F_94bcc : fetch_word Asan.M.loaded_segments (0x94c1c : word) = Some W_94bcc.
Proof. vm_refl. Qed.
Lemma D_94bcc : decode_any W_94bcc = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bd0 : bv 32 := 0x00050993.
Lemma F_94bd0 : fetch_word Asan.M.loaded_segments (0x94c20 : word) = Some W_94bd0.
Proof. vm_refl. Qed.
Lemma D_94bd0 : decode_any W_94bd0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bd4 : bv 32 := 0x00000593.
Lemma F_94bd4 : fetch_word Asan.M.loaded_segments (0x94c24 : word) = Some W_94bd4.
Proof. vm_refl. Qed.
Lemma D_94bd4 : decode_any W_94bd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bd8 : bv 32 := 0xa14fe0ef.
Lemma F_94bd8 : fetch_word Asan.M.loaded_segments (0x94c28 : word) = Some W_94bd8.
Proof. vm_refl. Qed.
Lemma D_94bd8 : decode_any W_94bd8 = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bdc : bv 32 := 0xaaaab537.
Lemma F_94bdc : fetch_word Asan.M.loaded_segments (0x94c2c : word) = Some W_94bdc.
Proof. vm_refl. Qed.
Lemma D_94bdc : decode_any W_94bdc = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94be0 : bv 32 := 0xaaa50513.
Lemma F_94be0 : fetch_word Asan.M.loaded_segments (0x94c30 : word) = Some W_94be0.
Proof. vm_refl. Qed.
Lemma D_94be0 : decode_any W_94be0 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_94be4 : bv 32 := 0x02a12623.
Lemma F_94be4 : fetch_word Asan.M.loaded_segments (0x94c34 : word) = Some W_94be4.
Proof. vm_refl. Qed.
Lemma D_94be4 : decode_any W_94be4 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_94be8 : bv 32 := 0x02c10593.
Lemma F_94be8 : fetch_word Asan.M.loaded_segments (0x94c38 : word) = Some W_94be8.
Proof. vm_refl. Qed.
Lemma D_94be8 : decode_any W_94be8 = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bec : bv 32 := 0x00098513.
Lemma F_94bec : fetch_word Asan.M.loaded_segments (0x94c3c : word) = Some W_94bec.
Proof. vm_refl. Qed.
Lemma D_94bec : decode_any W_94bec = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bf0 : bv 32 := 0x9fcfe0ef.
Lemma F_94bf0 : fetch_word Asan.M.loaded_segments (0x94c40 : word) = Some W_94bf0.
Proof. vm_refl. Qed.
Lemma D_94bf0 : decode_any W_94bf0 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bf4 : bv 32 := 0x04051063.
Lemma F_94bf4 : fetch_word Asan.M.loaded_segments (0x94c44 : word) = Some W_94bf4.
Proof. vm_refl. Qed.
Lemma D_94bf4 : decode_any W_94bf4 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bf8 : bv 32 := 0x00040513.
Lemma F_94bf8 : fetch_word Asan.M.loaded_segments (0x94c48 : word) = Some W_94bf8.
Proof. vm_refl. Qed.
Lemma D_94bf8 : decode_any W_94bf8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94bfc : bv 32 := 0x8d8fa0ef.
Lemma F_94bfc : fetch_word Asan.M.loaded_segments (0x94c4c : word) = Some W_94bfc.
Proof. vm_refl. Qed.
Lemma D_94bfc : decode_any W_94bfc = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c00 : bv 32 := 0x00098513.
Lemma F_94c00 : fetch_word Asan.M.loaded_segments (0x94c50 : word) = Some W_94c00.
Proof. vm_refl. Qed.
Lemma D_94c00 : decode_any W_94c00 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c04 : bv 32 := 0x05813083.
Lemma F_94c04 : fetch_word Asan.M.loaded_segments (0x94c54 : word) = Some W_94c04.
Proof. vm_refl. Qed.
Lemma D_94c04 : decode_any W_94c04 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c08 : bv 32 := 0x05013403.
Lemma F_94c08 : fetch_word Asan.M.loaded_segments (0x94c58 : word) = Some W_94c08.
Proof. vm_refl. Qed.
Lemma D_94c08 : decode_any W_94c08 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c0c : bv 32 := 0x04813483.
Lemma F_94c0c : fetch_word Asan.M.loaded_segments (0x94c5c : word) = Some W_94c0c.
Proof. vm_refl. Qed.
Lemma D_94c0c : decode_any W_94c0c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c10 : bv 32 := 0x04013903.
Lemma F_94c10 : fetch_word Asan.M.loaded_segments (0x94c60 : word) = Some W_94c10.
Proof. vm_refl. Qed.
Lemma D_94c10 : decode_any W_94c10 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c14 : bv 32 := 0x03813983.
Lemma F_94c14 : fetch_word Asan.M.loaded_segments (0x94c64 : word) = Some W_94c14.
Proof. vm_refl. Qed.
Lemma D_94c14 : decode_any W_94c14 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c18 : bv 32 := 0x03013a03.
Lemma F_94c18 : fetch_word Asan.M.loaded_segments (0x94c68 : word) = Some W_94c18.
Proof. vm_refl. Qed.
Lemma D_94c18 : decode_any W_94c18 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c1c : bv 32 := 0x06010113.
Lemma F_94c1c : fetch_word Asan.M.loaded_segments (0x94c6c : word) = Some W_94c1c.
Proof. vm_refl. Qed.
Lemma D_94c1c : decode_any W_94c1c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c20 : bv 32 := 0x00008067.
Lemma F_94c20 : fetch_word Asan.M.loaded_segments (0x94c70 : word) = Some W_94c20.
Proof. vm_refl. Qed.
Lemma D_94c20 : decode_any W_94c20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94c9c : bv 32 := 0x00060693.
Lemma F_94c9c : fetch_word Asan.M.loaded_segments (0x94cec : word) = Some W_94c9c.
Proof. vm_refl. Qed.
Lemma D_94c9c : decode_any W_94c9c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ca0 : bv 32 := 0x00100613.
Lemma F_94ca0 : fetch_word Asan.M.loaded_segments (0x94cf0 : word) = Some W_94ca0.
Proof. vm_refl. Qed.
Lemma D_94ca0 : decode_any W_94ca0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_94ca4 : bv 32 := 0xe81ff06f.
Lemma F_94ca4 : fetch_word Asan.M.loaded_segments (0x94cf4 : word) = Some W_94ca4.
Proof. vm_refl. Qed.
Lemma D_94ca4 : decode_any W_94ca4 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

