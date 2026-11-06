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

Definition W_88274 : bv 32 := 0xff010113.
Lemma F_88274 : fetch_word Asan.M.loaded_segments (0x882c4 : word) = Some W_88274.
Proof. vm_refl. Qed.
Lemma D_88274 : decode_any W_88274 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_88278 : bv 32 := 0x00113423.
Lemma F_88278 : fetch_word Asan.M.loaded_segments (0x882c8 : word) = Some W_88278.
Proof. vm_refl. Qed.
Lemma D_88278 : decode_any W_88278 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8827c : bv 32 := 0x00813023.
Lemma F_8827c : fetch_word Asan.M.loaded_segments (0x882cc : word) = Some W_8827c.
Proof. vm_refl. Qed.
Lemma D_8827c : decode_any W_8827c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88280 : bv 32 := 0x000d5517.
Lemma F_88280 : fetch_word Asan.M.loaded_segments (0x882d0 : word) = Some W_88280.
Proof. vm_refl. Qed.
Lemma D_88280 : decode_any W_88280 = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_88284 : bv 32 := 0x3c850413.
Lemma F_88284 : fetch_word Asan.M.loaded_segments (0x882d4 : word) = Some W_88284.
Proof. vm_refl. Qed.
Lemma D_88284 : decode_any W_88284 = Some (OpImm ALU_ADD 8 10 968, 4%Z).
Proof. vm_refl. Qed.

Definition W_88288 : bv 32 := 0x00040583.
Lemma F_88288 : fetch_word Asan.M.loaded_segments (0x882d8 : word) = Some W_88288.
Proof. vm_refl. Qed.
Lemma D_88288 : decode_any W_88288 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8828c : bv 32 := 0x00100513.
Lemma F_8828c : fetch_word Asan.M.loaded_segments (0x882dc : word) = Some W_8828c.
Proof. vm_refl. Qed.
Lemma D_8828c : decode_any W_8828c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88290 : bv 32 := 0x0230000f.
Lemma F_88290 : fetch_word Asan.M.loaded_segments (0x882e0 : word) = Some W_88290.
Proof. vm_refl. Qed.
Lemma D_88290 : decode_any W_88290 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88294 : bv 32 := 0x00a59a63.
Lemma F_88294 : fetch_word Asan.M.loaded_segments (0x882e4 : word) = Some W_88294.
Proof. vm_refl. Qed.
Lemma D_88294 : decode_any W_88294 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_88298 : bv 32 := 0x00813083.
Lemma F_88298 : fetch_word Asan.M.loaded_segments (0x882e8 : word) = Some W_88298.
Proof. vm_refl. Qed.
Lemma D_88298 : decode_any W_88298 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8829c : bv 32 := 0x00013403.
Lemma F_8829c : fetch_word Asan.M.loaded_segments (0x882ec : word) = Some W_8829c.
Proof. vm_refl. Qed.
Lemma D_8829c : decode_any W_8829c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_882a0 : bv 32 := 0x01010113.
Lemma F_882a0 : fetch_word Asan.M.loaded_segments (0x882f0 : word) = Some W_882a0.
Proof. vm_refl. Qed.
Lemma D_882a0 : decode_any W_882a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_882a4 : bv 32 := 0x00008067.
Lemma F_882a4 : fetch_word Asan.M.loaded_segments (0x882f4 : word) = Some W_882a4.
Proof. vm_refl. Qed.
Lemma D_882a4 : decode_any W_882a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88378 : bv 32 := 0xfb010113.
Lemma F_88378 : fetch_word Asan.M.loaded_segments (0x883c8 : word) = Some W_88378.
Proof. vm_refl. Qed.
Lemma D_88378 : decode_any W_88378 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8837c : bv 32 := 0x04113423.
Lemma F_8837c : fetch_word Asan.M.loaded_segments (0x883cc : word) = Some W_8837c.
Proof. vm_refl. Qed.
Lemma D_8837c : decode_any W_8837c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_88380 : bv 32 := 0x04813023.
Lemma F_88380 : fetch_word Asan.M.loaded_segments (0x883d0 : word) = Some W_88380.
Proof. vm_refl. Qed.
Lemma D_88380 : decode_any W_88380 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_88384 : bv 32 := 0x02913c23.
Lemma F_88384 : fetch_word Asan.M.loaded_segments (0x883d4 : word) = Some W_88384.
Proof. vm_refl. Qed.
Lemma D_88384 : decode_any W_88384 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_88388 : bv 32 := 0x03213823.
Lemma F_88388 : fetch_word Asan.M.loaded_segments (0x883d8 : word) = Some W_88388.
Proof. vm_refl. Qed.
Lemma D_88388 : decode_any W_88388 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8838c : bv 32 := 0x03313423.
Lemma F_8838c : fetch_word Asan.M.loaded_segments (0x883dc : word) = Some W_8838c.
Proof. vm_refl. Qed.
Lemma D_8838c : decode_any W_8838c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_88390 : bv 32 := 0x000d5517.
Lemma F_88390 : fetch_word Asan.M.loaded_segments (0x883e0 : word) = Some W_88390.
Proof. vm_refl. Qed.
Lemma D_88390 : decode_any W_88390 = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_88394 : bv 32 := 0x2b850493.
Lemma F_88394 : fetch_word Asan.M.loaded_segments (0x883e4 : word) = Some W_88394.
Proof. vm_refl. Qed.
Lemma D_88394 : decode_any W_88394 = Some (OpImm ALU_ADD 9 10 696, 4%Z).
Proof. vm_refl. Qed.

Definition W_88398 : bv 32 := 0x00048503.
Lemma F_88398 : fetch_word Asan.M.loaded_segments (0x883e8 : word) = Some W_88398.
Proof. vm_refl. Qed.
Lemma D_88398 : decode_any W_88398 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8839c : bv 32 := 0x00100593.
Lemma F_8839c : fetch_word Asan.M.loaded_segments (0x883ec : word) = Some W_8839c.
Proof. vm_refl. Qed.
Lemma D_8839c : decode_any W_8839c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_883a0 : bv 32 := 0x0230000f.
Lemma F_883a0 : fetch_word Asan.M.loaded_segments (0x883f0 : word) = Some W_883a0.
Proof. vm_refl. Qed.
Lemma D_883a0 : decode_any W_883a0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_883a4 : bv 32 := 0x10b51e63.
Lemma F_883a4 : fetch_word Asan.M.loaded_segments (0x883f4 : word) = Some W_883a4.
Proof. vm_refl. Qed.
Lemma D_883a4 : decode_any W_883a4 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_883a8 : bv 32 := 0xbe1fa0ef.
Lemma F_883a8 : fetch_word Asan.M.loaded_segments (0x883f8 : word) = Some W_883a8.
Proof. vm_refl. Qed.
Lemma D_883a8 : decode_any W_883a8 = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

Definition W_883ac : bv 32 := 0x0e051663.
Lemma F_883ac : fetch_word Asan.M.loaded_segments (0x883fc : word) = Some W_883ac.
Proof. vm_refl. Qed.
Lemma D_883ac : decode_any W_883ac = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_883b0 : bv 32 := 0xfff88517.
Lemma F_883b0 : fetch_word Asan.M.loaded_segments (0x88400 : word) = Some W_883b0.
Proof. vm_refl. Qed.
Lemma D_883b0 : decode_any W_883b0 = Some (Auipc 10 1048456, 4%Z).
Proof. vm_refl. Qed.

Definition W_883b4 : bv 32 := 0x08053403.
Lemma F_883b4 : fetch_word Asan.M.loaded_segments (0x88404 : word) = Some W_883b4.
Proof. vm_refl. Qed.
Lemma D_883b4 : decode_any W_883b4 = Some (Load SZ8 true 8 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_883b8 : bv 32 := 0x02813023.
Lemma F_883b8 : fetch_word Asan.M.loaded_segments (0x88408 : word) = Some W_883b8.
Proof. vm_refl. Qed.
Lemma D_883b8 : decode_any W_883b8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_883bc : bv 32 := 0x00813c23.
Lemma F_883bc : fetch_word Asan.M.loaded_segments (0x8840c : word) = Some W_883bc.
Proof. vm_refl. Qed.
Lemma D_883bc : decode_any W_883bc = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_883c0 : bv 32 := 0x6b4020ef.
Lemma F_883c0 : fetch_word Asan.M.loaded_segments (0x88410 : word) = Some W_883c0.
Proof. vm_refl. Qed.
Lemma D_883c0 : decode_any W_883c0 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_883c4 : bv 32 := 0x08050263.
Lemma F_883c4 : fetch_word Asan.M.loaded_segments (0x88414 : word) = Some W_883c4.
Proof. vm_refl. Qed.
Lemma D_883c4 : decode_any W_883c4 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_883c8 : bv 32 := 0x000cb597.
Lemma F_883c8 : fetch_word Asan.M.loaded_segments (0x88418 : word) = Some W_883c8.
Proof. vm_refl. Qed.
Lemma D_883c8 : decode_any W_883c8 = Some (Auipc 11 203, 4%Z).
Proof. vm_refl. Qed.

Definition W_883cc : bv 32 := 0xd005b903.
Lemma F_883cc : fetch_word Asan.M.loaded_segments (0x8841c : word) = Some W_883cc.
Proof. vm_refl. Qed.
Lemma D_883cc : decode_any W_883cc = Some (Load SZ8 true 18 11 3328, 4%Z).
Proof. vm_refl. Qed.

Definition W_883d0 : bv 32 := 0x00093403.
Lemma F_883d0 : fetch_word Asan.M.loaded_segments (0x88420 : word) = Some W_883d0.
Proof. vm_refl. Qed.
Lemma D_883d0 : decode_any W_883d0 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_883d4 : bv 32 := 0x00041c63.
Lemma F_883d4 : fetch_word Asan.M.loaded_segments (0x88424 : word) = Some W_883d4.
Proof. vm_refl. Qed.
Lemma D_883d4 : decode_any W_883d4 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_883ec : bv 32 := 0x04d020ef.
Lemma F_883ec : fetch_word Asan.M.loaded_segments (0x8843c : word) = Some W_883ec.
Proof. vm_refl. Qed.
Lemma D_883ec : decode_any W_883ec = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_883f0 : bv 32 := 0x00050613.
Lemma F_883f0 : fetch_word Asan.M.loaded_segments (0x88440 : word) = Some W_883f0.
Proof. vm_refl. Qed.
Lemma D_883f0 : decode_any W_883f0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_883f4 : bv 32 := 0x00a13c23.
Lemma F_883f4 : fetch_word Asan.M.loaded_segments (0x88444 : word) = Some W_883f4.
Proof. vm_refl. Qed.
Lemma D_883f4 : decode_any W_883f4 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_883f8 : bv 32 := 0x01010513.
Lemma F_883f8 : fetch_word Asan.M.loaded_segments (0x88448 : word) = Some W_883f8.
Proof. vm_refl. Qed.
Lemma D_883f8 : decode_any W_883f8 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_883fc : bv 32 := 0x40850533.
Lemma F_883fc : fetch_word Asan.M.loaded_segments (0x8844c : word) = Some W_883fc.
Proof. vm_refl. Qed.
Lemma D_883fc : decode_any W_883fc = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88400 : bv 32 := 0x408006b3.
Lemma F_88400 : fetch_word Asan.M.loaded_segments (0x88450 : word) = Some W_88400.
Proof. vm_refl. Qed.
Lemma D_88400 : decode_any W_88400 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88404 : bv 32 := 0x00d576b3.
Lemma F_88404 : fetch_word Asan.M.loaded_segments (0x88454 : word) = Some W_88404.
Proof. vm_refl. Qed.
Lemma D_88404 : decode_any W_88404 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_88408 : bv 32 := 0x02d13023.
Lemma F_88408 : fetch_word Asan.M.loaded_segments (0x88458 : word) = Some W_88408.
Proof. vm_refl. Qed.
Lemma D_88408 : decode_any W_88408 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8840c : bv 32 := 0x40d60733.
Lemma F_8840c : fetch_word Asan.M.loaded_segments (0x8845c : word) = Some W_8840c.
Proof. vm_refl. Qed.
Lemma D_8840c : decode_any W_8840c = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_88410 : bv 32 := 0x04000537.
Lemma F_88410 : fetch_word Asan.M.loaded_segments (0x88460 : word) = Some W_88410.
Proof. vm_refl. Qed.
Lemma D_88410 : decode_any W_88410 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_88414 : bv 32 := 0x0015051b.
Lemma F_88414 : fetch_word Asan.M.loaded_segments (0x88464 : word) = Some W_88414.
Proof. vm_refl. Qed.
Lemma D_88414 : decode_any W_88414 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88418 : bv 32 := 0x06a76263.
Lemma F_88418 : fetch_word Asan.M.loaded_segments (0x88468 : word) = Some W_88418.
Proof. vm_refl. Qed.
Lemma D_88418 : decode_any W_88418 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8847c : bv 32 := 0x00770713.
Lemma F_8847c : fetch_word Asan.M.loaded_segments (0x884cc : word) = Some W_8847c.
Proof. vm_refl. Qed.
Lemma D_8847c : decode_any W_8847c = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_88480 : bv 32 := 0x10000537.
Lemma F_88480 : fetch_word Asan.M.loaded_segments (0x884d0 : word) = Some W_88480.
Proof. vm_refl. Qed.
Lemma D_88480 : decode_any W_88480 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_88484 : bv 32 := 0xff85051b.
Lemma F_88484 : fetch_word Asan.M.loaded_segments (0x884d4 : word) = Some W_88484.
Proof. vm_refl. Qed.
Lemma D_88484 : decode_any W_88484 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_88488 : bv 32 := 0x00a775b3.
Lemma F_88488 : fetch_word Asan.M.loaded_segments (0x884d8 : word) = Some W_88488.
Proof. vm_refl. Qed.
Lemma D_88488 : decode_any W_88488 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8848c : bv 32 := 0x00068513.
Lemma F_8848c : fetch_word Asan.M.loaded_segments (0x884dc : word) = Some W_8848c.
Proof. vm_refl. Qed.
Lemma D_8848c : decode_any W_8848c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88490 : bv 32 := 0x00000613.
Lemma F_88490 : fetch_word Asan.M.loaded_segments (0x884e0 : word) = Some W_88490.
Proof. vm_refl. Qed.
Lemma D_88490 : decode_any W_88490 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88494 : bv 32 := 0x835f90ef.
Lemma F_88494 : fetch_word Asan.M.loaded_segments (0x884e4 : word) = Some W_88494.
Proof. vm_refl. Qed.
Lemma D_88494 : decode_any W_88494 = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

Definition W_88498 : bv 32 := 0x5dc020ef.
Lemma F_88498 : fetch_word Asan.M.loaded_segments (0x884e8 : word) = Some W_88498.
Proof. vm_refl. Qed.
Lemma D_88498 : decode_any W_88498 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_8849c : bv 32 := 0x02050263.
Lemma F_8849c : fetch_word Asan.M.loaded_segments (0x884ec : word) = Some W_8849c.
Proof. vm_refl. Qed.
Lemma D_8849c : decode_any W_8849c = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_884a0 : bv 32 := 0x02850583.
Lemma F_884a0 : fetch_word Asan.M.loaded_segments (0x884f0 : word) = Some W_884a0.
Proof. vm_refl. Qed.
Lemma D_884a0 : decode_any W_884a0 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_884a4 : bv 32 := 0x00059e63.
Lemma F_884a4 : fetch_word Asan.M.loaded_segments (0x884f4 : word) = Some W_884a4.
Proof. vm_refl. Qed.
Lemma D_884a4 : decode_any W_884a4 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_884a8 : bv 32 := 0x04853503.
Lemma F_884a8 : fetch_word Asan.M.loaded_segments (0x884f8 : word) = Some W_884a8.
Proof. vm_refl. Qed.
Lemma D_884a8 : decode_any W_884a8 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_884ac : bv 32 := 0x00253593.
Lemma F_884ac : fetch_word Asan.M.loaded_segments (0x884fc : word) = Some W_884ac.
Proof. vm_refl. Qed.
Lemma D_884ac : decode_any W_884ac = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_884b0 : bv 32 := 0xfff58593.
Lemma F_884b0 : fetch_word Asan.M.loaded_segments (0x88500 : word) = Some W_884b0.
Proof. vm_refl. Qed.
Lemma D_884b0 : decode_any W_884b0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_884b4 : bv 32 := 0x00a5f533.
Lemma F_884b4 : fetch_word Asan.M.loaded_segments (0x88504 : word) = Some W_884b4.
Proof. vm_refl. Qed.
Lemma D_884b4 : decode_any W_884b4 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_884b8 : bv 32 := 0x00050463.
Lemma F_884b8 : fetch_word Asan.M.loaded_segments (0x88508 : word) = Some W_884b8.
Proof. vm_refl. Qed.
Lemma D_884b8 : decode_any W_884b8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_884bc : bv 32 := 0xc34dc0ef.
Lemma F_884bc : fetch_word Asan.M.loaded_segments (0x8850c : word) = Some W_884bc.
Proof. vm_refl. Qed.
Lemma D_884bc : decode_any W_884bc = Some (Jal 1 1950772, 4%Z).
Proof. vm_refl. Qed.

Definition W_884c0 : bv 32 := 0x04813083.
Lemma F_884c0 : fetch_word Asan.M.loaded_segments (0x88510 : word) = Some W_884c0.
Proof. vm_refl. Qed.
Lemma D_884c0 : decode_any W_884c0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_884c4 : bv 32 := 0x04013403.
Lemma F_884c4 : fetch_word Asan.M.loaded_segments (0x88514 : word) = Some W_884c4.
Proof. vm_refl. Qed.
Lemma D_884c4 : decode_any W_884c4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_884c8 : bv 32 := 0x03813483.
Lemma F_884c8 : fetch_word Asan.M.loaded_segments (0x88518 : word) = Some W_884c8.
Proof. vm_refl. Qed.
Lemma D_884c8 : decode_any W_884c8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_884cc : bv 32 := 0x03013903.
Lemma F_884cc : fetch_word Asan.M.loaded_segments (0x8851c : word) = Some W_884cc.
Proof. vm_refl. Qed.
Lemma D_884cc : decode_any W_884cc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_884d0 : bv 32 := 0x02813983.
Lemma F_884d0 : fetch_word Asan.M.loaded_segments (0x88520 : word) = Some W_884d0.
Proof. vm_refl. Qed.
Lemma D_884d0 : decode_any W_884d0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_884d4 : bv 32 := 0x05010113.
Lemma F_884d4 : fetch_word Asan.M.loaded_segments (0x88524 : word) = Some W_884d4.
Proof. vm_refl. Qed.
Lemma D_884d4 : decode_any W_884d4 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_884d8 : bv 32 := 0x00008067.
Lemma F_884d8 : fetch_word Asan.M.loaded_segments (0x88528 : word) = Some W_884d8.
Proof. vm_refl. Qed.
Lemma D_884d8 : decode_any W_884d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ffc : bv 32 := 0x000d4517.
Lemma F_88ffc : fetch_word Asan.M.loaded_segments (0x8904c : word) = Some W_88ffc.
Proof. vm_refl. Qed.
Lemma D_88ffc : decode_any W_88ffc = Some (Auipc 10 212, 4%Z).
Proof. vm_refl. Qed.

