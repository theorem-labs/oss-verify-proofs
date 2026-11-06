(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_86294 : bv 32 := 0xfd010113.
Lemma F_86294 : fetch_word Asan.M.loaded_segments (0x862e4 : word) = Some W_86294.
Proof. vm_refl. Qed.
Lemma D_86294 : decode_any W_86294 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_86298 : bv 32 := 0x02113423.
Lemma F_86298 : fetch_word Asan.M.loaded_segments (0x862e8 : word) = Some W_86298.
Proof. vm_refl. Qed.
Lemma D_86298 : decode_any W_86298 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8629c : bv 32 := 0x02813023.
Lemma F_8629c : fetch_word Asan.M.loaded_segments (0x862ec : word) = Some W_8629c.
Proof. vm_refl. Qed.
Lemma D_8629c : decode_any W_8629c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_862a0 : bv 32 := 0x00913c23.
Lemma F_862a0 : fetch_word Asan.M.loaded_segments (0x862f0 : word) = Some W_862a0.
Proof. vm_refl. Qed.
Lemma D_862a0 : decode_any W_862a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_862a4 : bv 32 := 0x01213823.
Lemma F_862a4 : fetch_word Asan.M.loaded_segments (0x862f4 : word) = Some W_862a4.
Proof. vm_refl. Qed.
Lemma D_862a4 : decode_any W_862a4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_862a8 : bv 32 := 0x01313423.
Lemma F_862a8 : fetch_word Asan.M.loaded_segments (0x862f8 : word) = Some W_862a8.
Proof. vm_refl. Qed.
Lemma D_862a8 : decode_any W_862a8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_862ac : bv 32 := 0x0014b517.
Lemma F_862ac : fetch_word Asan.M.loaded_segments (0x862fc : word) = Some W_862ac.
Proof. vm_refl. Qed.
Lemma D_862ac : decode_any W_862ac = Some (Auipc 10 331, 4%Z).
Proof. vm_refl. Qed.

Definition W_862b0 : bv 32 := 0x18c50413.
Lemma F_862b0 : fetch_word Asan.M.loaded_segments (0x86300 : word) = Some W_862b0.
Proof. vm_refl. Qed.
Lemma D_862b0 : decode_any W_862b0 = Some (OpImm ALU_ADD 8 10 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_862b4 : bv 32 := 0x00040503.
Lemma F_862b4 : fetch_word Asan.M.loaded_segments (0x86304 : word) = Some W_862b4.
Proof. vm_refl. Qed.
Lemma D_862b4 : decode_any W_862b4 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_862b8 : bv 32 := 0x0230000f.
Lemma F_862b8 : fetch_word Asan.M.loaded_segments (0x86308 : word) = Some W_862b8.
Proof. vm_refl. Qed.
Lemma D_862b8 : decode_any W_862b8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_862bc : bv 32 := 0x0e051e63.
Lemma F_862bc : fetch_word Asan.M.loaded_segments (0x8630c : word) = Some W_862bc.
Proof. vm_refl. Qed.
Lemma D_862bc : decode_any W_862bc = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_862c0 : bv 32 := 0x00140513.
Lemma F_862c0 : fetch_word Asan.M.loaded_segments (0x86310 : word) = Some W_862c0.
Proof. vm_refl. Qed.
Lemma D_862c0 : decode_any W_862c0 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_862c4 : bv 32 := 0x0ff00593.
Lemma F_862c4 : fetch_word Asan.M.loaded_segments (0x86314 : word) = Some W_862c4.
Proof. vm_refl. Qed.
Lemma D_862c4 : decode_any W_862c4 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_862c8 : bv 32 := 0x00100613.
Lemma F_862c8 : fetch_word Asan.M.loaded_segments (0x86318 : word) = Some W_862c8.
Proof. vm_refl. Qed.
Lemma D_862c8 : decode_any W_862c8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_862cc : bv 32 := 0xffc57693.
Lemma F_862cc : fetch_word Asan.M.loaded_segments (0x8631c : word) = Some W_862cc.
Proof. vm_refl. Qed.
Lemma D_862cc : decode_any W_862cc = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_862d0 : bv 32 := 0x00357713.
Lemma F_862d0 : fetch_word Asan.M.loaded_segments (0x86320 : word) = Some W_862d0.
Proof. vm_refl. Qed.
Lemma D_862d0 : decode_any W_862d0 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_862d4 : bv 32 := 0x00371713.
Lemma F_862d4 : fetch_word Asan.M.loaded_segments (0x86324 : word) = Some W_862d4.
Proof. vm_refl. Qed.
Lemma D_862d4 : decode_any W_862d4 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_862d8 : bv 32 := 0x00e595bb.
Lemma F_862d8 : fetch_word Asan.M.loaded_segments (0x86328 : word) = Some W_862d8.
Proof. vm_refl. Qed.
Lemma D_862d8 : decode_any W_862d8 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_862dc : bv 32 := 0x00e6163b.
Lemma F_862dc : fetch_word Asan.M.loaded_segments (0x8632c : word) = Some W_862dc.
Proof. vm_refl. Qed.
Lemma D_862dc : decode_any W_862dc = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_862e0 : bv 32 := 0x1406a7af.
Lemma F_862e0 : fetch_word Asan.M.loaded_segments (0x86330 : word) = Some W_862e0.
Proof. vm_refl. Qed.
Lemma D_862e0 : decode_any W_862e0 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_862e4 : bv 32 := 0x00060813.
Lemma F_862e4 : fetch_word Asan.M.loaded_segments (0x86334 : word) = Some W_862e4.
Proof. vm_refl. Qed.
Lemma D_862e4 : decode_any W_862e4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_862e8 : bv 32 := 0x0107c833.
Lemma F_862e8 : fetch_word Asan.M.loaded_segments (0x86338 : word) = Some W_862e8.
Proof. vm_refl. Qed.
Lemma D_862e8 : decode_any W_862e8 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_862ec : bv 32 := 0x00b87833.
Lemma F_862ec : fetch_word Asan.M.loaded_segments (0x8633c : word) = Some W_862ec.
Proof. vm_refl. Qed.
Lemma D_862ec : decode_any W_862ec = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_862f0 : bv 32 := 0x0107c833.
Lemma F_862f0 : fetch_word Asan.M.loaded_segments (0x86340 : word) = Some W_862f0.
Proof. vm_refl. Qed.
Lemma D_862f0 : decode_any W_862f0 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_862f4 : bv 32 := 0x1906a82f.
Lemma F_862f4 : fetch_word Asan.M.loaded_segments (0x86344 : word) = Some W_862f4.
Proof. vm_refl. Qed.
Lemma D_862f4 : decode_any W_862f4 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_862f8 : bv 32 := 0xfe0814e3.
Lemma F_862f8 : fetch_word Asan.M.loaded_segments (0x86348 : word) = Some W_862f8.
Proof. vm_refl. Qed.
Lemma D_862f8 : decode_any W_862f8 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_862fc : bv 32 := 0x00e7d5bb.
Lemma F_862fc : fetch_word Asan.M.loaded_segments (0x8634c : word) = Some W_862fc.
Proof. vm_refl. Qed.
Lemma D_862fc : decode_any W_862fc = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_86300 : bv 32 := 0x0ff5f593.
Lemma F_86300 : fetch_word Asan.M.loaded_segments (0x86350 : word) = Some W_86300.
Proof. vm_refl. Qed.
Lemma D_86300 : decode_any W_86300 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_86304 : bv 32 := 0x0c059c63.
Lemma F_86304 : fetch_word Asan.M.loaded_segments (0x86354 : word) = Some W_86304.
Proof. vm_refl. Qed.
Lemma D_86304 : decode_any W_86304 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_86308 : bv 32 := 0x00040503.
Lemma F_86308 : fetch_word Asan.M.loaded_segments (0x86358 : word) = Some W_86308.
Proof. vm_refl. Qed.
Lemma D_86308 : decode_any W_86308 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8630c : bv 32 := 0x0a051263.
Lemma F_8630c : fetch_word Asan.M.loaded_segments (0x8635c : word) = Some W_8630c.
Proof. vm_refl. Qed.
Lemma D_8630c : decode_any W_8630c = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_86310 : bv 32 := 0x000bd517.
Lemma F_86310 : fetch_word Asan.M.loaded_segments (0x86360 : word) = Some W_86310.
Proof. vm_refl. Qed.
Lemma D_86310 : decode_any W_86310 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_86314 : bv 32 := 0x000815b7.
Lemma F_86314 : fetch_word Asan.M.loaded_segments (0x86364 : word) = Some W_86314.
Proof. vm_refl. Qed.
Lemma D_86314 : decode_any W_86314 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_86318 : bv 32 := 0x8a050493.
Lemma F_86318 : fetch_word Asan.M.loaded_segments (0x86368 : word) = Some W_86318.
Proof. vm_refl. Qed.
Lemma D_86318 : decode_any W_86318 = Some (OpImm ALU_ADD 9 10 2208, 4%Z).
Proof. vm_refl. Qed.

Definition W_8631c : bv 32 := 0x0085851b.
Lemma F_8631c : fetch_word Asan.M.loaded_segments (0x8636c : word) = Some W_8631c.
Proof. vm_refl. Qed.
Lemma D_8631c : decode_any W_8631c = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86320 : bv 32 := 0x00a48533.
Lemma F_86320 : fetch_word Asan.M.loaded_segments (0x86370 : word) = Some W_86320.
Proof. vm_refl. Qed.
Lemma D_86320 : decode_any W_86320 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_86324 : bv 32 := 0x02800613.
Lemma F_86324 : fetch_word Asan.M.loaded_segments (0x86374 : word) = Some W_86324.
Proof. vm_refl. Qed.
Lemma D_86324 : decode_any W_86324 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86328 : bv 32 := 0x00000593.
Lemma F_86328 : fetch_word Asan.M.loaded_segments (0x86378 : word) = Some W_86328.
Proof. vm_refl. Qed.
Lemma D_86328 : decode_any W_86328 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8632c : bv 32 := 0x269050ef.
Lemma F_8632c : fetch_word Asan.M.loaded_segments (0x8637c : word) = Some W_8632c.
Proof. vm_refl. Qed.
Lemma D_8632c : decode_any W_8632c = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_86330 : bv 32 := 0x00048023.
Lemma F_86330 : fetch_word Asan.M.loaded_segments (0x86380 : word) = Some W_86330.
Proof. vm_refl. Qed.
Lemma D_86330 : decode_any W_86330 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86334 : bv 32 := 0x00848513.
Lemma F_86334 : fetch_word Asan.M.loaded_segments (0x86384 : word) = Some W_86334.
Proof. vm_refl. Qed.
Lemma D_86334 : decode_any W_86334 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86338 : bv 32 := 0x00040637.
Lemma F_86338 : fetch_word Asan.M.loaded_segments (0x86388 : word) = Some W_86338.
Proof. vm_refl. Qed.
Lemma D_86338 : decode_any W_86338 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8633c : bv 32 := 0x000409b7.
Lemma F_8633c : fetch_word Asan.M.loaded_segments (0x8638c : word) = Some W_8633c.
Proof. vm_refl. Qed.
Lemma D_8633c : decode_any W_8633c = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86340 : bv 32 := 0x00000593.
Lemma F_86340 : fetch_word Asan.M.loaded_segments (0x86390 : word) = Some W_86340.
Proof. vm_refl. Qed.
Lemma D_86340 : decode_any W_86340 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86344 : bv 32 := 0x251050ef.
Lemma F_86344 : fetch_word Asan.M.loaded_segments (0x86394 : word) = Some W_86344.
Proof. vm_refl. Qed.
Lemma D_86344 : decode_any W_86344 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86348 : bv 32 := 0x0409851b.
Lemma F_86348 : fetch_word Asan.M.loaded_segments (0x86398 : word) = Some W_86348.
Proof. vm_refl. Qed.
Lemma D_86348 : decode_any W_86348 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8634c : bv 32 := 0x00a48533.
Lemma F_8634c : fetch_word Asan.M.loaded_segments (0x8639c : word) = Some W_8634c.
Proof. vm_refl. Qed.
Lemma D_8634c : decode_any W_8634c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_86350 : bv 32 := 0x01b00613.
Lemma F_86350 : fetch_word Asan.M.loaded_segments (0x863a0 : word) = Some W_86350.
Proof. vm_refl. Qed.
Lemma D_86350 : decode_any W_86350 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86354 : bv 32 := 0x00761613.
Lemma F_86354 : fetch_word Asan.M.loaded_segments (0x863a4 : word) = Some W_86354.
Proof. vm_refl. Qed.
Lemma D_86354 : decode_any W_86354 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86358 : bv 32 := 0x00000593.
Lemma F_86358 : fetch_word Asan.M.loaded_segments (0x863a8 : word) = Some W_86358.
Proof. vm_refl. Qed.
Lemma D_86358 : decode_any W_86358 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8635c : bv 32 := 0x239050ef.
Lemma F_8635c : fetch_word Asan.M.loaded_segments (0x863ac : word) = Some W_8635c.
Proof. vm_refl. Qed.
Lemma D_8635c : decode_any W_8635c = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_86360 : bv 32 := 0x00041937.
Lemma F_86360 : fetch_word Asan.M.loaded_segments (0x863b0 : word) = Some W_86360.
Proof. vm_refl. Qed.
Lemma D_86360 : decode_any W_86360 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_86364 : bv 32 := 0xdc09051b.
Lemma F_86364 : fetch_word Asan.M.loaded_segments (0x863b4 : word) = Some W_86364.
Proof. vm_refl. Qed.
Lemma D_86364 : decode_any W_86364 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_86368 : bv 32 := 0x00a48533.
Lemma F_86368 : fetch_word Asan.M.loaded_segments (0x863b8 : word) = Some W_86368.
Proof. vm_refl. Qed.
Lemma D_86368 : decode_any W_86368 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8636c : bv 32 := 0x2489861b.
Lemma F_8636c : fetch_word Asan.M.loaded_segments (0x863bc : word) = Some W_8636c.
Proof. vm_refl. Qed.
Lemma D_8636c : decode_any W_8636c = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_86370 : bv 32 := 0x00000593.
Lemma F_86370 : fetch_word Asan.M.loaded_segments (0x863c0 : word) = Some W_86370.
Proof. vm_refl. Qed.
Lemma D_86370 : decode_any W_86370 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86374 : bv 32 := 0x221050ef.
Lemma F_86374 : fetch_word Asan.M.loaded_segments (0x863c4 : word) = Some W_86374.
Proof. vm_refl. Qed.
Lemma D_86374 : decode_any W_86374 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_86378 : bv 32 := 0x000b3517.
Lemma F_86378 : fetch_word Asan.M.loaded_segments (0x863c8 : word) = Some W_86378.
Proof. vm_refl. Qed.
Lemma D_86378 : decode_any W_86378 = Some (Auipc 10 179, 4%Z).
Proof. vm_refl. Qed.

Definition W_8637c : bv 32 := 0xdd053983.
Lemma F_8637c : fetch_word Asan.M.loaded_segments (0x863cc : word) = Some W_8637c.
Proof. vm_refl. Qed.
Lemma D_8637c : decode_any W_8637c = Some (Load SZ8 true 19 10 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_86380 : bv 32 := 0x0009b503.
Lemma F_86380 : fetch_word Asan.M.loaded_segments (0x863d0 : word) = Some W_86380.
Proof. vm_refl. Qed.
Lemma D_86380 : decode_any W_86380 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86384 : bv 32 := 0x00051663.
Lemma F_86384 : fetch_word Asan.M.loaded_segments (0x863d4 : word) = Some W_86384.
Proof. vm_refl. Qed.
Lemma D_86384 : decode_any W_86384 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86390 : bv 32 := 0x012485b3.
Lemma F_86390 : fetch_word Asan.M.loaded_segments (0x863e0 : word) = Some W_86390.
Proof. vm_refl. Qed.
Lemma D_86390 : decode_any W_86390 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86394 : bv 32 := 0xdd09061b.
Lemma F_86394 : fetch_word Asan.M.loaded_segments (0x863e4 : word) = Some W_86394.
Proof. vm_refl. Qed.
Lemma D_86394 : decode_any W_86394 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_86398 : bv 32 := 0x00c48633.
Lemma F_86398 : fetch_word Asan.M.loaded_segments (0x863e8 : word) = Some W_86398.
Proof. vm_refl. Qed.
Lemma D_86398 : decode_any W_86398 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8639c : bv 32 := 0x00100693.
Lemma F_8639c : fetch_word Asan.M.loaded_segments (0x863ec : word) = Some W_8639c.
Proof. vm_refl. Qed.
Lemma D_8639c : decode_any W_8639c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_863a0 : bv 32 := 0xdca5b023.
Lemma F_863a0 : fetch_word Asan.M.loaded_segments (0x863f0 : word) = Some W_863a0.
Proof. vm_refl. Qed.
Lemma D_863a0 : decode_any W_863a0 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_863a4 : bv 32 := 0xdcc5b423.
Lemma F_863a4 : fetch_word Asan.M.loaded_segments (0x863f4 : word) = Some W_863a4.
Proof. vm_refl. Qed.
Lemma D_863a4 : decode_any W_863a4 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_863a8 : bv 32 := 0x0310000f.
Lemma F_863a8 : fetch_word Asan.M.loaded_segments (0x863f8 : word) = Some W_863a8.
Proof. vm_refl. Qed.
Lemma D_863a8 : decode_any W_863a8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_863ac : bv 32 := 0x00d40023.
Lemma F_863ac : fetch_word Asan.M.loaded_segments (0x863fc : word) = Some W_863ac.
Proof. vm_refl. Qed.
Lemma D_863ac : decode_any W_863ac = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_863b0 : bv 32 := 0x0310000f.
Lemma F_863b0 : fetch_word Asan.M.loaded_segments (0x86400 : word) = Some W_863b0.
Proof. vm_refl. Qed.
Lemma D_863b0 : decode_any W_863b0 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_863b4 : bv 32 := 0x000400a3.
Lemma F_863b4 : fetch_word Asan.M.loaded_segments (0x86404 : word) = Some W_863b4.
Proof. vm_refl. Qed.
Lemma D_863b4 : decode_any W_863b4 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_863b8 : bv 32 := 0x000bc517.
Lemma F_863b8 : fetch_word Asan.M.loaded_segments (0x86408 : word) = Some W_863b8.
Proof. vm_refl. Qed.
Lemma D_863b8 : decode_any W_863b8 = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_863bc : bv 32 := 0x7f850513.
Lemma F_863bc : fetch_word Asan.M.loaded_segments (0x8640c : word) = Some W_863bc.
Proof. vm_refl. Qed.
Lemma D_863bc : decode_any W_863bc = Some (OpImm ALU_ADD 10 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_863c0 : bv 32 := 0x02813083.
Lemma F_863c0 : fetch_word Asan.M.loaded_segments (0x86410 : word) = Some W_863c0.
Proof. vm_refl. Qed.
Lemma D_863c0 : decode_any W_863c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_863c4 : bv 32 := 0x02013403.
Lemma F_863c4 : fetch_word Asan.M.loaded_segments (0x86414 : word) = Some W_863c4.
Proof. vm_refl. Qed.
Lemma D_863c4 : decode_any W_863c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_863c8 : bv 32 := 0x01813483.
Lemma F_863c8 : fetch_word Asan.M.loaded_segments (0x86418 : word) = Some W_863c8.
Proof. vm_refl. Qed.
Lemma D_863c8 : decode_any W_863c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_863cc : bv 32 := 0x01013903.
Lemma F_863cc : fetch_word Asan.M.loaded_segments (0x8641c : word) = Some W_863cc.
Proof. vm_refl. Qed.
Lemma D_863cc : decode_any W_863cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_863d0 : bv 32 := 0x00813983.
Lemma F_863d0 : fetch_word Asan.M.loaded_segments (0x86420 : word) = Some W_863d0.
Proof. vm_refl. Qed.
Lemma D_863d0 : decode_any W_863d0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_863d4 : bv 32 := 0x03010113.
Lemma F_863d4 : fetch_word Asan.M.loaded_segments (0x86424 : word) = Some W_863d4.
Proof. vm_refl. Qed.
Lemma D_863d4 : decode_any W_863d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_863d8 : bv 32 := 0x00008067.
Lemma F_863d8 : fetch_word Asan.M.loaded_segments (0x86428 : word) = Some W_863d8.
Proof. vm_refl. Qed.
Lemma D_863d8 : decode_any W_863d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
