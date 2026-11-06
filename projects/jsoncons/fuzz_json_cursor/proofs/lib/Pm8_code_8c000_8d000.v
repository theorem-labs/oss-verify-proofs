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

Definition W_8caf0 : bv 32 := 0xfd010113.
Lemma F_8caf0 : fetch_word Asan.M.loaded_segments (0x8cb40 : word) = Some W_8caf0.
Proof. vm_refl. Qed.
Lemma D_8caf0 : decode_any W_8caf0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8caf4 : bv 32 := 0x02113423.
Lemma F_8caf4 : fetch_word Asan.M.loaded_segments (0x8cb44 : word) = Some W_8caf4.
Proof. vm_refl. Qed.
Lemma D_8caf4 : decode_any W_8caf4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8caf8 : bv 32 := 0x02813023.
Lemma F_8caf8 : fetch_word Asan.M.loaded_segments (0x8cb48 : word) = Some W_8caf8.
Proof. vm_refl. Qed.
Lemma D_8caf8 : decode_any W_8caf8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cafc : bv 32 := 0x00913c23.
Lemma F_8cafc : fetch_word Asan.M.loaded_segments (0x8cb4c : word) = Some W_8cafc.
Proof. vm_refl. Qed.
Lemma D_8cafc : decode_any W_8cafc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb00 : bv 32 := 0x01213823.
Lemma F_8cb00 : fetch_word Asan.M.loaded_segments (0x8cb50 : word) = Some W_8cb00.
Proof. vm_refl. Qed.
Lemma D_8cb00 : decode_any W_8cb00 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb04 : bv 32 := 0x01313423.
Lemma F_8cb04 : fetch_word Asan.M.loaded_segments (0x8cb54 : word) = Some W_8cb04.
Proof. vm_refl. Qed.
Lemma D_8cb04 : decode_any W_8cb04 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb08 : bv 32 := 0x00160517.
Lemma F_8cb08 : fetch_word Asan.M.loaded_segments (0x8cb58 : word) = Some W_8cb08.
Proof. vm_refl. Qed.
Lemma D_8cb08 : decode_any W_8cb08 = Some (Auipc 10 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb0c : bv 32 := 0x8f050413.
Lemma F_8cb0c : fetch_word Asan.M.loaded_segments (0x8cb5c : word) = Some W_8cb0c.
Proof. vm_refl. Qed.
Lemma D_8cb0c : decode_any W_8cb0c = Some (OpImm ALU_ADD 8 10 2288, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb10 : bv 32 := 0x00040503.
Lemma F_8cb10 : fetch_word Asan.M.loaded_segments (0x8cb60 : word) = Some W_8cb10.
Proof. vm_refl. Qed.
Lemma D_8cb10 : decode_any W_8cb10 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb14 : bv 32 := 0x0230000f.
Lemma F_8cb14 : fetch_word Asan.M.loaded_segments (0x8cb64 : word) = Some W_8cb14.
Proof. vm_refl. Qed.
Lemma D_8cb14 : decode_any W_8cb14 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb18 : bv 32 := 0x0e051e63.
Lemma F_8cb18 : fetch_word Asan.M.loaded_segments (0x8cb68 : word) = Some W_8cb18.
Proof. vm_refl. Qed.
Lemma D_8cb18 : decode_any W_8cb18 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb1c : bv 32 := 0x00140513.
Lemma F_8cb1c : fetch_word Asan.M.loaded_segments (0x8cb6c : word) = Some W_8cb1c.
Proof. vm_refl. Qed.
Lemma D_8cb1c : decode_any W_8cb1c = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb20 : bv 32 := 0x0ff00593.
Lemma F_8cb20 : fetch_word Asan.M.loaded_segments (0x8cb70 : word) = Some W_8cb20.
Proof. vm_refl. Qed.
Lemma D_8cb20 : decode_any W_8cb20 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb24 : bv 32 := 0x00100613.
Lemma F_8cb24 : fetch_word Asan.M.loaded_segments (0x8cb74 : word) = Some W_8cb24.
Proof. vm_refl. Qed.
Lemma D_8cb24 : decode_any W_8cb24 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb28 : bv 32 := 0xffc57693.
Lemma F_8cb28 : fetch_word Asan.M.loaded_segments (0x8cb78 : word) = Some W_8cb28.
Proof. vm_refl. Qed.
Lemma D_8cb28 : decode_any W_8cb28 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb2c : bv 32 := 0x00357713.
Lemma F_8cb2c : fetch_word Asan.M.loaded_segments (0x8cb7c : word) = Some W_8cb2c.
Proof. vm_refl. Qed.
Lemma D_8cb2c : decode_any W_8cb2c = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb30 : bv 32 := 0x00371713.
Lemma F_8cb30 : fetch_word Asan.M.loaded_segments (0x8cb80 : word) = Some W_8cb30.
Proof. vm_refl. Qed.
Lemma D_8cb30 : decode_any W_8cb30 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb34 : bv 32 := 0x00e595bb.
Lemma F_8cb34 : fetch_word Asan.M.loaded_segments (0x8cb84 : word) = Some W_8cb34.
Proof. vm_refl. Qed.
Lemma D_8cb34 : decode_any W_8cb34 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb38 : bv 32 := 0x00e6163b.
Lemma F_8cb38 : fetch_word Asan.M.loaded_segments (0x8cb88 : word) = Some W_8cb38.
Proof. vm_refl. Qed.
Lemma D_8cb38 : decode_any W_8cb38 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb3c : bv 32 := 0x1406a7af.
Lemma F_8cb3c : fetch_word Asan.M.loaded_segments (0x8cb8c : word) = Some W_8cb3c.
Proof. vm_refl. Qed.
Lemma D_8cb3c : decode_any W_8cb3c = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb40 : bv 32 := 0x00060813.
Lemma F_8cb40 : fetch_word Asan.M.loaded_segments (0x8cb90 : word) = Some W_8cb40.
Proof. vm_refl. Qed.
Lemma D_8cb40 : decode_any W_8cb40 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb44 : bv 32 := 0x0107c833.
Lemma F_8cb44 : fetch_word Asan.M.loaded_segments (0x8cb94 : word) = Some W_8cb44.
Proof. vm_refl. Qed.
Lemma D_8cb44 : decode_any W_8cb44 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb48 : bv 32 := 0x00b87833.
Lemma F_8cb48 : fetch_word Asan.M.loaded_segments (0x8cb98 : word) = Some W_8cb48.
Proof. vm_refl. Qed.
Lemma D_8cb48 : decode_any W_8cb48 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb4c : bv 32 := 0x0107c833.
Lemma F_8cb4c : fetch_word Asan.M.loaded_segments (0x8cb9c : word) = Some W_8cb4c.
Proof. vm_refl. Qed.
Lemma D_8cb4c : decode_any W_8cb4c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb50 : bv 32 := 0x1906a82f.
Lemma F_8cb50 : fetch_word Asan.M.loaded_segments (0x8cba0 : word) = Some W_8cb50.
Proof. vm_refl. Qed.
Lemma D_8cb50 : decode_any W_8cb50 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb54 : bv 32 := 0xfe0814e3.
Lemma F_8cb54 : fetch_word Asan.M.loaded_segments (0x8cba4 : word) = Some W_8cb54.
Proof. vm_refl. Qed.
Lemma D_8cb54 : decode_any W_8cb54 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb58 : bv 32 := 0x00e7d5bb.
Lemma F_8cb58 : fetch_word Asan.M.loaded_segments (0x8cba8 : word) = Some W_8cb58.
Proof. vm_refl. Qed.
Lemma D_8cb58 : decode_any W_8cb58 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb5c : bv 32 := 0x0ff5f593.
Lemma F_8cb5c : fetch_word Asan.M.loaded_segments (0x8cbac : word) = Some W_8cb5c.
Proof. vm_refl. Qed.
Lemma D_8cb5c : decode_any W_8cb5c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb60 : bv 32 := 0x0c059c63.
Lemma F_8cb60 : fetch_word Asan.M.loaded_segments (0x8cbb0 : word) = Some W_8cb60.
Proof. vm_refl. Qed.
Lemma D_8cb60 : decode_any W_8cb60 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb64 : bv 32 := 0x00040503.
Lemma F_8cb64 : fetch_word Asan.M.loaded_segments (0x8cbb4 : word) = Some W_8cb64.
Proof. vm_refl. Qed.
Lemma D_8cb64 : decode_any W_8cb64 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb68 : bv 32 := 0x0a051263.
Lemma F_8cb68 : fetch_word Asan.M.loaded_segments (0x8cbb8 : word) = Some W_8cb68.
Proof. vm_refl. Qed.
Lemma D_8cb68 : decode_any W_8cb68 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb6c : bv 32 := 0x000d1517.
Lemma F_8cb6c : fetch_word Asan.M.loaded_segments (0x8cbbc : word) = Some W_8cb6c.
Proof. vm_refl. Qed.
Lemma D_8cb6c : decode_any W_8cb6c = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb70 : bv 32 := 0x000815b7.
Lemma F_8cb70 : fetch_word Asan.M.loaded_segments (0x8cbc0 : word) = Some W_8cb70.
Proof. vm_refl. Qed.
Lemma D_8cb70 : decode_any W_8cb70 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb74 : bv 32 := 0x00450493.
Lemma F_8cb74 : fetch_word Asan.M.loaded_segments (0x8cbc4 : word) = Some W_8cb74.
Proof. vm_refl. Qed.
Lemma D_8cb74 : decode_any W_8cb74 = Some (OpImm ALU_ADD 9 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb78 : bv 32 := 0x0085851b.
Lemma F_8cb78 : fetch_word Asan.M.loaded_segments (0x8cbc8 : word) = Some W_8cb78.
Proof. vm_refl. Qed.
Lemma D_8cb78 : decode_any W_8cb78 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb7c : bv 32 := 0x00a48533.
Lemma F_8cb7c : fetch_word Asan.M.loaded_segments (0x8cbcc : word) = Some W_8cb7c.
Proof. vm_refl. Qed.
Lemma D_8cb7c : decode_any W_8cb7c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb80 : bv 32 := 0x02800613.
Lemma F_8cb80 : fetch_word Asan.M.loaded_segments (0x8cbd0 : word) = Some W_8cb80.
Proof. vm_refl. Qed.
Lemma D_8cb80 : decode_any W_8cb80 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb84 : bv 32 := 0x00000593.
Lemma F_8cb84 : fetch_word Asan.M.loaded_segments (0x8cbd4 : word) = Some W_8cb84.
Proof. vm_refl. Qed.
Lemma D_8cb84 : decode_any W_8cb84 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb88 : bv 32 := 0x269050ef.
Lemma F_8cb88 : fetch_word Asan.M.loaded_segments (0x8cbd8 : word) = Some W_8cb88.
Proof. vm_refl. Qed.
Lemma D_8cb88 : decode_any W_8cb88 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb8c : bv 32 := 0x00048023.
Lemma F_8cb8c : fetch_word Asan.M.loaded_segments (0x8cbdc : word) = Some W_8cb8c.
Proof. vm_refl. Qed.
Lemma D_8cb8c : decode_any W_8cb8c = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb90 : bv 32 := 0x00848513.
Lemma F_8cb90 : fetch_word Asan.M.loaded_segments (0x8cbe0 : word) = Some W_8cb90.
Proof. vm_refl. Qed.
Lemma D_8cb90 : decode_any W_8cb90 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb94 : bv 32 := 0x00040637.
Lemma F_8cb94 : fetch_word Asan.M.loaded_segments (0x8cbe4 : word) = Some W_8cb94.
Proof. vm_refl. Qed.
Lemma D_8cb94 : decode_any W_8cb94 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb98 : bv 32 := 0x000409b7.
Lemma F_8cb98 : fetch_word Asan.M.loaded_segments (0x8cbe8 : word) = Some W_8cb98.
Proof. vm_refl. Qed.
Lemma D_8cb98 : decode_any W_8cb98 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb9c : bv 32 := 0x00000593.
Lemma F_8cb9c : fetch_word Asan.M.loaded_segments (0x8cbec : word) = Some W_8cb9c.
Proof. vm_refl. Qed.
Lemma D_8cb9c : decode_any W_8cb9c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cba0 : bv 32 := 0x251050ef.
Lemma F_8cba0 : fetch_word Asan.M.loaded_segments (0x8cbf0 : word) = Some W_8cba0.
Proof. vm_refl. Qed.
Lemma D_8cba0 : decode_any W_8cba0 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cba4 : bv 32 := 0x0409851b.
Lemma F_8cba4 : fetch_word Asan.M.loaded_segments (0x8cbf4 : word) = Some W_8cba4.
Proof. vm_refl. Qed.
Lemma D_8cba4 : decode_any W_8cba4 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cba8 : bv 32 := 0x00a48533.
Lemma F_8cba8 : fetch_word Asan.M.loaded_segments (0x8cbf8 : word) = Some W_8cba8.
Proof. vm_refl. Qed.
Lemma D_8cba8 : decode_any W_8cba8 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbac : bv 32 := 0x01b00613.
Lemma F_8cbac : fetch_word Asan.M.loaded_segments (0x8cbfc : word) = Some W_8cbac.
Proof. vm_refl. Qed.
Lemma D_8cbac : decode_any W_8cbac = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbb0 : bv 32 := 0x00761613.
Lemma F_8cbb0 : fetch_word Asan.M.loaded_segments (0x8cc00 : word) = Some W_8cbb0.
Proof. vm_refl. Qed.
Lemma D_8cbb0 : decode_any W_8cbb0 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbb4 : bv 32 := 0x00000593.
Lemma F_8cbb4 : fetch_word Asan.M.loaded_segments (0x8cc04 : word) = Some W_8cbb4.
Proof. vm_refl. Qed.
Lemma D_8cbb4 : decode_any W_8cbb4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbb8 : bv 32 := 0x239050ef.
Lemma F_8cbb8 : fetch_word Asan.M.loaded_segments (0x8cc08 : word) = Some W_8cbb8.
Proof. vm_refl. Qed.
Lemma D_8cbb8 : decode_any W_8cbb8 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbbc : bv 32 := 0x00041937.
Lemma F_8cbbc : fetch_word Asan.M.loaded_segments (0x8cc0c : word) = Some W_8cbbc.
Proof. vm_refl. Qed.
Lemma D_8cbbc : decode_any W_8cbbc = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbc0 : bv 32 := 0xdc09051b.
Lemma F_8cbc0 : fetch_word Asan.M.loaded_segments (0x8cc10 : word) = Some W_8cbc0.
Proof. vm_refl. Qed.
Lemma D_8cbc0 : decode_any W_8cbc0 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbc4 : bv 32 := 0x00a48533.
Lemma F_8cbc4 : fetch_word Asan.M.loaded_segments (0x8cc14 : word) = Some W_8cbc4.
Proof. vm_refl. Qed.
Lemma D_8cbc4 : decode_any W_8cbc4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbc8 : bv 32 := 0x2489861b.
Lemma F_8cbc8 : fetch_word Asan.M.loaded_segments (0x8cc18 : word) = Some W_8cbc8.
Proof. vm_refl. Qed.
Lemma D_8cbc8 : decode_any W_8cbc8 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbcc : bv 32 := 0x00000593.
Lemma F_8cbcc : fetch_word Asan.M.loaded_segments (0x8cc1c : word) = Some W_8cbcc.
Proof. vm_refl. Qed.
Lemma D_8cbcc : decode_any W_8cbcc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbd0 : bv 32 := 0x221050ef.
Lemma F_8cbd0 : fetch_word Asan.M.loaded_segments (0x8cc20 : word) = Some W_8cbd0.
Proof. vm_refl. Qed.
Lemma D_8cbd0 : decode_any W_8cbd0 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbd4 : bv 32 := 0x000c6517.
Lemma F_8cbd4 : fetch_word Asan.M.loaded_segments (0x8cc24 : word) = Some W_8cbd4.
Proof. vm_refl. Qed.
Lemma D_8cbd4 : decode_any W_8cbd4 = Some (Auipc 10 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbd8 : bv 32 := 0x4f453983.
Lemma F_8cbd8 : fetch_word Asan.M.loaded_segments (0x8cc28 : word) = Some W_8cbd8.
Proof. vm_refl. Qed.
Lemma D_8cbd8 : decode_any W_8cbd8 = Some (Load SZ8 true 19 10 1268, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbdc : bv 32 := 0x0009b503.
Lemma F_8cbdc : fetch_word Asan.M.loaded_segments (0x8cc2c : word) = Some W_8cbdc.
Proof. vm_refl. Qed.
Lemma D_8cbdc : decode_any W_8cbdc = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbe0 : bv 32 := 0x00051663.
Lemma F_8cbe0 : fetch_word Asan.M.loaded_segments (0x8cc30 : word) = Some W_8cbe0.
Proof. vm_refl. Qed.
Lemma D_8cbe0 : decode_any W_8cbe0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbec : bv 32 := 0x012485b3.
Lemma F_8cbec : fetch_word Asan.M.loaded_segments (0x8cc3c : word) = Some W_8cbec.
Proof. vm_refl. Qed.
Lemma D_8cbec : decode_any W_8cbec = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbf0 : bv 32 := 0xdd09061b.
Lemma F_8cbf0 : fetch_word Asan.M.loaded_segments (0x8cc40 : word) = Some W_8cbf0.
Proof. vm_refl. Qed.
Lemma D_8cbf0 : decode_any W_8cbf0 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbf4 : bv 32 := 0x00c48633.
Lemma F_8cbf4 : fetch_word Asan.M.loaded_segments (0x8cc44 : word) = Some W_8cbf4.
Proof. vm_refl. Qed.
Lemma D_8cbf4 : decode_any W_8cbf4 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbf8 : bv 32 := 0x00100693.
Lemma F_8cbf8 : fetch_word Asan.M.loaded_segments (0x8cc48 : word) = Some W_8cbf8.
Proof. vm_refl. Qed.
Lemma D_8cbf8 : decode_any W_8cbf8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cbfc : bv 32 := 0xdca5b023.
Lemma F_8cbfc : fetch_word Asan.M.loaded_segments (0x8cc4c : word) = Some W_8cbfc.
Proof. vm_refl. Qed.
Lemma D_8cbfc : decode_any W_8cbfc = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc00 : bv 32 := 0xdcc5b423.
Lemma F_8cc00 : fetch_word Asan.M.loaded_segments (0x8cc50 : word) = Some W_8cc00.
Proof. vm_refl. Qed.
Lemma D_8cc00 : decode_any W_8cc00 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc04 : bv 32 := 0x0310000f.
Lemma F_8cc04 : fetch_word Asan.M.loaded_segments (0x8cc54 : word) = Some W_8cc04.
Proof. vm_refl. Qed.
Lemma D_8cc04 : decode_any W_8cc04 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc08 : bv 32 := 0x00d40023.
Lemma F_8cc08 : fetch_word Asan.M.loaded_segments (0x8cc58 : word) = Some W_8cc08.
Proof. vm_refl. Qed.
Lemma D_8cc08 : decode_any W_8cc08 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc0c : bv 32 := 0x0310000f.
Lemma F_8cc0c : fetch_word Asan.M.loaded_segments (0x8cc5c : word) = Some W_8cc0c.
Proof. vm_refl. Qed.
Lemma D_8cc0c : decode_any W_8cc0c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc10 : bv 32 := 0x000400a3.
Lemma F_8cc10 : fetch_word Asan.M.loaded_segments (0x8cc60 : word) = Some W_8cc10.
Proof. vm_refl. Qed.
Lemma D_8cc10 : decode_any W_8cc10 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc14 : bv 32 := 0x000d1517.
Lemma F_8cc14 : fetch_word Asan.M.loaded_segments (0x8cc64 : word) = Some W_8cc14.
Proof. vm_refl. Qed.
Lemma D_8cc14 : decode_any W_8cc14 = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc18 : bv 32 := 0xf5c50513.
Lemma F_8cc18 : fetch_word Asan.M.loaded_segments (0x8cc68 : word) = Some W_8cc18.
Proof. vm_refl. Qed.
Lemma D_8cc18 : decode_any W_8cc18 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc1c : bv 32 := 0x02813083.
Lemma F_8cc1c : fetch_word Asan.M.loaded_segments (0x8cc6c : word) = Some W_8cc1c.
Proof. vm_refl. Qed.
Lemma D_8cc1c : decode_any W_8cc1c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc20 : bv 32 := 0x02013403.
Lemma F_8cc20 : fetch_word Asan.M.loaded_segments (0x8cc70 : word) = Some W_8cc20.
Proof. vm_refl. Qed.
Lemma D_8cc20 : decode_any W_8cc20 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc24 : bv 32 := 0x01813483.
Lemma F_8cc24 : fetch_word Asan.M.loaded_segments (0x8cc74 : word) = Some W_8cc24.
Proof. vm_refl. Qed.
Lemma D_8cc24 : decode_any W_8cc24 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc28 : bv 32 := 0x01013903.
Lemma F_8cc28 : fetch_word Asan.M.loaded_segments (0x8cc78 : word) = Some W_8cc28.
Proof. vm_refl. Qed.
Lemma D_8cc28 : decode_any W_8cc28 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc2c : bv 32 := 0x00813983.
Lemma F_8cc2c : fetch_word Asan.M.loaded_segments (0x8cc7c : word) = Some W_8cc2c.
Proof. vm_refl. Qed.
Lemma D_8cc2c : decode_any W_8cc2c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc30 : bv 32 := 0x03010113.
Lemma F_8cc30 : fetch_word Asan.M.loaded_segments (0x8cc80 : word) = Some W_8cc30.
Proof. vm_refl. Qed.
Lemma D_8cc30 : decode_any W_8cc30 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cc34 : bv 32 := 0x00008067.
Lemma F_8cc34 : fetch_word Asan.M.loaded_segments (0x8cc84 : word) = Some W_8cc34.
Proof. vm_refl. Qed.
Lemma D_8cc34 : decode_any W_8cc34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

