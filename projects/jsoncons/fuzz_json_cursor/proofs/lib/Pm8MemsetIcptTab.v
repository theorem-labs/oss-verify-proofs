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

Definition Wx_7ee18 : bv 32 := 0x2590006f.
Lemma Fx_7ee18 : fetch_word Asan.M.loaded_segments (0x7ee68 : word) = Some Wx_7ee18.
Proof. vm_refl. Qed.
Lemma Dx_7ee18 : decode_any Wx_7ee18 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f870 : bv 32 := 0x81010113.
Lemma Fx_7f870 : fetch_word Asan.M.loaded_segments (0x7f8c0 : word) = Some Wx_7f870.
Proof. vm_refl. Qed.
Lemma Dx_7f870 : decode_any Wx_7f870 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f874 : bv 32 := 0x7e113423.
Lemma Fx_7f874 : fetch_word Asan.M.loaded_segments (0x7f8c4 : word) = Some Wx_7f874.
Proof. vm_refl. Qed.
Lemma Dx_7f874 : decode_any Wx_7f874 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f878 : bv 32 := 0x7e813023.
Lemma Fx_7f878 : fetch_word Asan.M.loaded_segments (0x7f8c8 : word) = Some Wx_7f878.
Proof. vm_refl. Qed.
Lemma Dx_7f878 : decode_any Wx_7f878 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f87c : bv 32 := 0x7c913c23.
Lemma Fx_7f87c : fetch_word Asan.M.loaded_segments (0x7f8cc : word) = Some Wx_7f87c.
Proof. vm_refl. Qed.
Lemma Dx_7f87c : decode_any Wx_7f87c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f880 : bv 32 := 0x7d213823.
Lemma Fx_7f880 : fetch_word Asan.M.loaded_segments (0x7f8d0 : word) = Some Wx_7f880.
Proof. vm_refl. Qed.
Lemma Dx_7f880 : decode_any Wx_7f880 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f884 : bv 32 := 0x7d313423.
Lemma Fx_7f884 : fetch_word Asan.M.loaded_segments (0x7f8d4 : word) = Some Wx_7f884.
Proof. vm_refl. Qed.
Lemma Dx_7f884 : decode_any Wx_7f884 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f888 : bv 32 := 0x7d413023.
Lemma Fx_7f888 : fetch_word Asan.M.loaded_segments (0x7f8d8 : word) = Some Wx_7f888.
Proof. vm_refl. Qed.
Lemma Dx_7f888 : decode_any Wx_7f888 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f88c : bv 32 := 0x7b513c23.
Lemma Fx_7f88c : fetch_word Asan.M.loaded_segments (0x7f8dc : word) = Some Wx_7f88c.
Proof. vm_refl. Qed.
Lemma Dx_7f88c : decode_any Wx_7f88c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f890 : bv 32 := 0x7b613823.
Lemma Fx_7f890 : fetch_word Asan.M.loaded_segments (0x7f8e0 : word) = Some Wx_7f890.
Proof. vm_refl. Qed.
Lemma Dx_7f890 : decode_any Wx_7f890 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f894 : bv 32 := 0x7f010413.
Lemma Fx_7f894 : fetch_word Asan.M.loaded_segments (0x7f8e4 : word) = Some Wx_7f894.
Proof. vm_refl. Qed.
Lemma Dx_7f894 : decode_any Wx_7f894 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f898 : bv 32 := 0xf9010113.
Lemma Fx_7f898 : fetch_word Asan.M.loaded_segments (0x7f8e8 : word) = Some Wx_7f898.
Proof. vm_refl. Qed.
Lemma Dx_7f898 : decode_any Wx_7f898 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f89c : bv 32 := 0x000d4697.
Lemma Fx_7f89c : fetch_word Asan.M.loaded_segments (0x7f8ec : word) = Some Wx_7f89c.
Proof. vm_refl. Qed.
Lemma Dx_7f89c : decode_any Wx_7f89c = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8a0 : bv 32 := 0x3b46b683.
Lemma Fx_7f8a0 : fetch_word Asan.M.loaded_segments (0x7f8f0 : word) = Some Wx_7f8a0.
Proof. vm_refl. Qed.
Lemma Dx_7f8a0 : decode_any Wx_7f8a0 = Some (Load SZ8 true 13 13 948, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8a4 : bv 32 := 0x0006c683.
Lemma Fx_7f8a4 : fetch_word Asan.M.loaded_segments (0x7f8f4 : word) = Some Wx_7f8a4.
Proof. vm_refl. Qed.
Lemma Dx_7f8a4 : decode_any Wx_7f8a4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8a8 : bv 32 := 0x08068a63.
Lemma Fx_7f8a8 : fetch_word Asan.M.loaded_segments (0x7f8f8 : word) = Some Wx_7f8a8.
Proof. vm_refl. Qed.
Lemma Dx_7f8a8 : decode_any Wx_7f8a8 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8ac : bv 32 := 0xfff54693.
Lemma Fx_7f8ac : fetch_word Asan.M.loaded_segments (0x7f8fc : word) = Some Wx_7f8ac.
Proof. vm_refl. Qed.
Lemma Dx_7f8ac : decode_any Wx_7f8ac = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8b0 : bv 32 := 0x80040a93.
Lemma Fx_7f8b0 : fetch_word Asan.M.loaded_segments (0x7f900 : word) = Some Wx_7f8b0.
Proof. vm_refl. Qed.
Lemma Dx_7f8b0 : decode_any Wx_7f8b0 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8b4 : bv 32 := 0xfa8a8a93.
Lemma Fx_7f8b4 : fetch_word Asan.M.loaded_segments (0x7f904 : word) = Some Wx_7f8b4.
Proof. vm_refl. Qed.
Lemma Dx_7f8b4 : decode_any Wx_7f8b4 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8b8 : bv 32 := 0x0cc6ea63.
Lemma Fx_7f8b8 : fetch_word Asan.M.loaded_segments (0x7f908 : word) = Some Wx_7f8b8.
Proof. vm_refl. Qed.
Lemma Dx_7f8b8 : decode_any Wx_7f8b8 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8bc : bv 32 := 0xfbf60693.
Lemma Fx_7f8bc : fetch_word Asan.M.loaded_segments (0x7f90c : word) = Some Wx_7f8bc.
Proof. vm_refl. Qed.
Lemma Dx_7f8bc : decode_any Wx_7f8bc = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8c0 : bv 32 := 0xfbf00713.
Lemma Fx_7f8c0 : fetch_word Asan.M.loaded_segments (0x7f910 : word) = Some Wx_7f8c0.
Proof. vm_refl. Qed.
Lemma Dx_7f8c0 : decode_any Wx_7f8c0 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8c4 : bv 32 := 0x14d77863.
Lemma Fx_7f8c4 : fetch_word Asan.M.loaded_segments (0x7f914 : word) = Some Wx_7f8c4.
Proof. vm_refl. Qed.
Lemma Dx_7f8c4 : decode_any Wx_7f8c4 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8c8 : bv 32 := 0x000d4697.
Lemma Fx_7f8c8 : fetch_word Asan.M.loaded_segments (0x7f918 : word) = Some Wx_7f8c8.
Proof. vm_refl. Qed.
Lemma Dx_7f8c8 : decode_any Wx_7f8c8 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8cc : bv 32 := 0x8206b683.
Lemma Fx_7f8cc : fetch_word Asan.M.loaded_segments (0x7f91c : word) = Some Wx_7f8cc.
Proof. vm_refl. Qed.
Lemma Dx_7f8cc : decode_any Wx_7f8cc = Some (Load SZ8 true 13 13 2080, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8d0 : bv 32 := 0x00c507b3.
Lemma Fx_7f8d0 : fetch_word Asan.M.loaded_segments (0x7f920 : word) = Some Wx_7f8d0.
Proof. vm_refl. Qed.
Lemma Dx_7f8d0 : decode_any Wx_7f8d0 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8d4 : bv 32 := 0x0006b703.
Lemma Fx_7f8d4 : fetch_word Asan.M.loaded_segments (0x7f924 : word) = Some Wx_7f8d4.
Proof. vm_refl. Qed.
Lemma Dx_7f8d4 : decode_any Wx_7f8d4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8d8 : bv 32 := 0x00355693.
Lemma Fx_7f8d8 : fetch_word Asan.M.loaded_segments (0x7f928 : word) = Some Wx_7f8d8.
Proof. vm_refl. Qed.
Lemma Dx_7f8d8 : decode_any Wx_7f8d8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8dc : bv 32 := 0xfff78793.
Lemma Fx_7f8dc : fetch_word Asan.M.loaded_segments (0x7f92c : word) = Some Wx_7f8dc.
Proof. vm_refl. Qed.
Lemma Dx_7f8dc : decode_any Wx_7f8dc = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8e0 : bv 32 := 0x0037d813.
Lemma Fx_7f8e0 : fetch_word Asan.M.loaded_segments (0x7f930 : word) = Some Wx_7f8e0.
Proof. vm_refl. Qed.
Lemma Dx_7f8e0 : decode_any Wx_7f8e0 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8e4 : bv 32 := 0x00d706b3.
Lemma Fx_7f8e4 : fetch_word Asan.M.loaded_segments (0x7f934 : word) = Some Wx_7f8e4.
Proof. vm_refl. Qed.
Lemma Dx_7f8e4 : decode_any Wx_7f8e4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8e8 : bv 32 := 0x01070733.
Lemma Fx_7f8e8 : fetch_word Asan.M.loaded_segments (0x7f938 : word) = Some Wx_7f8e8.
Proof. vm_refl. Qed.
Lemma Dx_7f8e8 : decode_any Wx_7f8e8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8ec : bv 32 := 0xff86f813.
Lemma Fx_7f8ec : fetch_word Asan.M.loaded_segments (0x7f93c : word) = Some Wx_7f8ec.
Proof. vm_refl. Qed.
Lemma Dx_7f8ec : decode_any Wx_7f8ec = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8f0 : bv 32 := 0xff877893.
Lemma Fx_7f8f0 : fetch_word Asan.M.loaded_segments (0x7f940 : word) = Some Wx_7f8f0.
Proof. vm_refl. Qed.
Lemma Dx_7f8f0 : decode_any Wx_7f8f0 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8f4 : bv 32 := 0x00083803.
Lemma Fx_7f8f4 : fetch_word Asan.M.loaded_segments (0x7f944 : word) = Some Wx_7f8f4.
Proof. vm_refl. Qed.
Lemma Dx_7f8f4 : decode_any Wx_7f8f4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8f8 : bv 32 := 0x0008b883.
Lemma Fx_7f8f8 : fetch_word Asan.M.loaded_segments (0x7f948 : word) = Some Wx_7f8f8.
Proof. vm_refl. Qed.
Lemma Dx_7f8f8 : decode_any Wx_7f8f8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f8fc : bv 32 := 0x0108e833.
Lemma Fx_7f8fc : fetch_word Asan.M.loaded_segments (0x7f94c : word) = Some Wx_7f8fc.
Proof. vm_refl. Qed.
Lemma Dx_7f8fc : decode_any Wx_7f8fc = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f900 : bv 32 := 0x10081e63.
Lemma Fx_7f900 : fetch_word Asan.M.loaded_segments (0x7f950 : word) = Some Wx_7f900.
Proof. vm_refl. Qed.
Lemma Dx_7f900 : decode_any Wx_7f900 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f904 : bv 32 := 0x000d6697.
Lemma Fx_7f904 : fetch_word Asan.M.loaded_segments (0x7f954 : word) = Some Wx_7f904.
Proof. vm_refl. Qed.
Lemma Dx_7f904 : decode_any Wx_7f904 = Some (Auipc 13 214, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f908 : bv 32 := 0x80c6b683.
Lemma Fx_7f908 : fetch_word Asan.M.loaded_segments (0x7f958 : word) = Some Wx_7f908.
Proof. vm_refl. Qed.
Lemma Dx_7f908 : decode_any Wx_7f908 = Some (Load SZ8 true 13 13 2060, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f90c : bv 32 := 0x000680e7.
Lemma Fx_7f90c : fetch_word Asan.M.loaded_segments (0x7f95c : word) = Some Wx_7f90c.
Proof. vm_refl. Qed.
Lemma Dx_7f90c : decode_any Wx_7f90c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f910 : bv 32 := 0x07010113.
Lemma Fx_7f910 : fetch_word Asan.M.loaded_segments (0x7f960 : word) = Some Wx_7f910.
Proof. vm_refl. Qed.
Lemma Dx_7f910 : decode_any Wx_7f910 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f914 : bv 32 := 0x7e813083.
Lemma Fx_7f914 : fetch_word Asan.M.loaded_segments (0x7f964 : word) = Some Wx_7f914.
Proof. vm_refl. Qed.
Lemma Dx_7f914 : decode_any Wx_7f914 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f918 : bv 32 := 0x7e013403.
Lemma Fx_7f918 : fetch_word Asan.M.loaded_segments (0x7f968 : word) = Some Wx_7f918.
Proof. vm_refl. Qed.
Lemma Dx_7f918 : decode_any Wx_7f918 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f91c : bv 32 := 0x7d813483.
Lemma Fx_7f91c : fetch_word Asan.M.loaded_segments (0x7f96c : word) = Some Wx_7f91c.
Proof. vm_refl. Qed.
Lemma Dx_7f91c : decode_any Wx_7f91c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f920 : bv 32 := 0x7d013903.
Lemma Fx_7f920 : fetch_word Asan.M.loaded_segments (0x7f970 : word) = Some Wx_7f920.
Proof. vm_refl. Qed.
Lemma Dx_7f920 : decode_any Wx_7f920 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f924 : bv 32 := 0x7c813983.
Lemma Fx_7f924 : fetch_word Asan.M.loaded_segments (0x7f974 : word) = Some Wx_7f924.
Proof. vm_refl. Qed.
Lemma Dx_7f924 : decode_any Wx_7f924 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f928 : bv 32 := 0x7c013a03.
Lemma Fx_7f928 : fetch_word Asan.M.loaded_segments (0x7f978 : word) = Some Wx_7f928.
Proof. vm_refl. Qed.
Lemma Dx_7f928 : decode_any Wx_7f928 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f92c : bv 32 := 0x7b813a83.
Lemma Fx_7f92c : fetch_word Asan.M.loaded_segments (0x7f97c : word) = Some Wx_7f92c.
Proof. vm_refl. Qed.
Lemma Dx_7f92c : decode_any Wx_7f92c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f930 : bv 32 := 0x7b013b03.
Lemma Fx_7f930 : fetch_word Asan.M.loaded_segments (0x7f980 : word) = Some Wx_7f930.
Proof. vm_refl. Qed.
Lemma Dx_7f930 : decode_any Wx_7f930 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f934 : bv 32 := 0x7f010113.
Lemma Fx_7f934 : fetch_word Asan.M.loaded_segments (0x7f984 : word) = Some Wx_7f934.
Proof. vm_refl. Qed.
Lemma Dx_7f934 : decode_any Wx_7f934 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7f938 : bv 32 := 0x00008067.
Lemma Fx_7f938 : fetch_word Asan.M.loaded_segments (0x7f988 : word) = Some Wx_7f938.
Proof. vm_refl. Qed.
Lemma Dx_7f938 : decode_any Wx_7f938 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa14 : bv 32 := 0x02061e63.
Lemma Fx_7fa14 : fetch_word Asan.M.loaded_segments (0x7fa64 : word) = Some Wx_7fa14.
Proof. vm_refl. Qed.
Lemma Dx_7fa14 : decode_any Wx_7fa14 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa18 : bv 32 := 0xeedff06f.
Lemma Fx_7fa18 : fetch_word Asan.M.loaded_segments (0x7fa68 : word) = Some Wx_7fa18.
Proof. vm_refl. Qed.
Lemma Dx_7fa18 : decode_any Wx_7fa18 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa1c : bv 32 := 0x00070803.
Lemma Fx_7fa1c : fetch_word Asan.M.loaded_segments (0x7fa6c : word) = Some Wx_7fa1c.
Proof. vm_refl. Qed.
Lemma Dx_7fa1c : decode_any Wx_7fa1c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa20 : bv 32 := 0x0077f793.
Lemma Fx_7fa20 : fetch_word Asan.M.loaded_segments (0x7fa70 : word) = Some Wx_7fa20.
Proof. vm_refl. Qed.
Lemma Dx_7fa20 : decode_any Wx_7fa20 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa24 : bv 32 := 0x010038b3.
Lemma Fx_7fa24 : fetch_word Asan.M.loaded_segments (0x7fa74 : word) = Some Wx_7fa24.
Proof. vm_refl. Qed.
Lemma Dx_7fa24 : decode_any Wx_7fa24 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa28 : bv 32 := 0x0107a7b3.
Lemma Fx_7fa28 : fetch_word Asan.M.loaded_segments (0x7fa78 : word) = Some Wx_7fa28.
Proof. vm_refl. Qed.
Lemma Dx_7fa28 : decode_any Wx_7fa28 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa2c : bv 32 := 0x0017c793.
Lemma Fx_7fa2c : fetch_word Asan.M.loaded_segments (0x7fa7c : word) = Some Wx_7fa2c.
Proof. vm_refl. Qed.
Lemma Dx_7fa2c : decode_any Wx_7fa2c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa30 : bv 32 := 0x00f8f7b3.
Lemma Fx_7fa30 : fetch_word Asan.M.loaded_segments (0x7fa80 : word) = Some Wx_7fa30.
Proof. vm_refl. Qed.
Lemma Dx_7fa30 : decode_any Wx_7fa30 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa34 : bv 32 := 0x00e6fa63.
Lemma Fx_7fa34 : fetch_word Asan.M.loaded_segments (0x7fa84 : word) = Some Wx_7fa34.
Proof. vm_refl. Qed.
Lemma Dx_7fa34 : decode_any Wx_7fa34 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa38 : bv 32 := 0x0006c803.
Lemma Fx_7fa38 : fetch_word Asan.M.loaded_segments (0x7fa88 : word) = Some Wx_7fa38.
Proof. vm_refl. Qed.
Lemma Dx_7fa38 : decode_any Wx_7fa38 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa3c : bv 32 := 0x00168693.
Lemma Fx_7fa3c : fetch_word Asan.M.loaded_segments (0x7fa8c : word) = Some Wx_7fa3c.
Proof. vm_refl. Qed.
Lemma Dx_7fa3c : decode_any Wx_7fa3c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa40 : bv 32 := 0x00f867b3.
Lemma Fx_7fa40 : fetch_word Asan.M.loaded_segments (0x7fa90 : word) = Some Wx_7fa40.
Proof. vm_refl. Qed.
Lemma Dx_7fa40 : decode_any Wx_7fa40 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa44 : bv 32 := 0xfee69ae3.
Lemma Fx_7fa44 : fetch_word Asan.M.loaded_segments (0x7fa94 : word) = Some Wx_7fa44.
Proof. vm_refl. Qed.
Lemma Dx_7fa44 : decode_any Wx_7fa44 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa48 : bv 32 := 0x0ff7f693.
Lemma Fx_7fa48 : fetch_word Asan.M.loaded_segments (0x7fa98 : word) = Some Wx_7fa48.
Proof. vm_refl. Qed.
Lemma Dx_7fa48 : decode_any Wx_7fa48 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa4c : bv 32 := 0xea068ce3.
Lemma Fx_7fa4c : fetch_word Asan.M.loaded_segments (0x7fa9c : word) = Some Wx_7fa4c.
Proof. vm_refl. Qed.
Lemma Dx_7fa4c : decode_any Wx_7fa4c = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa50 : bv 32 := 0x00050493.
Lemma Fx_7fa50 : fetch_word Asan.M.loaded_segments (0x7faa0 : word) = Some Wx_7fa50.
Proof. vm_refl. Qed.
Lemma Dx_7fa50 : decode_any Wx_7fa50 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa54 : bv 32 := 0x00058b13.
Lemma Fx_7fa54 : fetch_word Asan.M.loaded_segments (0x7faa4 : word) = Some Wx_7fa54.
Proof. vm_refl. Qed.
Lemma Dx_7fa54 : decode_any Wx_7fa54 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa58 : bv 32 := 0x00060593.
Lemma Fx_7fa58 : fetch_word Asan.M.loaded_segments (0x7faa8 : word) = Some Wx_7fa58.
Proof. vm_refl. Qed.
Lemma Dx_7fa58 : decode_any Wx_7fa58 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa5c : bv 32 := 0x00060913.
Lemma Fx_7fa5c : fetch_word Asan.M.loaded_segments (0x7faac : word) = Some Wx_7fa5c.
Proof. vm_refl. Qed.
Lemma Dx_7fa5c : decode_any Wx_7fa5c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa60 : bv 32 := 0x3f1020ef.
Lemma Fx_7fa60 : fetch_word Asan.M.loaded_segments (0x7fab0 : word) = Some Wx_7fa60.
Proof. vm_refl. Qed.
Lemma Dx_7fa60 : decode_any Wx_7fa60 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa64 : bv 32 := 0x000b0593.
Lemma Fx_7fa64 : fetch_word Asan.M.loaded_segments (0x7fab4 : word) = Some Wx_7fa64.
Proof. vm_refl. Qed.
Lemma Dx_7fa64 : decode_any Wx_7fa64 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa68 : bv 32 := 0x00090613.
Lemma Fx_7fa68 : fetch_word Asan.M.loaded_segments (0x7fab8 : word) = Some Wx_7fa68.
Proof. vm_refl. Qed.
Lemma Dx_7fa68 : decode_any Wx_7fa68 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa6c : bv 32 := 0x00050993.
Lemma Fx_7fa6c : fetch_word Asan.M.loaded_segments (0x7fabc : word) = Some Wx_7fa6c.
Proof. vm_refl. Qed.
Lemma Dx_7fa6c : decode_any Wx_7fa6c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa70 : bv 32 := 0x00048513.
Lemma Fx_7fa70 : fetch_word Asan.M.loaded_segments (0x7fac0 : word) = Some Wx_7fa70.
Proof. vm_refl. Qed.
Lemma Dx_7fa70 : decode_any Wx_7fa70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fa74 : bv 32 := 0xe80988e3.
Lemma Fx_7fa74 : fetch_word Asan.M.loaded_segments (0x7fac4 : word) = Some Wx_7fa74.
Proof. vm_refl. Qed.
Lemma Dx_7fa74 : decode_any Wx_7fa74 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

