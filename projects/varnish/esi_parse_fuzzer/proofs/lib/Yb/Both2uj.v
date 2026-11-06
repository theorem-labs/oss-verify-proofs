(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a1f90 : bv 32 := 0x0e060a63.
Lemma F_a1f90 : fetch_word AsanUbsan.M.loaded_segments (0xa1f90 : word) = Some W_a1f90.
Proof. vm_refl. Qed.
Lemma D_a1f90 : decode_any W_a1f90 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f94 : bv 32 := 0x00b50023.
Lemma F_a1f94 : fetch_word AsanUbsan.M.loaded_segments (0xa1f94 : word) = Some W_a1f94.
Proof. vm_refl. Qed.
Lemma D_a1f94 : decode_any W_a1f94 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f98 : bv 32 := 0x00c506b3.
Lemma F_a1f98 : fetch_word AsanUbsan.M.loaded_segments (0xa1f98 : word) = Some W_a1f98.
Proof. vm_refl. Qed.
Lemma D_a1f98 : decode_any W_a1f98 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f9c : bv 32 := 0x00300713.
Lemma F_a1f9c : fetch_word AsanUbsan.M.loaded_segments (0xa1f9c : word) = Some W_a1f9c.
Proof. vm_refl. Qed.
Lemma D_a1f9c : decode_any W_a1f9c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fa0 : bv 32 := 0xfeb68fa3.
Lemma F_a1fa0 : fetch_word AsanUbsan.M.loaded_segments (0xa1fa0 : word) = Some W_a1fa0.
Proof. vm_refl. Qed.
Lemma D_a1fa0 : decode_any W_a1fa0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fa4 : bv 32 := 0x0ee66063.
Lemma F_a1fa4 : fetch_word AsanUbsan.M.loaded_segments (0xa1fa4 : word) = Some W_a1fa4.
Proof. vm_refl. Qed.
Lemma D_a1fa4 : decode_any W_a1fa4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fa8 : bv 32 := 0x00b500a3.
Lemma F_a1fa8 : fetch_word AsanUbsan.M.loaded_segments (0xa1fa8 : word) = Some W_a1fa8.
Proof. vm_refl. Qed.
Lemma D_a1fa8 : decode_any W_a1fa8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fac : bv 32 := 0x00b50123.
Lemma F_a1fac : fetch_word AsanUbsan.M.loaded_segments (0xa1fac : word) = Some W_a1fac.
Proof. vm_refl. Qed.
Lemma D_a1fac : decode_any W_a1fac = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fb0 : bv 32 := 0x00700713.
Lemma F_a1fb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1fb0 : word) = Some W_a1fb0.
Proof. vm_refl. Qed.
Lemma D_a1fb0 : decode_any W_a1fb0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fb4 : bv 32 := 0xfeb68ea3.
Lemma F_a1fb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1fb4 : word) = Some W_a1fb4.
Proof. vm_refl. Qed.
Lemma D_a1fb4 : decode_any W_a1fb4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fb8 : bv 32 := 0xfeb68f23.
Lemma F_a1fb8 : fetch_word AsanUbsan.M.loaded_segments (0xa1fb8 : word) = Some W_a1fb8.
Proof. vm_refl. Qed.
Lemma D_a1fb8 : decode_any W_a1fb8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fbc : bv 32 := 0x0ce66463.
Lemma F_a1fbc : fetch_word AsanUbsan.M.loaded_segments (0xa1fbc : word) = Some W_a1fbc.
Proof. vm_refl. Qed.
Lemma D_a1fbc : decode_any W_a1fbc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fc0 : bv 32 := 0x00b501a3.
Lemma F_a1fc0 : fetch_word AsanUbsan.M.loaded_segments (0xa1fc0 : word) = Some W_a1fc0.
Proof. vm_refl. Qed.
Lemma D_a1fc0 : decode_any W_a1fc0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fc4 : bv 32 := 0x00900793.
Lemma F_a1fc4 : fetch_word AsanUbsan.M.loaded_segments (0xa1fc4 : word) = Some W_a1fc4.
Proof. vm_refl. Qed.
Lemma D_a1fc4 : decode_any W_a1fc4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fc8 : bv 32 := 0xfeb68e23.
Lemma F_a1fc8 : fetch_word AsanUbsan.M.loaded_segments (0xa1fc8 : word) = Some W_a1fc8.
Proof. vm_refl. Qed.
Lemma D_a1fc8 : decode_any W_a1fc8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fcc : bv 32 := 0x0af66c63.
Lemma F_a1fcc : fetch_word AsanUbsan.M.loaded_segments (0xa1fcc : word) = Some W_a1fcc.
Proof. vm_refl. Qed.
Lemma D_a1fcc : decode_any W_a1fcc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fd0 : bv 32 := 0x40a006bb.
Lemma F_a1fd0 : fetch_word AsanUbsan.M.loaded_segments (0xa1fd0 : word) = Some W_a1fd0.
Proof. vm_refl. Qed.
Lemma D_a1fd0 : decode_any W_a1fd0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fd4 : bv 32 := 0x03859813.
Lemma F_a1fd4 : fetch_word AsanUbsan.M.loaded_segments (0xa1fd4 : word) = Some W_a1fd4.
Proof. vm_refl. Qed.
Lemma D_a1fd4 : decode_any W_a1fd4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fd8 : bv 32 := 0x101015b7.
Lemma F_a1fd8 : fetch_word AsanUbsan.M.loaded_segments (0xa1fd8 : word) = Some W_a1fd8.
Proof. vm_refl. Qed.
Lemma D_a1fd8 : decode_any W_a1fd8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fdc : bv 32 := 0x0036f693.
Lemma F_a1fdc : fetch_word AsanUbsan.M.loaded_segments (0xa1fdc : word) = Some W_a1fdc.
Proof. vm_refl. Qed.
Lemma D_a1fdc : decode_any W_a1fdc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fe0 : bv 32 := 0x00459713.
Lemma F_a1fe0 : fetch_word AsanUbsan.M.loaded_segments (0xa1fe0 : word) = Some W_a1fe0.
Proof. vm_refl. Qed.
Lemma D_a1fe0 : decode_any W_a1fe0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fe4 : bv 32 := 0x40d60633.
Lemma F_a1fe4 : fetch_word AsanUbsan.M.loaded_segments (0xa1fe4 : word) = Some W_a1fe4.
Proof. vm_refl. Qed.
Lemma D_a1fe4 : decode_any W_a1fe4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fe8 : bv 32 := 0x00d505b3.
Lemma F_a1fe8 : fetch_word AsanUbsan.M.loaded_segments (0xa1fe8 : word) = Some W_a1fe8.
Proof. vm_refl. Qed.
Lemma D_a1fe8 : decode_any W_a1fe8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1fec : bv 32 := 0x10070693.
Lemma F_a1fec : fetch_word AsanUbsan.M.loaded_segments (0xa1fec : word) = Some W_a1fec.
Proof. vm_refl. Qed.
Lemma D_a1fec : decode_any W_a1fec = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ff0 : bv 32 := 0xffc67713.
Lemma F_a1ff0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ff0 : word) = Some W_a1ff0.
Proof. vm_refl. Qed.
Lemma D_a1ff0 : decode_any W_a1ff0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ff4 : bv 32 := 0x02d83633.
Lemma F_a1ff4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ff4 : word) = Some W_a1ff4.
Proof. vm_refl. Qed.
Lemma D_a1ff4 : decode_any W_a1ff4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ff8 : bv 32 := 0x00c5a023.
Lemma F_a1ff8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ff8 : word) = Some W_a1ff8.
Proof. vm_refl. Qed.
Lemma D_a1ff8 : decode_any W_a1ff8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ffc : bv 32 := 0x00e586b3.
Lemma F_a1ffc : fetch_word AsanUbsan.M.loaded_segments (0xa1ffc : word) = Some W_a1ffc.
Proof. vm_refl. Qed.
Lemma D_a1ffc : decode_any W_a1ffc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2000 : bv 32 := 0xfec6ae23.
Lemma F_a2000 : fetch_word AsanUbsan.M.loaded_segments (0xa2000 : word) = Some W_a2000.
Proof. vm_refl. Qed.
Lemma D_a2000 : decode_any W_a2000 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2004 : bv 32 := 0x08f76063.
Lemma F_a2004 : fetch_word AsanUbsan.M.loaded_segments (0xa2004 : word) = Some W_a2004.
Proof. vm_refl. Qed.
Lemma D_a2004 : decode_any W_a2004 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2008 : bv 32 := 0x00c5a223.
Lemma F_a2008 : fetch_word AsanUbsan.M.loaded_segments (0xa2008 : word) = Some W_a2008.
Proof. vm_refl. Qed.
Lemma D_a2008 : decode_any W_a2008 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a200c : bv 32 := 0x00c5a423.
Lemma F_a200c : fetch_word AsanUbsan.M.loaded_segments (0xa200c : word) = Some W_a200c.
Proof. vm_refl. Qed.
Lemma D_a200c : decode_any W_a200c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2010 : bv 32 := 0x01900793.
Lemma F_a2010 : fetch_word AsanUbsan.M.loaded_segments (0xa2010 : word) = Some W_a2010.
Proof. vm_refl. Qed.
Lemma D_a2010 : decode_any W_a2010 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2014 : bv 32 := 0xfec6aa23.
Lemma F_a2014 : fetch_word AsanUbsan.M.loaded_segments (0xa2014 : word) = Some W_a2014.
Proof. vm_refl. Qed.
Lemma D_a2014 : decode_any W_a2014 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2018 : bv 32 := 0xfec6ac23.
Lemma F_a2018 : fetch_word AsanUbsan.M.loaded_segments (0xa2018 : word) = Some W_a2018.
Proof. vm_refl. Qed.
Lemma D_a2018 : decode_any W_a2018 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a201c : bv 32 := 0x06f76463.
Lemma F_a201c : fetch_word AsanUbsan.M.loaded_segments (0xa201c : word) = Some W_a201c.
Proof. vm_refl. Qed.
Lemma D_a201c : decode_any W_a201c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2020 : bv 32 := 0x00c5a623.
Lemma F_a2020 : fetch_word AsanUbsan.M.loaded_segments (0xa2020 : word) = Some W_a2020.
Proof. vm_refl. Qed.
Lemma D_a2020 : decode_any W_a2020 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2024 : bv 32 := 0x00c5a823.
Lemma F_a2024 : fetch_word AsanUbsan.M.loaded_segments (0xa2024 : word) = Some W_a2024.
Proof. vm_refl. Qed.
Lemma D_a2024 : decode_any W_a2024 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2028 : bv 32 := 0x00c5aa23.
Lemma F_a2028 : fetch_word AsanUbsan.M.loaded_segments (0xa2028 : word) = Some W_a2028.
Proof. vm_refl. Qed.
Lemma D_a2028 : decode_any W_a2028 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a202c : bv 32 := 0x00c5ac23.
Lemma F_a202c : fetch_word AsanUbsan.M.loaded_segments (0xa202c : word) = Some W_a202c.
Proof. vm_refl. Qed.
Lemma D_a202c : decode_any W_a202c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2030 : bv 32 := 0x0045f793.
Lemma F_a2030 : fetch_word AsanUbsan.M.loaded_segments (0xa2030 : word) = Some W_a2030.
Proof. vm_refl. Qed.
Lemma D_a2030 : decode_any W_a2030 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2034 : bv 32 := 0x02000813.
Lemma F_a2034 : fetch_word AsanUbsan.M.loaded_segments (0xa2034 : word) = Some W_a2034.
Proof. vm_refl. Qed.
Lemma D_a2034 : decode_any W_a2034 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2038 : bv 32 := 0x01878793.
Lemma F_a2038 : fetch_word AsanUbsan.M.loaded_segments (0xa2038 : word) = Some W_a2038.
Proof. vm_refl. Qed.
Lemma D_a2038 : decode_any W_a2038 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a203c : bv 32 := 0x40f70733.
Lemma F_a203c : fetch_word AsanUbsan.M.loaded_segments (0xa203c : word) = Some W_a203c.
Proof. vm_refl. Qed.
Lemma D_a203c : decode_any W_a203c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2040 : bv 32 := 0xfec6a223.
Lemma F_a2040 : fetch_word AsanUbsan.M.loaded_segments (0xa2040 : word) = Some W_a2040.
Proof. vm_refl. Qed.
Lemma D_a2040 : decode_any W_a2040 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2044 : bv 32 := 0xfec6a423.
Lemma F_a2044 : fetch_word AsanUbsan.M.loaded_segments (0xa2044 : word) = Some W_a2044.
Proof. vm_refl. Qed.
Lemma D_a2044 : decode_any W_a2044 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2048 : bv 32 := 0xfec6a623.
Lemma F_a2048 : fetch_word AsanUbsan.M.loaded_segments (0xa2048 : word) = Some W_a2048.
Proof. vm_refl. Qed.
Lemma D_a2048 : decode_any W_a2048 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a204c : bv 32 := 0xfec6a823.
Lemma F_a204c : fetch_word AsanUbsan.M.loaded_segments (0xa204c : word) = Some W_a204c.
Proof. vm_refl. Qed.
Lemma D_a204c : decode_any W_a204c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2050 : bv 32 := 0x03076a63.
Lemma F_a2050 : fetch_word AsanUbsan.M.loaded_segments (0xa2050 : word) = Some W_a2050.
Proof. vm_refl. Qed.
Lemma D_a2050 : decode_any W_a2050 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2054 : bv 32 := 0x02061613.
Lemma F_a2054 : fetch_word AsanUbsan.M.loaded_segments (0xa2054 : word) = Some W_a2054.
Proof. vm_refl. Qed.
Lemma D_a2054 : decode_any W_a2054 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2058 : bv 32 := 0x00f585b3.
Lemma F_a2058 : fetch_word AsanUbsan.M.loaded_segments (0xa2058 : word) = Some W_a2058.
Proof. vm_refl. Qed.
Lemma D_a2058 : decode_any W_a2058 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a205c : bv 32 := 0x02065693.
Lemma F_a205c : fetch_word AsanUbsan.M.loaded_segments (0xa205c : word) = Some W_a205c.
Proof. vm_refl. Qed.
Lemma D_a205c : decode_any W_a205c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2060 : bv 32 := 0x00d66633.
Lemma F_a2060 : fetch_word AsanUbsan.M.loaded_segments (0xa2060 : word) = Some W_a2060.
Proof. vm_refl. Qed.
Lemma D_a2060 : decode_any W_a2060 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2064 : bv 32 := 0x01f00693.
Lemma F_a2064 : fetch_word AsanUbsan.M.loaded_segments (0xa2064 : word) = Some W_a2064.
Proof. vm_refl. Qed.
Lemma D_a2064 : decode_any W_a2064 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2068 : bv 32 := 0x00c5b023.
Lemma F_a2068 : fetch_word AsanUbsan.M.loaded_segments (0xa2068 : word) = Some W_a2068.
Proof. vm_refl. Qed.
Lemma D_a2068 : decode_any W_a2068 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a206c : bv 32 := 0x00c5b423.
Lemma F_a206c : fetch_word AsanUbsan.M.loaded_segments (0xa206c : word) = Some W_a206c.
Proof. vm_refl. Qed.
Lemma D_a206c : decode_any W_a206c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2070 : bv 32 := 0x00c5b823.
Lemma F_a2070 : fetch_word AsanUbsan.M.loaded_segments (0xa2070 : word) = Some W_a2070.
Proof. vm_refl. Qed.
Lemma D_a2070 : decode_any W_a2070 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2074 : bv 32 := 0x00c5bc23.
Lemma F_a2074 : fetch_word AsanUbsan.M.loaded_segments (0xa2074 : word) = Some W_a2074.
Proof. vm_refl. Qed.
Lemma D_a2074 : decode_any W_a2074 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2078 : bv 32 := 0xfe070713.
Lemma F_a2078 : fetch_word AsanUbsan.M.loaded_segments (0xa2078 : word) = Some W_a2078.
Proof. vm_refl. Qed.
Lemma D_a2078 : decode_any W_a2078 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a207c : bv 32 := 0x02058593.
Lemma F_a207c : fetch_word AsanUbsan.M.loaded_segments (0xa207c : word) = Some W_a207c.
Proof. vm_refl. Qed.
Lemma D_a207c : decode_any W_a207c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2080 : bv 32 := 0xfee6e4e3.
Lemma F_a2080 : fetch_word AsanUbsan.M.loaded_segments (0xa2080 : word) = Some W_a2080.
Proof. vm_refl. Qed.
Lemma D_a2080 : decode_any W_a2080 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2084 : bv 32 := 0x00008067.
Lemma F_a2084 : fetch_word AsanUbsan.M.loaded_segments (0xa2084 : word) = Some W_a2084.
Proof. vm_refl. Qed.
Lemma D_a2084 : decode_any W_a2084 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xa1f90%Z.
Definition Fo_000 := F_a1f90.
Definition Do_000 := D_a1f90.
Definition Fo_004 := F_a1f94.
Definition Do_004 := D_a1f94.
Definition Fo_008 := F_a1f98.
Definition Do_008 := D_a1f98.
Definition Fo_00c := F_a1f9c.
Definition Do_00c := D_a1f9c.
Definition Fo_010 := F_a1fa0.
Definition Do_010 := D_a1fa0.
Definition Fo_014 := F_a1fa4.
Definition Do_014 := D_a1fa4.
Definition Fo_018 := F_a1fa8.
Definition Do_018 := D_a1fa8.
Definition Fo_01c := F_a1fac.
Definition Do_01c := D_a1fac.
Definition Fo_020 := F_a1fb0.
Definition Do_020 := D_a1fb0.
Definition Fo_024 := F_a1fb4.
Definition Do_024 := D_a1fb4.
Definition Fo_028 := F_a1fb8.
Definition Do_028 := D_a1fb8.
Definition Fo_02c := F_a1fbc.
Definition Do_02c := D_a1fbc.
Definition Fo_030 := F_a1fc0.
Definition Do_030 := D_a1fc0.
Definition Fo_034 := F_a1fc4.
Definition Do_034 := D_a1fc4.
Definition Fo_038 := F_a1fc8.
Definition Do_038 := D_a1fc8.
Definition Fo_03c := F_a1fcc.
Definition Do_03c := D_a1fcc.
Definition Fo_040 := F_a1fd0.
Definition Do_040 := D_a1fd0.
Definition Fo_044 := F_a1fd4.
Definition Do_044 := D_a1fd4.
Definition Fo_048 := F_a1fd8.
Definition Do_048 := D_a1fd8.
Definition Fo_04c := F_a1fdc.
Definition Do_04c := D_a1fdc.
Definition Fo_050 := F_a1fe0.
Definition Do_050 := D_a1fe0.
Definition Fo_054 := F_a1fe4.
Definition Do_054 := D_a1fe4.
Definition Fo_058 := F_a1fe8.
Definition Do_058 := D_a1fe8.
Definition Fo_05c := F_a1fec.
Definition Do_05c := D_a1fec.
Definition Fo_060 := F_a1ff0.
Definition Do_060 := D_a1ff0.
Definition Fo_064 := F_a1ff4.
Definition Do_064 := D_a1ff4.
Definition Fo_068 := F_a1ff8.
Definition Do_068 := D_a1ff8.
Definition Fo_06c := F_a1ffc.
Definition Do_06c := D_a1ffc.
Definition Fo_070 := F_a2000.
Definition Do_070 := D_a2000.
Definition Fo_074 := F_a2004.
Definition Do_074 := D_a2004.
Definition Fo_078 := F_a2008.
Definition Do_078 := D_a2008.
Definition Fo_07c := F_a200c.
Definition Do_07c := D_a200c.
Definition Fo_080 := F_a2010.
Definition Do_080 := D_a2010.
Definition Fo_084 := F_a2014.
Definition Do_084 := D_a2014.
Definition Fo_088 := F_a2018.
Definition Do_088 := D_a2018.
Definition Fo_08c := F_a201c.
Definition Do_08c := D_a201c.
Definition Fo_090 := F_a2020.
Definition Do_090 := D_a2020.
Definition Fo_094 := F_a2024.
Definition Do_094 := D_a2024.
Definition Fo_098 := F_a2028.
Definition Do_098 := D_a2028.
Definition Fo_09c := F_a202c.
Definition Do_09c := D_a202c.
Definition Fo_0a0 := F_a2030.
Definition Do_0a0 := D_a2030.
Definition Fo_0a4 := F_a2034.
Definition Do_0a4 := D_a2034.
Definition Fo_0a8 := F_a2038.
Definition Do_0a8 := D_a2038.
Definition Fo_0ac := F_a203c.
Definition Do_0ac := D_a203c.
Definition Fo_0b0 := F_a2040.
Definition Do_0b0 := D_a2040.
Definition Fo_0b4 := F_a2044.
Definition Do_0b4 := D_a2044.
Definition Fo_0b8 := F_a2048.
Definition Do_0b8 := D_a2048.
Definition Fo_0bc := F_a204c.
Definition Do_0bc := D_a204c.
Definition Fo_0c0 := F_a2050.
Definition Do_0c0 := D_a2050.
Definition Fo_0c4 := F_a2054.
Definition Do_0c4 := D_a2054.
Definition Fo_0c8 := F_a2058.
Definition Do_0c8 := D_a2058.
Definition Fo_0cc := F_a205c.
Definition Do_0cc := D_a205c.
Definition Fo_0d0 := F_a2060.
Definition Do_0d0 := D_a2060.
Definition Fo_0d4 := F_a2064.
Definition Do_0d4 := D_a2064.
Definition Fo_0d8 := F_a2068.
Definition Do_0d8 := D_a2068.
Definition Fo_0dc := F_a206c.
Definition Do_0dc := D_a206c.
Definition Fo_0e0 := F_a2070.
Definition Do_0e0 := D_a2070.
Definition Fo_0e4 := F_a2074.
Definition Do_0e4 := D_a2074.
Definition Fo_0e8 := F_a2078.
Definition Do_0e8 := D_a2078.
Definition Fo_0ec := F_a207c.
Definition Do_0ec := D_a207c.
Definition Fo_0f0 := F_a2080.
Definition Do_0f0 := D_a2080.
Definition Fo_0f4 := F_a2084.
Definition Do_0f4 := D_a2084.
