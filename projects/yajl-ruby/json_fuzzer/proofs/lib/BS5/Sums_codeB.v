(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_65358 : bv 32 := 0x02060063.
Lemma F_65358 : fetch_word AsanUbsan.M.loaded_segments (0x651ac : word) = Some W_65358.
Proof. vm_refl. Qed.
Lemma D_65358 : decode_any W_65358 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6535c : bv 32 := 0x00c50633.
Lemma F_6535c : fetch_word AsanUbsan.M.loaded_segments (0x651b0 : word) = Some W_6535c.
Proof. vm_refl. Qed.
Lemma D_6535c : decode_any W_6535c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65360 : bv 32 := 0x00050693.
Lemma F_65360 : fetch_word AsanUbsan.M.loaded_segments (0x651b4 : word) = Some W_65360.
Proof. vm_refl. Qed.
Lemma D_65360 : decode_any W_65360 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65364 : bv 32 := 0x0005c703.
Lemma F_65364 : fetch_word AsanUbsan.M.loaded_segments (0x651b8 : word) = Some W_65364.
Proof. vm_refl. Qed.
Lemma D_65364 : decode_any W_65364 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65368 : bv 32 := 0x00e68023.
Lemma F_65368 : fetch_word AsanUbsan.M.loaded_segments (0x651bc : word) = Some W_65368.
Proof. vm_refl. Qed.
Lemma D_65368 : decode_any W_65368 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6536c : bv 32 := 0x00168693.
Lemma F_6536c : fetch_word AsanUbsan.M.loaded_segments (0x651c0 : word) = Some W_6536c.
Proof. vm_refl. Qed.
Lemma D_6536c : decode_any W_6536c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65370 : bv 32 := 0x00158593.
Lemma F_65370 : fetch_word AsanUbsan.M.loaded_segments (0x651c4 : word) = Some W_65370.
Proof. vm_refl. Qed.
Lemma D_65370 : decode_any W_65370 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65374 : bv 32 := 0xfec698e3.
Lemma F_65374 : fetch_word AsanUbsan.M.loaded_segments (0x651c8 : word) = Some W_65374.
Proof. vm_refl. Qed.
Lemma D_65374 : decode_any W_65374 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65378 : bv 32 := 0x00008067.
Lemma F_65378 : fetch_word AsanUbsan.M.loaded_segments (0x651cc : word) = Some W_65378.
Proof. vm_refl. Qed.
Lemma D_65378 : decode_any W_65378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_653d4 : bv 32 := 0x00a666b3.
Lemma F_653d4 : fetch_word AsanUbsan.M.loaded_segments (0x65228 : word) = Some W_653d4.
Proof. vm_refl. Qed.
Lemma D_653d4 : decode_any W_653d4 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d8 : bv 32 := 0x00f6f693.
Lemma F_653d8 : fetch_word AsanUbsan.M.loaded_segments (0x6522c : word) = Some W_653d8.
Proof. vm_refl. Qed.
Lemma D_653d8 : decode_any W_653d8 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653dc : bv 32 := 0x02068063.
Lemma F_653dc : fetch_word AsanUbsan.M.loaded_segments (0x65230 : word) = Some W_653dc.
Proof. vm_refl. Qed.
Lemma D_653dc : decode_any W_653dc = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e0 : bv 32 := 0x04060863.
Lemma F_653e0 : fetch_word AsanUbsan.M.loaded_segments (0x65234 : word) = Some W_653e0.
Proof. vm_refl. Qed.
Lemma D_653e0 : decode_any W_653e0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e4 : bv 32 := 0x00c50633.
Lemma F_653e4 : fetch_word AsanUbsan.M.loaded_segments (0x65238 : word) = Some W_653e4.
Proof. vm_refl. Qed.
Lemma D_653e4 : decode_any W_653e4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e8 : bv 32 := 0x00050693.
Lemma F_653e8 : fetch_word AsanUbsan.M.loaded_segments (0x6523c : word) = Some W_653e8.
Proof. vm_refl. Qed.
Lemma D_653e8 : decode_any W_653e8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653ec : bv 32 := 0x00b68023.
Lemma F_653ec : fetch_word AsanUbsan.M.loaded_segments (0x65240 : word) = Some W_653ec.
Proof. vm_refl. Qed.
Lemma D_653ec : decode_any W_653ec = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f0 : bv 32 := 0x00168693.
Lemma F_653f0 : fetch_word AsanUbsan.M.loaded_segments (0x65244 : word) = Some W_653f0.
Proof. vm_refl. Qed.
Lemma D_653f0 : decode_any W_653f0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f4 : bv 32 := 0xfec69ce3.
Lemma F_653f4 : fetch_word AsanUbsan.M.loaded_segments (0x65248 : word) = Some W_653f4.
Proof. vm_refl. Qed.
Lemma D_653f4 : decode_any W_653f4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f8 : bv 32 := 0x0380006f.
Lemma F_653f8 : fetch_word AsanUbsan.M.loaded_segments (0x6524c : word) = Some W_653f8.
Proof. vm_refl. Qed.
Lemma D_653f8 : decode_any W_653f8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653fc : bv 32 := 0x02060a63.
Lemma F_653fc : fetch_word AsanUbsan.M.loaded_segments (0x65250 : word) = Some W_653fc.
Proof. vm_refl. Qed.
Lemma D_653fc : decode_any W_653fc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65400 : bv 32 := 0x00c50633.
Lemma F_65400 : fetch_word AsanUbsan.M.loaded_segments (0x65254 : word) = Some W_65400.
Proof. vm_refl. Qed.
Lemma D_65400 : decode_any W_65400 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65404 : bv 32 := 0x00859693.
Lemma F_65404 : fetch_word AsanUbsan.M.loaded_segments (0x65258 : word) = Some W_65404.
Proof. vm_refl. Qed.
Lemma D_65404 : decode_any W_65404 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65408 : bv 32 := 0x00b6e5b3.
Lemma F_65408 : fetch_word AsanUbsan.M.loaded_segments (0x6525c : word) = Some W_65408.
Proof. vm_refl. Qed.
Lemma D_65408 : decode_any W_65408 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6540c : bv 32 := 0x01059693.
Lemma F_6540c : fetch_word AsanUbsan.M.loaded_segments (0x65260 : word) = Some W_6540c.
Proof. vm_refl. Qed.
Lemma D_6540c : decode_any W_6540c = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65410 : bv 32 := 0x00b6e5b3.
Lemma F_65410 : fetch_word AsanUbsan.M.loaded_segments (0x65264 : word) = Some W_65410.
Proof. vm_refl. Qed.
Lemma D_65410 : decode_any W_65410 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65414 : bv 32 := 0x02059693.
Lemma F_65414 : fetch_word AsanUbsan.M.loaded_segments (0x65268 : word) = Some W_65414.
Proof. vm_refl. Qed.
Lemma D_65414 : decode_any W_65414 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65418 : bv 32 := 0x00b6e5b3.
Lemma F_65418 : fetch_word AsanUbsan.M.loaded_segments (0x6526c : word) = Some W_65418.
Proof. vm_refl. Qed.
Lemma D_65418 : decode_any W_65418 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6541c : bv 32 := 0x00050693.
Lemma F_6541c : fetch_word AsanUbsan.M.loaded_segments (0x65270 : word) = Some W_6541c.
Proof. vm_refl. Qed.
Lemma D_6541c : decode_any W_6541c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65420 : bv 32 := 0x00b6b023.
Lemma F_65420 : fetch_word AsanUbsan.M.loaded_segments (0x65274 : word) = Some W_65420.
Proof. vm_refl. Qed.
Lemma D_65420 : decode_any W_65420 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65424 : bv 32 := 0x00b6b423.
Lemma F_65424 : fetch_word AsanUbsan.M.loaded_segments (0x65278 : word) = Some W_65424.
Proof. vm_refl. Qed.
Lemma D_65424 : decode_any W_65424 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65428 : bv 32 := 0x01068693.
Lemma F_65428 : fetch_word AsanUbsan.M.loaded_segments (0x6527c : word) = Some W_65428.
Proof. vm_refl. Qed.
Lemma D_65428 : decode_any W_65428 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6542c : bv 32 := 0xfec6eae3.
Lemma F_6542c : fetch_word AsanUbsan.M.loaded_segments (0x65280 : word) = Some W_6542c.
Proof. vm_refl. Qed.
Lemma D_6542c : decode_any W_6542c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65430 : bv 32 := 0x00008067.
Lemma F_65430 : fetch_word AsanUbsan.M.loaded_segments (0x65284 : word) = Some W_65430.
Proof. vm_refl. Qed.
Lemma D_65430 : decode_any W_65430 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_65904 : bv 32 := 0xff010113.
Lemma F_65904 : fetch_word AsanUbsan.M.loaded_segments (0x65758 : word) = Some W_65904.
Proof. vm_refl. Qed.
Lemma D_65904 : decode_any W_65904 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65908 : bv 32 := 0x00113423.
Lemma F_65908 : fetch_word AsanUbsan.M.loaded_segments (0x6575c : word) = Some W_65908.
Proof. vm_refl. Qed.
Lemma D_65908 : decode_any W_65908 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6590c : bv 32 := 0x00058693.
Lemma F_6590c : fetch_word AsanUbsan.M.loaded_segments (0x65760 : word) = Some W_6590c.
Proof. vm_refl. Qed.
Lemma D_6590c : decode_any W_6590c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65910 : bv 32 := 0x00100713.
Lemma F_65910 : fetch_word AsanUbsan.M.loaded_segments (0x65764 : word) = Some W_65910.
Proof. vm_refl. Qed.
Lemma D_65910 : decode_any W_65910 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65914 : bv 32 := 0x02871713.
Lemma F_65914 : fetch_word AsanUbsan.M.loaded_segments (0x65768 : word) = Some W_65914.
Proof. vm_refl. Qed.
Lemma D_65914 : decode_any W_65914 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65918 : bv 32 := 0x00170593.
Lemma F_65918 : fetch_word AsanUbsan.M.loaded_segments (0x6576c : word) = Some W_65918.
Proof. vm_refl. Qed.
Lemma D_65918 : decode_any W_65918 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6591c : bv 32 := 0x08b6f263.
Lemma F_6591c : fetch_word AsanUbsan.M.loaded_segments (0x65770 : word) = Some W_6591c.
Proof. vm_refl. Qed.
Lemma D_6591c : decode_any W_6591c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65920 : bv 32 := 0x00000593.
Lemma F_65920 : fetch_word AsanUbsan.M.loaded_segments (0x65774 : word) = Some W_65920.
Proof. vm_refl. Qed.
Lemma D_65920 : decode_any W_65920 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65924 : bv 32 := 0x00d50733.
Lemma F_65924 : fetch_word AsanUbsan.M.loaded_segments (0x65778 : word) = Some W_65924.
Proof. vm_refl. Qed.
Lemma D_65924 : decode_any W_65924 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65928 : bv 32 := 0x00750793.
Lemma F_65928 : fetch_word AsanUbsan.M.loaded_segments (0x6577c : word) = Some W_65928.
Proof. vm_refl. Qed.
Lemma D_65928 : decode_any W_65928 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6592c : bv 32 := 0xff87f793.
Lemma F_6592c : fetch_word AsanUbsan.M.loaded_segments (0x65780 : word) = Some W_6592c.
Proof. vm_refl. Qed.
Lemma D_6592c : decode_any W_6592c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65930 : bv 32 := 0xff877613.
Lemma F_65930 : fetch_word AsanUbsan.M.loaded_segments (0x65784 : word) = Some W_65930.
Proof. vm_refl. Qed.
Lemma D_65930 : decode_any W_65930 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65934 : bv 32 := 0x02f57463.
Lemma F_65934 : fetch_word AsanUbsan.M.loaded_segments (0x65788 : word) = Some W_65934.
Proof. vm_refl. Qed.
Lemma D_65934 : decode_any W_65934 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65938 : bv 32 := 0x02068263.
Lemma F_65938 : fetch_word AsanUbsan.M.loaded_segments (0x6578c : word) = Some W_65938.
Proof. vm_refl. Qed.
Lemma D_65938 : decode_any W_65938 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6593c : bv 32 := 0x00000593.
Lemma F_6593c : fetch_word AsanUbsan.M.loaded_segments (0x65790 : word) = Some W_6593c.
Proof. vm_refl. Qed.
Lemma D_6593c : decode_any W_6593c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65940 : bv 32 := 0x00150693.
Lemma F_65940 : fetch_word AsanUbsan.M.loaded_segments (0x65794 : word) = Some W_65940.
Proof. vm_refl. Qed.
Lemma D_65940 : decode_any W_65940 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65944 : bv 32 := 0x00068813.
Lemma F_65944 : fetch_word AsanUbsan.M.loaded_segments (0x65798 : word) = Some W_65944.
Proof. vm_refl. Qed.
Lemma D_65944 : decode_any W_65944 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65948 : bv 32 := 0xfff6c683.
Lemma F_65948 : fetch_word AsanUbsan.M.loaded_segments (0x6579c : word) = Some W_65948.
Proof. vm_refl. Qed.
Lemma D_65948 : decode_any W_65948 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6594c : bv 32 := 0x00d5e5b3.
Lemma F_6594c : fetch_word AsanUbsan.M.loaded_segments (0x657a0 : word) = Some W_6594c.
Proof. vm_refl. Qed.
Lemma D_6594c : decode_any W_6594c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65950 : bv 32 := 0x00f87663.
Lemma F_65950 : fetch_word AsanUbsan.M.loaded_segments (0x657a4 : word) = Some W_65950.
Proof. vm_refl. Qed.
Lemma D_65950 : decode_any W_65950 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65954 : bv 32 := 0x00180693.
Lemma F_65954 : fetch_word AsanUbsan.M.loaded_segments (0x657a8 : word) = Some W_65954.
Proof. vm_refl. Qed.
Lemma D_65954 : decode_any W_65954 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65958 : bv 32 := 0xfee866e3.
Lemma F_65958 : fetch_word AsanUbsan.M.loaded_segments (0x657ac : word) = Some W_65958.
Proof. vm_refl. Qed.
Lemma D_65958 : decode_any W_65958 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6595c : bv 32 := 0x00c7fa63.
Lemma F_6595c : fetch_word AsanUbsan.M.loaded_segments (0x657b0 : word) = Some W_6595c.
Proof. vm_refl. Qed.
Lemma D_6595c : decode_any W_6595c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65960 : bv 32 := 0x0007b683.
Lemma F_65960 : fetch_word AsanUbsan.M.loaded_segments (0x657b4 : word) = Some W_65960.
Proof. vm_refl. Qed.
Lemma D_65960 : decode_any W_65960 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65964 : bv 32 := 0x00878793.
Lemma F_65964 : fetch_word AsanUbsan.M.loaded_segments (0x657b8 : word) = Some W_65964.
Proof. vm_refl. Qed.
Lemma D_65964 : decode_any W_65964 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65968 : bv 32 := 0x00b6e5b3.
Lemma F_65968 : fetch_word AsanUbsan.M.loaded_segments (0x657bc : word) = Some W_65968.
Proof. vm_refl. Qed.
Lemma D_65968 : decode_any W_65968 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6596c : bv 32 := 0xfec7eae3.
Lemma F_6596c : fetch_word AsanUbsan.M.loaded_segments (0x657c0 : word) = Some W_6596c.
Proof. vm_refl. Qed.
Lemma D_6596c : decode_any W_6596c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65970 : bv 32 := 0x02a66063.
Lemma F_65970 : fetch_word AsanUbsan.M.loaded_segments (0x657c4 : word) = Some W_65970.
Proof. vm_refl. Qed.
Lemma D_65970 : decode_any W_65970 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65974 : bv 32 := 0x00e67e63.
Lemma F_65974 : fetch_word AsanUbsan.M.loaded_segments (0x657c8 : word) = Some W_65974.
Proof. vm_refl. Qed.
Lemma D_65974 : decode_any W_65974 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65978 : bv 32 := 0x40c70733.
Lemma F_65978 : fetch_word AsanUbsan.M.loaded_segments (0x657cc : word) = Some W_65978.
Proof. vm_refl. Qed.
Lemma D_65978 : decode_any W_65978 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6597c : bv 32 := 0x00064503.
Lemma F_6597c : fetch_word AsanUbsan.M.loaded_segments (0x657d0 : word) = Some W_6597c.
Proof. vm_refl. Qed.
Lemma D_6597c : decode_any W_6597c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65980 : bv 32 := 0xfff70713.
Lemma F_65980 : fetch_word AsanUbsan.M.loaded_segments (0x657d4 : word) = Some W_65980.
Proof. vm_refl. Qed.
Lemma D_65980 : decode_any W_65980 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65984 : bv 32 := 0x00a5e5b3.
Lemma F_65984 : fetch_word AsanUbsan.M.loaded_segments (0x657d8 : word) = Some W_65984.
Proof. vm_refl. Qed.
Lemma D_65984 : decode_any W_65984 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65988 : bv 32 := 0x00160613.
Lemma F_65988 : fetch_word AsanUbsan.M.loaded_segments (0x657dc : word) = Some W_65988.
Proof. vm_refl. Qed.
Lemma D_65988 : decode_any W_65988 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6598c : bv 32 := 0xfe0718e3.
Lemma F_6598c : fetch_word AsanUbsan.M.loaded_segments (0x657e0 : word) = Some W_6598c.
Proof. vm_refl. Qed.
Lemma D_6598c : decode_any W_6598c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65990 : bv 32 := 0x0015b513.
Lemma F_65990 : fetch_word AsanUbsan.M.loaded_segments (0x657e4 : word) = Some W_65990.
Proof. vm_refl. Qed.
Lemma D_65990 : decode_any W_65990 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65994 : bv 32 := 0x00813083.
Lemma F_65994 : fetch_word AsanUbsan.M.loaded_segments (0x657e8 : word) = Some W_65994.
Proof. vm_refl. Qed.
Lemma D_65994 : decode_any W_65994 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65998 : bv 32 := 0x01010113.
Lemma F_65998 : fetch_word AsanUbsan.M.loaded_segments (0x657ec : word) = Some W_65998.
Proof. vm_refl. Qed.
Lemma D_65998 : decode_any W_65998 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6599c : bv 32 := 0x00008067.
Lemma F_6599c : fetch_word AsanUbsan.M.loaded_segments (0x657f0 : word) = Some W_6599c.
Proof. vm_refl. Qed.
Lemma D_6599c : decode_any W_6599c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
