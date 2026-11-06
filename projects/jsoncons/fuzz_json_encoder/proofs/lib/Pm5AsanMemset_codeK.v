(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_156880 : bv 32 := 0x0e060a63.
Lemma F_156880 : fetch_word AsanUbsan.M.loaded_segments (0x1568bc : word) = Some W_156880.
Proof. vm_refl. Qed.
Lemma D_156880 : decode_any W_156880 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156884 : bv 32 := 0x00b50023.
Lemma F_156884 : fetch_word AsanUbsan.M.loaded_segments (0x1568c0 : word) = Some W_156884.
Proof. vm_refl. Qed.
Lemma D_156884 : decode_any W_156884 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156888 : bv 32 := 0x00c506b3.
Lemma F_156888 : fetch_word AsanUbsan.M.loaded_segments (0x1568c4 : word) = Some W_156888.
Proof. vm_refl. Qed.
Lemma D_156888 : decode_any W_156888 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15688c : bv 32 := 0x00300713.
Lemma F_15688c : fetch_word AsanUbsan.M.loaded_segments (0x1568c8 : word) = Some W_15688c.
Proof. vm_refl. Qed.
Lemma D_15688c : decode_any W_15688c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156890 : bv 32 := 0xfeb68fa3.
Lemma F_156890 : fetch_word AsanUbsan.M.loaded_segments (0x1568cc : word) = Some W_156890.
Proof. vm_refl. Qed.
Lemma D_156890 : decode_any W_156890 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156894 : bv 32 := 0x0ee66063.
Lemma F_156894 : fetch_word AsanUbsan.M.loaded_segments (0x1568d0 : word) = Some W_156894.
Proof. vm_refl. Qed.
Lemma D_156894 : decode_any W_156894 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156898 : bv 32 := 0x00b500a3.
Lemma F_156898 : fetch_word AsanUbsan.M.loaded_segments (0x1568d4 : word) = Some W_156898.
Proof. vm_refl. Qed.
Lemma D_156898 : decode_any W_156898 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15689c : bv 32 := 0x00b50123.
Lemma F_15689c : fetch_word AsanUbsan.M.loaded_segments (0x1568d8 : word) = Some W_15689c.
Proof. vm_refl. Qed.
Lemma D_15689c : decode_any W_15689c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568a0 : bv 32 := 0x00700713.
Lemma F_1568a0 : fetch_word AsanUbsan.M.loaded_segments (0x1568dc : word) = Some W_1568a0.
Proof. vm_refl. Qed.
Lemma D_1568a0 : decode_any W_1568a0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568a4 : bv 32 := 0xfeb68ea3.
Lemma F_1568a4 : fetch_word AsanUbsan.M.loaded_segments (0x1568e0 : word) = Some W_1568a4.
Proof. vm_refl. Qed.
Lemma D_1568a4 : decode_any W_1568a4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568a8 : bv 32 := 0xfeb68f23.
Lemma F_1568a8 : fetch_word AsanUbsan.M.loaded_segments (0x1568e4 : word) = Some W_1568a8.
Proof. vm_refl. Qed.
Lemma D_1568a8 : decode_any W_1568a8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568ac : bv 32 := 0x0ce66463.
Lemma F_1568ac : fetch_word AsanUbsan.M.loaded_segments (0x1568e8 : word) = Some W_1568ac.
Proof. vm_refl. Qed.
Lemma D_1568ac : decode_any W_1568ac = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568b0 : bv 32 := 0x00b501a3.
Lemma F_1568b0 : fetch_word AsanUbsan.M.loaded_segments (0x1568ec : word) = Some W_1568b0.
Proof. vm_refl. Qed.
Lemma D_1568b0 : decode_any W_1568b0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568b4 : bv 32 := 0x00900793.
Lemma F_1568b4 : fetch_word AsanUbsan.M.loaded_segments (0x1568f0 : word) = Some W_1568b4.
Proof. vm_refl. Qed.
Lemma D_1568b4 : decode_any W_1568b4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568b8 : bv 32 := 0xfeb68e23.
Lemma F_1568b8 : fetch_word AsanUbsan.M.loaded_segments (0x1568f4 : word) = Some W_1568b8.
Proof. vm_refl. Qed.
Lemma D_1568b8 : decode_any W_1568b8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568bc : bv 32 := 0x0af66c63.
Lemma F_1568bc : fetch_word AsanUbsan.M.loaded_segments (0x1568f8 : word) = Some W_1568bc.
Proof. vm_refl. Qed.
Lemma D_1568bc : decode_any W_1568bc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c0 : bv 32 := 0x40a006bb.
Lemma F_1568c0 : fetch_word AsanUbsan.M.loaded_segments (0x1568fc : word) = Some W_1568c0.
Proof. vm_refl. Qed.
Lemma D_1568c0 : decode_any W_1568c0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c4 : bv 32 := 0x03859813.
Lemma F_1568c4 : fetch_word AsanUbsan.M.loaded_segments (0x156900 : word) = Some W_1568c4.
Proof. vm_refl. Qed.
Lemma D_1568c4 : decode_any W_1568c4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c8 : bv 32 := 0x101015b7.
Lemma F_1568c8 : fetch_word AsanUbsan.M.loaded_segments (0x156904 : word) = Some W_1568c8.
Proof. vm_refl. Qed.
Lemma D_1568c8 : decode_any W_1568c8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568cc : bv 32 := 0x0036f693.
Lemma F_1568cc : fetch_word AsanUbsan.M.loaded_segments (0x156908 : word) = Some W_1568cc.
Proof. vm_refl. Qed.
Lemma D_1568cc : decode_any W_1568cc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568d0 : bv 32 := 0x00459713.
Lemma F_1568d0 : fetch_word AsanUbsan.M.loaded_segments (0x15690c : word) = Some W_1568d0.
Proof. vm_refl. Qed.
Lemma D_1568d0 : decode_any W_1568d0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568d4 : bv 32 := 0x40d60633.
Lemma F_1568d4 : fetch_word AsanUbsan.M.loaded_segments (0x156910 : word) = Some W_1568d4.
Proof. vm_refl. Qed.
Lemma D_1568d4 : decode_any W_1568d4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568d8 : bv 32 := 0x00d505b3.
Lemma F_1568d8 : fetch_word AsanUbsan.M.loaded_segments (0x156914 : word) = Some W_1568d8.
Proof. vm_refl. Qed.
Lemma D_1568d8 : decode_any W_1568d8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568dc : bv 32 := 0x10070693.
Lemma F_1568dc : fetch_word AsanUbsan.M.loaded_segments (0x156918 : word) = Some W_1568dc.
Proof. vm_refl. Qed.
Lemma D_1568dc : decode_any W_1568dc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568e0 : bv 32 := 0xffc67713.
Lemma F_1568e0 : fetch_word AsanUbsan.M.loaded_segments (0x15691c : word) = Some W_1568e0.
Proof. vm_refl. Qed.
Lemma D_1568e0 : decode_any W_1568e0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568e4 : bv 32 := 0x02d83633.
Lemma F_1568e4 : fetch_word AsanUbsan.M.loaded_segments (0x156920 : word) = Some W_1568e4.
Proof. vm_refl. Qed.
Lemma D_1568e4 : decode_any W_1568e4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568e8 : bv 32 := 0x00c5a023.
Lemma F_1568e8 : fetch_word AsanUbsan.M.loaded_segments (0x156924 : word) = Some W_1568e8.
Proof. vm_refl. Qed.
Lemma D_1568e8 : decode_any W_1568e8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568ec : bv 32 := 0x00e586b3.
Lemma F_1568ec : fetch_word AsanUbsan.M.loaded_segments (0x156928 : word) = Some W_1568ec.
Proof. vm_refl. Qed.
Lemma D_1568ec : decode_any W_1568ec = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568f0 : bv 32 := 0xfec6ae23.
Lemma F_1568f0 : fetch_word AsanUbsan.M.loaded_segments (0x15692c : word) = Some W_1568f0.
Proof. vm_refl. Qed.
Lemma D_1568f0 : decode_any W_1568f0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568f4 : bv 32 := 0x08f76063.
Lemma F_1568f4 : fetch_word AsanUbsan.M.loaded_segments (0x156930 : word) = Some W_1568f4.
Proof. vm_refl. Qed.
Lemma D_1568f4 : decode_any W_1568f4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568f8 : bv 32 := 0x00c5a223.
Lemma F_1568f8 : fetch_word AsanUbsan.M.loaded_segments (0x156934 : word) = Some W_1568f8.
Proof. vm_refl. Qed.
Lemma D_1568f8 : decode_any W_1568f8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568fc : bv 32 := 0x00c5a423.
Lemma F_1568fc : fetch_word AsanUbsan.M.loaded_segments (0x156938 : word) = Some W_1568fc.
Proof. vm_refl. Qed.
Lemma D_1568fc : decode_any W_1568fc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156900 : bv 32 := 0x01900793.
Lemma F_156900 : fetch_word AsanUbsan.M.loaded_segments (0x15693c : word) = Some W_156900.
Proof. vm_refl. Qed.
Lemma D_156900 : decode_any W_156900 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156904 : bv 32 := 0xfec6aa23.
Lemma F_156904 : fetch_word AsanUbsan.M.loaded_segments (0x156940 : word) = Some W_156904.
Proof. vm_refl. Qed.
Lemma D_156904 : decode_any W_156904 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156908 : bv 32 := 0xfec6ac23.
Lemma F_156908 : fetch_word AsanUbsan.M.loaded_segments (0x156944 : word) = Some W_156908.
Proof. vm_refl. Qed.
Lemma D_156908 : decode_any W_156908 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15690c : bv 32 := 0x06f76463.
Lemma F_15690c : fetch_word AsanUbsan.M.loaded_segments (0x156948 : word) = Some W_15690c.
Proof. vm_refl. Qed.
Lemma D_15690c : decode_any W_15690c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156910 : bv 32 := 0x00c5a623.
Lemma F_156910 : fetch_word AsanUbsan.M.loaded_segments (0x15694c : word) = Some W_156910.
Proof. vm_refl. Qed.
Lemma D_156910 : decode_any W_156910 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156914 : bv 32 := 0x00c5a823.
Lemma F_156914 : fetch_word AsanUbsan.M.loaded_segments (0x156950 : word) = Some W_156914.
Proof. vm_refl. Qed.
Lemma D_156914 : decode_any W_156914 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156918 : bv 32 := 0x00c5aa23.
Lemma F_156918 : fetch_word AsanUbsan.M.loaded_segments (0x156954 : word) = Some W_156918.
Proof. vm_refl. Qed.
Lemma D_156918 : decode_any W_156918 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15691c : bv 32 := 0x00c5ac23.
Lemma F_15691c : fetch_word AsanUbsan.M.loaded_segments (0x156958 : word) = Some W_15691c.
Proof. vm_refl. Qed.
Lemma D_15691c : decode_any W_15691c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156920 : bv 32 := 0x0045f793.
Lemma F_156920 : fetch_word AsanUbsan.M.loaded_segments (0x15695c : word) = Some W_156920.
Proof. vm_refl. Qed.
Lemma D_156920 : decode_any W_156920 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156924 : bv 32 := 0x02000813.
Lemma F_156924 : fetch_word AsanUbsan.M.loaded_segments (0x156960 : word) = Some W_156924.
Proof. vm_refl. Qed.
Lemma D_156924 : decode_any W_156924 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156928 : bv 32 := 0x01878793.
Lemma F_156928 : fetch_word AsanUbsan.M.loaded_segments (0x156964 : word) = Some W_156928.
Proof. vm_refl. Qed.
Lemma D_156928 : decode_any W_156928 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15692c : bv 32 := 0x40f70733.
Lemma F_15692c : fetch_word AsanUbsan.M.loaded_segments (0x156968 : word) = Some W_15692c.
Proof. vm_refl. Qed.
Lemma D_15692c : decode_any W_15692c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156930 : bv 32 := 0xfec6a223.
Lemma F_156930 : fetch_word AsanUbsan.M.loaded_segments (0x15696c : word) = Some W_156930.
Proof. vm_refl. Qed.
Lemma D_156930 : decode_any W_156930 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156934 : bv 32 := 0xfec6a423.
Lemma F_156934 : fetch_word AsanUbsan.M.loaded_segments (0x156970 : word) = Some W_156934.
Proof. vm_refl. Qed.
Lemma D_156934 : decode_any W_156934 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156938 : bv 32 := 0xfec6a623.
Lemma F_156938 : fetch_word AsanUbsan.M.loaded_segments (0x156974 : word) = Some W_156938.
Proof. vm_refl. Qed.
Lemma D_156938 : decode_any W_156938 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15693c : bv 32 := 0xfec6a823.
Lemma F_15693c : fetch_word AsanUbsan.M.loaded_segments (0x156978 : word) = Some W_15693c.
Proof. vm_refl. Qed.
Lemma D_15693c : decode_any W_15693c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156940 : bv 32 := 0x03076a63.
Lemma F_156940 : fetch_word AsanUbsan.M.loaded_segments (0x15697c : word) = Some W_156940.
Proof. vm_refl. Qed.
Lemma D_156940 : decode_any W_156940 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156944 : bv 32 := 0x02061613.
Lemma F_156944 : fetch_word AsanUbsan.M.loaded_segments (0x156980 : word) = Some W_156944.
Proof. vm_refl. Qed.
Lemma D_156944 : decode_any W_156944 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156948 : bv 32 := 0x00f585b3.
Lemma F_156948 : fetch_word AsanUbsan.M.loaded_segments (0x156984 : word) = Some W_156948.
Proof. vm_refl. Qed.
Lemma D_156948 : decode_any W_156948 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15694c : bv 32 := 0x02065693.
Lemma F_15694c : fetch_word AsanUbsan.M.loaded_segments (0x156988 : word) = Some W_15694c.
Proof. vm_refl. Qed.
Lemma D_15694c : decode_any W_15694c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156950 : bv 32 := 0x00d66633.
Lemma F_156950 : fetch_word AsanUbsan.M.loaded_segments (0x15698c : word) = Some W_156950.
Proof. vm_refl. Qed.
Lemma D_156950 : decode_any W_156950 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156954 : bv 32 := 0x01f00693.
Lemma F_156954 : fetch_word AsanUbsan.M.loaded_segments (0x156990 : word) = Some W_156954.
Proof. vm_refl. Qed.
Lemma D_156954 : decode_any W_156954 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156958 : bv 32 := 0x00c5b023.
Lemma F_156958 : fetch_word AsanUbsan.M.loaded_segments (0x156994 : word) = Some W_156958.
Proof. vm_refl. Qed.
Lemma D_156958 : decode_any W_156958 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15695c : bv 32 := 0x00c5b423.
Lemma F_15695c : fetch_word AsanUbsan.M.loaded_segments (0x156998 : word) = Some W_15695c.
Proof. vm_refl. Qed.
Lemma D_15695c : decode_any W_15695c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156960 : bv 32 := 0x00c5b823.
Lemma F_156960 : fetch_word AsanUbsan.M.loaded_segments (0x15699c : word) = Some W_156960.
Proof. vm_refl. Qed.
Lemma D_156960 : decode_any W_156960 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156964 : bv 32 := 0x00c5bc23.
Lemma F_156964 : fetch_word AsanUbsan.M.loaded_segments (0x1569a0 : word) = Some W_156964.
Proof. vm_refl. Qed.
Lemma D_156964 : decode_any W_156964 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156968 : bv 32 := 0xfe070713.
Lemma F_156968 : fetch_word AsanUbsan.M.loaded_segments (0x1569a4 : word) = Some W_156968.
Proof. vm_refl. Qed.
Lemma D_156968 : decode_any W_156968 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15696c : bv 32 := 0x02058593.
Lemma F_15696c : fetch_word AsanUbsan.M.loaded_segments (0x1569a8 : word) = Some W_15696c.
Proof. vm_refl. Qed.
Lemma D_15696c : decode_any W_15696c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156970 : bv 32 := 0xfee6e4e3.
Lemma F_156970 : fetch_word AsanUbsan.M.loaded_segments (0x1569ac : word) = Some W_156970.
Proof. vm_refl. Qed.
Lemma D_156970 : decode_any W_156970 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156974 : bv 32 := 0x00008067.
Lemma F_156974 : fetch_word AsanUbsan.M.loaded_segments (0x1569b0 : word) = Some W_156974.
Proof. vm_refl. Qed.
Lemma D_156974 : decode_any W_156974 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x1568bc%Z.
Definition Fo_000 := F_156880.
Definition Do_000 := D_156880.
Definition Fo_004 := F_156884.
Definition Do_004 := D_156884.
Definition Fo_008 := F_156888.
Definition Do_008 := D_156888.
Definition Fo_00c := F_15688c.
Definition Do_00c := D_15688c.
Definition Fo_010 := F_156890.
Definition Do_010 := D_156890.
Definition Fo_014 := F_156894.
Definition Do_014 := D_156894.
Definition Fo_018 := F_156898.
Definition Do_018 := D_156898.
Definition Fo_01c := F_15689c.
Definition Do_01c := D_15689c.
Definition Fo_020 := F_1568a0.
Definition Do_020 := D_1568a0.
Definition Fo_024 := F_1568a4.
Definition Do_024 := D_1568a4.
Definition Fo_028 := F_1568a8.
Definition Do_028 := D_1568a8.
Definition Fo_02c := F_1568ac.
Definition Do_02c := D_1568ac.
Definition Fo_030 := F_1568b0.
Definition Do_030 := D_1568b0.
Definition Fo_034 := F_1568b4.
Definition Do_034 := D_1568b4.
Definition Fo_038 := F_1568b8.
Definition Do_038 := D_1568b8.
Definition Fo_03c := F_1568bc.
Definition Do_03c := D_1568bc.
Definition Fo_040 := F_1568c0.
Definition Do_040 := D_1568c0.
Definition Fo_044 := F_1568c4.
Definition Do_044 := D_1568c4.
Definition Fo_048 := F_1568c8.
Definition Do_048 := D_1568c8.
Definition Fo_04c := F_1568cc.
Definition Do_04c := D_1568cc.
Definition Fo_050 := F_1568d0.
Definition Do_050 := D_1568d0.
Definition Fo_054 := F_1568d4.
Definition Do_054 := D_1568d4.
Definition Fo_058 := F_1568d8.
Definition Do_058 := D_1568d8.
Definition Fo_05c := F_1568dc.
Definition Do_05c := D_1568dc.
Definition Fo_060 := F_1568e0.
Definition Do_060 := D_1568e0.
Definition Fo_064 := F_1568e4.
Definition Do_064 := D_1568e4.
Definition Fo_068 := F_1568e8.
Definition Do_068 := D_1568e8.
Definition Fo_06c := F_1568ec.
Definition Do_06c := D_1568ec.
Definition Fo_070 := F_1568f0.
Definition Do_070 := D_1568f0.
Definition Fo_074 := F_1568f4.
Definition Do_074 := D_1568f4.
Definition Fo_078 := F_1568f8.
Definition Do_078 := D_1568f8.
Definition Fo_07c := F_1568fc.
Definition Do_07c := D_1568fc.
Definition Fo_080 := F_156900.
Definition Do_080 := D_156900.
Definition Fo_084 := F_156904.
Definition Do_084 := D_156904.
Definition Fo_088 := F_156908.
Definition Do_088 := D_156908.
Definition Fo_08c := F_15690c.
Definition Do_08c := D_15690c.
Definition Fo_090 := F_156910.
Definition Do_090 := D_156910.
Definition Fo_094 := F_156914.
Definition Do_094 := D_156914.
Definition Fo_098 := F_156918.
Definition Do_098 := D_156918.
Definition Fo_09c := F_15691c.
Definition Do_09c := D_15691c.
Definition Fo_0a0 := F_156920.
Definition Do_0a0 := D_156920.
Definition Fo_0a4 := F_156924.
Definition Do_0a4 := D_156924.
Definition Fo_0a8 := F_156928.
Definition Do_0a8 := D_156928.
Definition Fo_0ac := F_15692c.
Definition Do_0ac := D_15692c.
Definition Fo_0b0 := F_156930.
Definition Do_0b0 := D_156930.
Definition Fo_0b4 := F_156934.
Definition Do_0b4 := D_156934.
Definition Fo_0b8 := F_156938.
Definition Do_0b8 := D_156938.
Definition Fo_0bc := F_15693c.
Definition Do_0bc := D_15693c.
Definition Fo_0c0 := F_156940.
Definition Do_0c0 := D_156940.
Definition Fo_0c4 := F_156944.
Definition Do_0c4 := D_156944.
Definition Fo_0c8 := F_156948.
Definition Do_0c8 := D_156948.
Definition Fo_0cc := F_15694c.
Definition Do_0cc := D_15694c.
Definition Fo_0d0 := F_156950.
Definition Do_0d0 := D_156950.
Definition Fo_0d4 := F_156954.
Definition Do_0d4 := D_156954.
Definition Fo_0d8 := F_156958.
Definition Do_0d8 := D_156958.
Definition Fo_0dc := F_15695c.
Definition Do_0dc := D_15695c.
Definition Fo_0e0 := F_156960.
Definition Do_0e0 := D_156960.
Definition Fo_0e4 := F_156964.
Definition Do_0e4 := D_156964.
Definition Fo_0e8 := F_156968.
Definition Do_0e8 := D_156968.
Definition Fo_0ec := F_15696c.
Definition Do_0ec := D_15696c.
Definition Fo_0f0 := F_156970.
Definition Do_0f0 := D_156970.
Definition Fo_0f4 := F_156974.
Definition Do_0f4 := D_156974.
