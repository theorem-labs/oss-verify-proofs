(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_26728 : bv 32 := 0x0116a223.
Lemma F_26728 : fetch_word Ubsan.M.loaded_segments (0x308a0 : word) = Some W_26728.
Proof. vm_refl. Qed.
Lemma D_26728 : decode_any W_26728 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2672c : bv 32 := 0x0056a423.
Lemma F_2672c : fetch_word Ubsan.M.loaded_segments (0x308a4 : word) = Some W_2672c.
Proof. vm_refl. Qed.
Lemma D_2672c : decode_any W_2672c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26730 : bv 32 := 0x0066a623.
Lemma F_26730 : fetch_word Ubsan.M.loaded_segments (0x308a8 : word) = Some W_26730.
Proof. vm_refl. Qed.
Lemma D_26730 : decode_any W_26730 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26734 : bv 32 := 0x01068693.
Lemma F_26734 : fetch_word Ubsan.M.loaded_segments (0x308ac : word) = Some W_26734.
Proof. vm_refl. Qed.
Lemma D_26734 : decode_any W_26734 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26738 : bv 32 := 0x01058593.
Lemma F_26738 : fetch_word Ubsan.M.loaded_segments (0x308b0 : word) = Some W_26738.
Proof. vm_refl. Qed.
Lemma D_26738 : decode_any W_26738 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2673c : bv 32 := 0xfac7e2e3.
Lemma F_2673c : fetch_word Ubsan.M.loaded_segments (0x308b4 : word) = Some W_2673c.
Proof. vm_refl. Qed.
Lemma D_2673c : decode_any W_2673c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26740 : bv 32 := 0xff158593.
Lemma F_26740 : fetch_word Ubsan.M.loaded_segments (0x308b8 : word) = Some W_26740.
Proof. vm_refl. Qed.
Lemma D_26740 : decode_any W_26740 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26744 : bv 32 := 0x01000713.
Lemma F_26744 : fetch_word Ubsan.M.loaded_segments (0x308bc : word) = Some W_26744.
Proof. vm_refl. Qed.
Lemma D_26744 : decode_any W_26744 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26748 : bv 32 := 0xe4e666e3.
Lemma F_26748 : fetch_word Ubsan.M.loaded_segments (0x308c0 : word) = Some W_26748.
Proof. vm_refl. Qed.
Lemma D_26748 : decode_any W_26748 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2674c : bv 32 := 0x0940006f.
Lemma F_2674c : fetch_word Ubsan.M.loaded_segments (0x308c4 : word) = Some W_2674c.
Proof. vm_refl. Qed.
Lemma D_2674c : decode_any W_2674c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26750 : bv 32 := 0x00875793.
Lemma F_26750 : fetch_word Ubsan.M.loaded_segments (0x308c8 : word) = Some W_26750.
Proof. vm_refl. Qed.
Lemma D_26750 : decode_any W_26750 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26754 : bv 32 := 0x01075813.
Lemma F_26754 : fetch_word Ubsan.M.loaded_segments (0x308cc : word) = Some W_26754.
Proof. vm_refl. Qed.
Lemma D_26754 : decode_any W_26754 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26758 : bv 32 := 0xffd60613.
Lemma F_26758 : fetch_word Ubsan.M.loaded_segments (0x308d0 : word) = Some W_26758.
Proof. vm_refl. Qed.
Lemma D_26758 : decode_any W_26758 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2675c : bv 32 := 0x00e68023.
Lemma F_2675c : fetch_word Ubsan.M.loaded_segments (0x308d4 : word) = Some W_2675c.
Proof. vm_refl. Qed.
Lemma D_2675c : decode_any W_2675c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26760 : bv 32 := 0x00f680a3.
Lemma F_26760 : fetch_word Ubsan.M.loaded_segments (0x308d8 : word) = Some W_26760.
Proof. vm_refl. Qed.
Lemma D_26760 : decode_any W_26760 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26764 : bv 32 := 0x01068123.
Lemma F_26764 : fetch_word Ubsan.M.loaded_segments (0x308dc : word) = Some W_26764.
Proof. vm_refl. Qed.
Lemma D_26764 : decode_any W_26764 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26768 : bv 32 := 0x00368693.
Lemma F_26768 : fetch_word Ubsan.M.loaded_segments (0x308e0 : word) = Some W_26768.
Proof. vm_refl. Qed.
Lemma D_26768 : decode_any W_26768 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2676c : bv 32 := 0x01058593.
Lemma F_2676c : fetch_word Ubsan.M.loaded_segments (0x308e4 : word) = Some W_2676c.
Proof. vm_refl. Qed.
Lemma D_2676c : decode_any W_2676c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26770 : bv 32 := 0x01000793.
Lemma F_26770 : fetch_word Ubsan.M.loaded_segments (0x308e8 : word) = Some W_26770.
Proof. vm_refl. Qed.
Lemma D_26770 : decode_any W_26770 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26774 : bv 32 := 0x0187581b.
Lemma F_26774 : fetch_word Ubsan.M.loaded_segments (0x308ec : word) = Some W_26774.
Proof. vm_refl. Qed.
Lemma D_26774 : decode_any W_26774 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26778 : bv 32 := 0xff45a883.
Lemma F_26778 : fetch_word Ubsan.M.loaded_segments (0x308f0 : word) = Some W_26778.
Proof. vm_refl. Qed.
Lemma D_26778 : decode_any W_26778 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2677c : bv 32 := 0xff85a283.
Lemma F_2677c : fetch_word Ubsan.M.loaded_segments (0x308f4 : word) = Some W_2677c.
Proof. vm_refl. Qed.
Lemma D_2677c : decode_any W_2677c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26780 : bv 32 := 0xffc5a303.
Lemma F_26780 : fetch_word Ubsan.M.loaded_segments (0x308f8 : word) = Some W_26780.
Proof. vm_refl. Qed.
Lemma D_26780 : decode_any W_26780 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26784 : bv 32 := 0x0005a703.
Lemma F_26784 : fetch_word Ubsan.M.loaded_segments (0x308fc : word) = Some W_26784.
Proof. vm_refl. Qed.
Lemma D_26784 : decode_any W_26784 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26788 : bv 32 := 0x00889393.
Lemma F_26788 : fetch_word Ubsan.M.loaded_segments (0x30900 : word) = Some W_26788.
Proof. vm_refl. Qed.
Lemma D_26788 : decode_any W_26788 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2678c : bv 32 := 0x0188d89b.
Lemma F_2678c : fetch_word Ubsan.M.loaded_segments (0x30904 : word) = Some W_2678c.
Proof. vm_refl. Qed.
Lemma D_2678c : decode_any W_2678c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26790 : bv 32 := 0x0103e833.
Lemma F_26790 : fetch_word Ubsan.M.loaded_segments (0x30908 : word) = Some W_26790.
Proof. vm_refl. Qed.
Lemma D_26790 : decode_any W_26790 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26794 : bv 32 := 0x00829393.
Lemma F_26794 : fetch_word Ubsan.M.loaded_segments (0x3090c : word) = Some W_26794.
Proof. vm_refl. Qed.
Lemma D_26794 : decode_any W_26794 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26798 : bv 32 := 0x0182d29b.
Lemma F_26798 : fetch_word Ubsan.M.loaded_segments (0x30910 : word) = Some W_26798.
Proof. vm_refl. Qed.
Lemma D_26798 : decode_any W_26798 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2679c : bv 32 := 0x0113e8b3.
Lemma F_2679c : fetch_word Ubsan.M.loaded_segments (0x30914 : word) = Some W_2679c.
Proof. vm_refl. Qed.
Lemma D_2679c : decode_any W_2679c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267a0 : bv 32 := 0x00831393.
Lemma F_267a0 : fetch_word Ubsan.M.loaded_segments (0x30918 : word) = Some W_267a0.
Proof. vm_refl. Qed.
Lemma D_267a0 : decode_any W_267a0 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267a4 : bv 32 := 0x0183531b.
Lemma F_267a4 : fetch_word Ubsan.M.loaded_segments (0x3091c : word) = Some W_267a4.
Proof. vm_refl. Qed.
Lemma D_267a4 : decode_any W_267a4 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267a8 : bv 32 := 0x0053e2b3.
Lemma F_267a8 : fetch_word Ubsan.M.loaded_segments (0x30920 : word) = Some W_267a8.
Proof. vm_refl. Qed.
Lemma D_267a8 : decode_any W_267a8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267ac : bv 32 := 0x00871393.
Lemma F_267ac : fetch_word Ubsan.M.loaded_segments (0x30924 : word) = Some W_267ac.
Proof. vm_refl. Qed.
Lemma D_267ac : decode_any W_267ac = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267b0 : bv 32 := 0x0063e333.
Lemma F_267b0 : fetch_word Ubsan.M.loaded_segments (0x30928 : word) = Some W_267b0.
Proof. vm_refl. Qed.
Lemma D_267b0 : decode_any W_267b0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267b4 : bv 32 := 0xff060613.
Lemma F_267b4 : fetch_word Ubsan.M.loaded_segments (0x3092c : word) = Some W_267b4.
Proof. vm_refl. Qed.
Lemma D_267b4 : decode_any W_267b4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267b8 : bv 32 := 0x0106a023.
Lemma F_267b8 : fetch_word Ubsan.M.loaded_segments (0x30930 : word) = Some W_267b8.
Proof. vm_refl. Qed.
Lemma D_267b8 : decode_any W_267b8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267bc : bv 32 := 0x0116a223.
Lemma F_267bc : fetch_word Ubsan.M.loaded_segments (0x30934 : word) = Some W_267bc.
Proof. vm_refl. Qed.
Lemma D_267bc : decode_any W_267bc = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267c0 : bv 32 := 0x0056a423.
Lemma F_267c0 : fetch_word Ubsan.M.loaded_segments (0x30938 : word) = Some W_267c0.
Proof. vm_refl. Qed.
Lemma D_267c0 : decode_any W_267c0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267c4 : bv 32 := 0x0066a623.
Lemma F_267c4 : fetch_word Ubsan.M.loaded_segments (0x3093c : word) = Some W_267c4.
Proof. vm_refl. Qed.
Lemma D_267c4 : decode_any W_267c4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267c8 : bv 32 := 0x01068693.
Lemma F_267c8 : fetch_word Ubsan.M.loaded_segments (0x30940 : word) = Some W_267c8.
Proof. vm_refl. Qed.
Lemma D_267c8 : decode_any W_267c8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267cc : bv 32 := 0x01058593.
Lemma F_267cc : fetch_word Ubsan.M.loaded_segments (0x30944 : word) = Some W_267cc.
Proof. vm_refl. Qed.
Lemma D_267cc : decode_any W_267cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267d0 : bv 32 := 0xfac7e2e3.
Lemma F_267d0 : fetch_word Ubsan.M.loaded_segments (0x30948 : word) = Some W_267d0.
Proof. vm_refl. Qed.
Lemma D_267d0 : decode_any W_267d0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267d4 : bv 32 := 0xff358593.
Lemma F_267d4 : fetch_word Ubsan.M.loaded_segments (0x3094c : word) = Some W_267d4.
Proof. vm_refl. Qed.
Lemma D_267d4 : decode_any W_267d4 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267d8 : bv 32 := 0x01000713.
Lemma F_267d8 : fetch_word Ubsan.M.loaded_segments (0x30950 : word) = Some W_267d8.
Proof. vm_refl. Qed.
Lemma D_267d8 : decode_any W_267d8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267dc : bv 32 := 0xdae66ce3.
Lemma F_267dc : fetch_word Ubsan.M.loaded_segments (0x30954 : word) = Some W_267dc.
Proof. vm_refl. Qed.
Lemma D_267dc : decode_any W_267dc = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267e0 : bv 32 := 0x0005c703.
Lemma F_267e0 : fetch_word Ubsan.M.loaded_segments (0x30958 : word) = Some W_267e0.
Proof. vm_refl. Qed.
Lemma D_267e0 : decode_any W_267e0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267e4 : bv 32 := 0x0015c783.
Lemma F_267e4 : fetch_word Ubsan.M.loaded_segments (0x3095c : word) = Some W_267e4.
Proof. vm_refl. Qed.
Lemma D_267e4 : decode_any W_267e4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267e8 : bv 32 := 0x0025c803.
Lemma F_267e8 : fetch_word Ubsan.M.loaded_segments (0x30960 : word) = Some W_267e8.
Proof. vm_refl. Qed.
Lemma D_267e8 : decode_any W_267e8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267ec : bv 32 := 0x0035c883.
Lemma F_267ec : fetch_word Ubsan.M.loaded_segments (0x30964 : word) = Some W_267ec.
Proof. vm_refl. Qed.
Lemma D_267ec : decode_any W_267ec = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267f0 : bv 32 := 0x0045c283.
Lemma F_267f0 : fetch_word Ubsan.M.loaded_segments (0x30968 : word) = Some W_267f0.
Proof. vm_refl. Qed.
Lemma D_267f0 : decode_any W_267f0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267f4 : bv 32 := 0x0055c303.
Lemma F_267f4 : fetch_word Ubsan.M.loaded_segments (0x3096c : word) = Some W_267f4.
Proof. vm_refl. Qed.
Lemma D_267f4 : decode_any W_267f4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267f8 : bv 32 := 0x0065c383.
Lemma F_267f8 : fetch_word Ubsan.M.loaded_segments (0x30970 : word) = Some W_267f8.
Proof. vm_refl. Qed.
Lemma D_267f8 : decode_any W_267f8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_267fc : bv 32 := 0x0075ce03.
Lemma F_267fc : fetch_word Ubsan.M.loaded_segments (0x30974 : word) = Some W_267fc.
Proof. vm_refl. Qed.
Lemma D_267fc : decode_any W_267fc = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26800 : bv 32 := 0x00e68023.
Lemma F_26800 : fetch_word Ubsan.M.loaded_segments (0x30978 : word) = Some W_26800.
Proof. vm_refl. Qed.
Lemma D_26800 : decode_any W_26800 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26804 : bv 32 := 0x00f680a3.
Lemma F_26804 : fetch_word Ubsan.M.loaded_segments (0x3097c : word) = Some W_26804.
Proof. vm_refl. Qed.
Lemma D_26804 : decode_any W_26804 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26808 : bv 32 := 0x01068123.
Lemma F_26808 : fetch_word Ubsan.M.loaded_segments (0x30980 : word) = Some W_26808.
Proof. vm_refl. Qed.
Lemma D_26808 : decode_any W_26808 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2680c : bv 32 := 0x011681a3.
Lemma F_2680c : fetch_word Ubsan.M.loaded_segments (0x30984 : word) = Some W_2680c.
Proof. vm_refl. Qed.
Lemma D_2680c : decode_any W_2680c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26810 : bv 32 := 0x0085c703.
Lemma F_26810 : fetch_word Ubsan.M.loaded_segments (0x30988 : word) = Some W_26810.
Proof. vm_refl. Qed.
Lemma D_26810 : decode_any W_26810 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26814 : bv 32 := 0x0095c783.
Lemma F_26814 : fetch_word Ubsan.M.loaded_segments (0x3098c : word) = Some W_26814.
Proof. vm_refl. Qed.
Lemma D_26814 : decode_any W_26814 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26818 : bv 32 := 0x00a5c803.
Lemma F_26818 : fetch_word Ubsan.M.loaded_segments (0x30990 : word) = Some W_26818.
Proof. vm_refl. Qed.
Lemma D_26818 : decode_any W_26818 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2681c : bv 32 := 0x00b5c883.
Lemma F_2681c : fetch_word Ubsan.M.loaded_segments (0x30994 : word) = Some W_2681c.
Proof. vm_refl. Qed.
Lemma D_2681c : decode_any W_2681c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26820 : bv 32 := 0x00568223.
Lemma F_26820 : fetch_word Ubsan.M.loaded_segments (0x30998 : word) = Some W_26820.
Proof. vm_refl. Qed.
Lemma D_26820 : decode_any W_26820 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26824 : bv 32 := 0x006682a3.
Lemma F_26824 : fetch_word Ubsan.M.loaded_segments (0x3099c : word) = Some W_26824.
Proof. vm_refl. Qed.
Lemma D_26824 : decode_any W_26824 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26828 : bv 32 := 0x00768323.
Lemma F_26828 : fetch_word Ubsan.M.loaded_segments (0x309a0 : word) = Some W_26828.
Proof. vm_refl. Qed.
Lemma D_26828 : decode_any W_26828 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2682c : bv 32 := 0x01c683a3.
Lemma F_2682c : fetch_word Ubsan.M.loaded_segments (0x309a4 : word) = Some W_2682c.
Proof. vm_refl. Qed.
Lemma D_2682c : decode_any W_2682c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26830 : bv 32 := 0x00c5c283.
Lemma F_26830 : fetch_word Ubsan.M.loaded_segments (0x309a8 : word) = Some W_26830.
Proof. vm_refl. Qed.
Lemma D_26830 : decode_any W_26830 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26834 : bv 32 := 0x00d5c303.
Lemma F_26834 : fetch_word Ubsan.M.loaded_segments (0x309ac : word) = Some W_26834.
Proof. vm_refl. Qed.
Lemma D_26834 : decode_any W_26834 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26838 : bv 32 := 0x00e5c383.
Lemma F_26838 : fetch_word Ubsan.M.loaded_segments (0x309b0 : word) = Some W_26838.
Proof. vm_refl. Qed.
Lemma D_26838 : decode_any W_26838 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2683c : bv 32 := 0x00f5ce03.
Lemma F_2683c : fetch_word Ubsan.M.loaded_segments (0x309b4 : word) = Some W_2683c.
Proof. vm_refl. Qed.
Lemma D_2683c : decode_any W_2683c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26840 : bv 32 := 0x01058593.
Lemma F_26840 : fetch_word Ubsan.M.loaded_segments (0x309b8 : word) = Some W_26840.
Proof. vm_refl. Qed.
Lemma D_26840 : decode_any W_26840 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26844 : bv 32 := 0x00e68423.
Lemma F_26844 : fetch_word Ubsan.M.loaded_segments (0x309bc : word) = Some W_26844.
Proof. vm_refl. Qed.
Lemma D_26844 : decode_any W_26844 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26848 : bv 32 := 0x00f684a3.
Lemma F_26848 : fetch_word Ubsan.M.loaded_segments (0x309c0 : word) = Some W_26848.
Proof. vm_refl. Qed.
Lemma D_26848 : decode_any W_26848 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2684c : bv 32 := 0x01068523.
Lemma F_2684c : fetch_word Ubsan.M.loaded_segments (0x309c4 : word) = Some W_2684c.
Proof. vm_refl. Qed.
Lemma D_2684c : decode_any W_2684c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26850 : bv 32 := 0x011685a3.
Lemma F_26850 : fetch_word Ubsan.M.loaded_segments (0x309c8 : word) = Some W_26850.
Proof. vm_refl. Qed.
Lemma D_26850 : decode_any W_26850 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26854 : bv 32 := 0x01068713.
Lemma F_26854 : fetch_word Ubsan.M.loaded_segments (0x309cc : word) = Some W_26854.
Proof. vm_refl. Qed.
Lemma D_26854 : decode_any W_26854 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26858 : bv 32 := 0x00568623.
Lemma F_26858 : fetch_word Ubsan.M.loaded_segments (0x309d0 : word) = Some W_26858.
Proof. vm_refl. Qed.
Lemma D_26858 : decode_any W_26858 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2685c : bv 32 := 0x006686a3.
Lemma F_2685c : fetch_word Ubsan.M.loaded_segments (0x309d4 : word) = Some W_2685c.
Proof. vm_refl. Qed.
Lemma D_2685c : decode_any W_2685c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26860 : bv 32 := 0x00768723.
Lemma F_26860 : fetch_word Ubsan.M.loaded_segments (0x309d8 : word) = Some W_26860.
Proof. vm_refl. Qed.
Lemma D_26860 : decode_any W_26860 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26864 : bv 32 := 0x01c687a3.
Lemma F_26864 : fetch_word Ubsan.M.loaded_segments (0x309dc : word) = Some W_26864.
Proof. vm_refl. Qed.
Lemma D_26864 : decode_any W_26864 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26868 : bv 32 := 0x00070693.
Lemma F_26868 : fetch_word Ubsan.M.loaded_segments (0x309e0 : word) = Some W_26868.
Proof. vm_refl. Qed.
Lemma D_26868 : decode_any W_26868 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2686c : bv 32 := 0x00867713.
Lemma F_2686c : fetch_word Ubsan.M.loaded_segments (0x309e4 : word) = Some W_2686c.
Proof. vm_refl. Qed.
Lemma D_2686c : decode_any W_2686c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26870 : bv 32 := 0xd20706e3.
Lemma F_26870 : fetch_word Ubsan.M.loaded_segments (0x309e8 : word) = Some W_26870.
Proof. vm_refl. Qed.
Lemma D_26870 : decode_any W_26870 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26874 : bv 32 := 0x0005c703.
Lemma F_26874 : fetch_word Ubsan.M.loaded_segments (0x309ec : word) = Some W_26874.
Proof. vm_refl. Qed.
Lemma D_26874 : decode_any W_26874 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26878 : bv 32 := 0x0015c783.
Lemma F_26878 : fetch_word Ubsan.M.loaded_segments (0x309f0 : word) = Some W_26878.
Proof. vm_refl. Qed.
Lemma D_26878 : decode_any W_26878 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2687c : bv 32 := 0x0025c803.
Lemma F_2687c : fetch_word Ubsan.M.loaded_segments (0x309f4 : word) = Some W_2687c.
Proof. vm_refl. Qed.
Lemma D_2687c : decode_any W_2687c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26880 : bv 32 := 0x0035c883.
Lemma F_26880 : fetch_word Ubsan.M.loaded_segments (0x309f8 : word) = Some W_26880.
Proof. vm_refl. Qed.
Lemma D_26880 : decode_any W_26880 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26884 : bv 32 := 0x0045c283.
Lemma F_26884 : fetch_word Ubsan.M.loaded_segments (0x309fc : word) = Some W_26884.
Proof. vm_refl. Qed.
Lemma D_26884 : decode_any W_26884 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26888 : bv 32 := 0x0055c303.
Lemma F_26888 : fetch_word Ubsan.M.loaded_segments (0x30a00 : word) = Some W_26888.
Proof. vm_refl. Qed.
Lemma D_26888 : decode_any W_26888 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2688c : bv 32 := 0x0065c383.
Lemma F_2688c : fetch_word Ubsan.M.loaded_segments (0x30a04 : word) = Some W_2688c.
Proof. vm_refl. Qed.
Lemma D_2688c : decode_any W_2688c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26890 : bv 32 := 0x0075ce03.
Lemma F_26890 : fetch_word Ubsan.M.loaded_segments (0x30a08 : word) = Some W_26890.
Proof. vm_refl. Qed.
Lemma D_26890 : decode_any W_26890 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26894 : bv 32 := 0x00858593.
Lemma F_26894 : fetch_word Ubsan.M.loaded_segments (0x30a0c : word) = Some W_26894.
Proof. vm_refl. Qed.
Lemma D_26894 : decode_any W_26894 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26898 : bv 32 := 0x00e68023.
Lemma F_26898 : fetch_word Ubsan.M.loaded_segments (0x30a10 : word) = Some W_26898.
Proof. vm_refl. Qed.
Lemma D_26898 : decode_any W_26898 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2689c : bv 32 := 0x00f680a3.
Lemma F_2689c : fetch_word Ubsan.M.loaded_segments (0x30a14 : word) = Some W_2689c.
Proof. vm_refl. Qed.
Lemma D_2689c : decode_any W_2689c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268a0 : bv 32 := 0x01068123.
Lemma F_268a0 : fetch_word Ubsan.M.loaded_segments (0x30a18 : word) = Some W_268a0.
Proof. vm_refl. Qed.
Lemma D_268a0 : decode_any W_268a0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268a4 : bv 32 := 0x011681a3.
Lemma F_268a4 : fetch_word Ubsan.M.loaded_segments (0x30a1c : word) = Some W_268a4.
Proof. vm_refl. Qed.
Lemma D_268a4 : decode_any W_268a4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268a8 : bv 32 := 0x00868713.
Lemma F_268a8 : fetch_word Ubsan.M.loaded_segments (0x30a20 : word) = Some W_268a8.
Proof. vm_refl. Qed.
Lemma D_268a8 : decode_any W_268a8 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268ac : bv 32 := 0x00568223.
Lemma F_268ac : fetch_word Ubsan.M.loaded_segments (0x30a24 : word) = Some W_268ac.
Proof. vm_refl. Qed.
Lemma D_268ac : decode_any W_268ac = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268b0 : bv 32 := 0x006682a3.
Lemma F_268b0 : fetch_word Ubsan.M.loaded_segments (0x30a28 : word) = Some W_268b0.
Proof. vm_refl. Qed.
Lemma D_268b0 : decode_any W_268b0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268b4 : bv 32 := 0x00768323.
Lemma F_268b4 : fetch_word Ubsan.M.loaded_segments (0x30a2c : word) = Some W_268b4.
Proof. vm_refl. Qed.
Lemma D_268b4 : decode_any W_268b4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268b8 : bv 32 := 0x01c683a3.
Lemma F_268b8 : fetch_word Ubsan.M.loaded_segments (0x30a30 : word) = Some W_268b8.
Proof. vm_refl. Qed.
Lemma D_268b8 : decode_any W_268b8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268bc : bv 32 := 0x00070693.
Lemma F_268bc : fetch_word Ubsan.M.loaded_segments (0x30a34 : word) = Some W_268bc.
Proof. vm_refl. Qed.
Lemma D_268bc : decode_any W_268bc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268c0 : bv 32 := 0x00467713.
Lemma F_268c0 : fetch_word Ubsan.M.loaded_segments (0x30a38 : word) = Some W_268c0.
Proof. vm_refl. Qed.
Lemma D_268c0 : decode_any W_268c0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268c4 : bv 32 := 0x02070863.
Lemma F_268c4 : fetch_word Ubsan.M.loaded_segments (0x30a3c : word) = Some W_268c4.
Proof. vm_refl. Qed.
Lemma D_268c4 : decode_any W_268c4 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268c8 : bv 32 := 0x0005c703.
Lemma F_268c8 : fetch_word Ubsan.M.loaded_segments (0x30a40 : word) = Some W_268c8.
Proof. vm_refl. Qed.
Lemma D_268c8 : decode_any W_268c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268cc : bv 32 := 0x0015c783.
Lemma F_268cc : fetch_word Ubsan.M.loaded_segments (0x30a44 : word) = Some W_268cc.
Proof. vm_refl. Qed.
Lemma D_268cc : decode_any W_268cc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268d0 : bv 32 := 0x0025c803.
Lemma F_268d0 : fetch_word Ubsan.M.loaded_segments (0x30a48 : word) = Some W_268d0.
Proof. vm_refl. Qed.
Lemma D_268d0 : decode_any W_268d0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268d4 : bv 32 := 0x0035c883.
Lemma F_268d4 : fetch_word Ubsan.M.loaded_segments (0x30a4c : word) = Some W_268d4.
Proof. vm_refl. Qed.
Lemma D_268d4 : decode_any W_268d4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268d8 : bv 32 := 0x00458593.
Lemma F_268d8 : fetch_word Ubsan.M.loaded_segments (0x30a50 : word) = Some W_268d8.
Proof. vm_refl. Qed.
Lemma D_268d8 : decode_any W_268d8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268dc : bv 32 := 0x00468293.
Lemma F_268dc : fetch_word Ubsan.M.loaded_segments (0x30a54 : word) = Some W_268dc.
Proof. vm_refl. Qed.
Lemma D_268dc : decode_any W_268dc = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268e0 : bv 32 := 0x00e68023.
Lemma F_268e0 : fetch_word Ubsan.M.loaded_segments (0x30a58 : word) = Some W_268e0.
Proof. vm_refl. Qed.
Lemma D_268e0 : decode_any W_268e0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268e4 : bv 32 := 0x00f680a3.
Lemma F_268e4 : fetch_word Ubsan.M.loaded_segments (0x30a5c : word) = Some W_268e4.
Proof. vm_refl. Qed.
Lemma D_268e4 : decode_any W_268e4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268e8 : bv 32 := 0x01068123.
Lemma F_268e8 : fetch_word Ubsan.M.loaded_segments (0x30a60 : word) = Some W_268e8.
Proof. vm_refl. Qed.
Lemma D_268e8 : decode_any W_268e8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268ec : bv 32 := 0x011681a3.
Lemma F_268ec : fetch_word Ubsan.M.loaded_segments (0x30a64 : word) = Some W_268ec.
Proof. vm_refl. Qed.
Lemma D_268ec : decode_any W_268ec = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268f0 : bv 32 := 0x00028693.
Lemma F_268f0 : fetch_word Ubsan.M.loaded_segments (0x30a68 : word) = Some W_268f0.
Proof. vm_refl. Qed.
Lemma D_268f0 : decode_any W_268f0 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268f4 : bv 32 := 0x00267713.
Lemma F_268f4 : fetch_word Ubsan.M.loaded_segments (0x30a6c : word) = Some W_268f4.
Proof. vm_refl. Qed.
Lemma D_268f4 : decode_any W_268f4 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268f8 : bv 32 := 0x00071863.
Lemma F_268f8 : fetch_word Ubsan.M.loaded_segments (0x30a70 : word) = Some W_268f8.
Proof. vm_refl. Qed.
Lemma D_268f8 : decode_any W_268f8 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_268fc : bv 32 := 0x00167613.
Lemma F_268fc : fetch_word Ubsan.M.loaded_segments (0x30a74 : word) = Some W_268fc.
Proof. vm_refl. Qed.
Lemma D_268fc : decode_any W_268fc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26900 : bv 32 := 0x02061663.
Lemma F_26900 : fetch_word Ubsan.M.loaded_segments (0x30a78 : word) = Some W_26900.
Proof. vm_refl. Qed.
Lemma D_26900 : decode_any W_26900 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26904 : bv 32 := 0x00008067.
Lemma F_26904 : fetch_word Ubsan.M.loaded_segments (0x30a7c : word) = Some W_26904.
Proof. vm_refl. Qed.
Lemma D_26904 : decode_any W_26904 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26908 : bv 32 := 0x0005c703.
Lemma F_26908 : fetch_word Ubsan.M.loaded_segments (0x30a80 : word) = Some W_26908.
Proof. vm_refl. Qed.
Lemma D_26908 : decode_any W_26908 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2690c : bv 32 := 0x0015c783.
Lemma F_2690c : fetch_word Ubsan.M.loaded_segments (0x30a84 : word) = Some W_2690c.
Proof. vm_refl. Qed.
Lemma D_2690c : decode_any W_2690c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26910 : bv 32 := 0x00258593.
Lemma F_26910 : fetch_word Ubsan.M.loaded_segments (0x30a88 : word) = Some W_26910.
Proof. vm_refl. Qed.
Lemma D_26910 : decode_any W_26910 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26914 : bv 32 := 0x00268813.
Lemma F_26914 : fetch_word Ubsan.M.loaded_segments (0x30a8c : word) = Some W_26914.
Proof. vm_refl. Qed.
Lemma D_26914 : decode_any W_26914 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26918 : bv 32 := 0x00e68023.
Lemma F_26918 : fetch_word Ubsan.M.loaded_segments (0x30a90 : word) = Some W_26918.
Proof. vm_refl. Qed.
Lemma D_26918 : decode_any W_26918 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2691c : bv 32 := 0x00f680a3.
Lemma F_2691c : fetch_word Ubsan.M.loaded_segments (0x30a94 : word) = Some W_2691c.
Proof. vm_refl. Qed.
Lemma D_2691c : decode_any W_2691c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26920 : bv 32 := 0x00080693.
Lemma F_26920 : fetch_word Ubsan.M.loaded_segments (0x30a98 : word) = Some W_26920.
Proof. vm_refl. Qed.
Lemma D_26920 : decode_any W_26920 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26924 : bv 32 := 0x00167613.
Lemma F_26924 : fetch_word Ubsan.M.loaded_segments (0x30a9c : word) = Some W_26924.
Proof. vm_refl. Qed.
Lemma D_26924 : decode_any W_26924 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26928 : bv 32 := 0xfc060ee3.
Lemma F_26928 : fetch_word Ubsan.M.loaded_segments (0x30aa0 : word) = Some W_26928.
Proof. vm_refl. Qed.
Lemma D_26928 : decode_any W_26928 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2692c : bv 32 := 0x0005c583.
Lemma F_2692c : fetch_word Ubsan.M.loaded_segments (0x30aa4 : word) = Some W_2692c.
Proof. vm_refl. Qed.
Lemma D_2692c : decode_any W_2692c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26930 : bv 32 := 0x00b68023.
Lemma F_26930 : fetch_word Ubsan.M.loaded_segments (0x30aa8 : word) = Some W_26930.
Proof. vm_refl. Qed.
Lemma D_26930 : decode_any W_26930 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26934 : bv 32 := 0x00008067.
Lemma F_26934 : fetch_word Ubsan.M.loaded_segments (0x30aac : word) = Some W_26934.
Proof. vm_refl. Qed.
Lemma D_26934 : decode_any W_26934 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26938 : bv 32 := 0x0e060a63.
Lemma F_26938 : fetch_word Ubsan.M.loaded_segments (0x30ab0 : word) = Some W_26938.
Proof. vm_refl. Qed.
Lemma D_26938 : decode_any W_26938 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2693c : bv 32 := 0x00b50023.
Lemma F_2693c : fetch_word Ubsan.M.loaded_segments (0x30ab4 : word) = Some W_2693c.
Proof. vm_refl. Qed.
Lemma D_2693c : decode_any W_2693c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26940 : bv 32 := 0x00c506b3.
Lemma F_26940 : fetch_word Ubsan.M.loaded_segments (0x30ab8 : word) = Some W_26940.
Proof. vm_refl. Qed.
Lemma D_26940 : decode_any W_26940 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26944 : bv 32 := 0x00300713.
Lemma F_26944 : fetch_word Ubsan.M.loaded_segments (0x30abc : word) = Some W_26944.
Proof. vm_refl. Qed.
Lemma D_26944 : decode_any W_26944 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26948 : bv 32 := 0xfeb68fa3.
Lemma F_26948 : fetch_word Ubsan.M.loaded_segments (0x30ac0 : word) = Some W_26948.
Proof. vm_refl. Qed.
Lemma D_26948 : decode_any W_26948 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2694c : bv 32 := 0x0ee66063.
Lemma F_2694c : fetch_word Ubsan.M.loaded_segments (0x30ac4 : word) = Some W_2694c.
Proof. vm_refl. Qed.
Lemma D_2694c : decode_any W_2694c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26950 : bv 32 := 0x00b500a3.
Lemma F_26950 : fetch_word Ubsan.M.loaded_segments (0x30ac8 : word) = Some W_26950.
Proof. vm_refl. Qed.
Lemma D_26950 : decode_any W_26950 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26954 : bv 32 := 0x00b50123.
Lemma F_26954 : fetch_word Ubsan.M.loaded_segments (0x30acc : word) = Some W_26954.
Proof. vm_refl. Qed.
Lemma D_26954 : decode_any W_26954 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26958 : bv 32 := 0x00700713.
Lemma F_26958 : fetch_word Ubsan.M.loaded_segments (0x30ad0 : word) = Some W_26958.
Proof. vm_refl. Qed.
Lemma D_26958 : decode_any W_26958 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2695c : bv 32 := 0xfeb68ea3.
Lemma F_2695c : fetch_word Ubsan.M.loaded_segments (0x30ad4 : word) = Some W_2695c.
Proof. vm_refl. Qed.
Lemma D_2695c : decode_any W_2695c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26960 : bv 32 := 0xfeb68f23.
Lemma F_26960 : fetch_word Ubsan.M.loaded_segments (0x30ad8 : word) = Some W_26960.
Proof. vm_refl. Qed.
Lemma D_26960 : decode_any W_26960 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26964 : bv 32 := 0x0ce66463.
Lemma F_26964 : fetch_word Ubsan.M.loaded_segments (0x30adc : word) = Some W_26964.
Proof. vm_refl. Qed.
Lemma D_26964 : decode_any W_26964 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26968 : bv 32 := 0x00b501a3.
Lemma F_26968 : fetch_word Ubsan.M.loaded_segments (0x30ae0 : word) = Some W_26968.
Proof. vm_refl. Qed.
Lemma D_26968 : decode_any W_26968 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2696c : bv 32 := 0x00900793.
Lemma F_2696c : fetch_word Ubsan.M.loaded_segments (0x30ae4 : word) = Some W_2696c.
Proof. vm_refl. Qed.
Lemma D_2696c : decode_any W_2696c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26970 : bv 32 := 0xfeb68e23.
Lemma F_26970 : fetch_word Ubsan.M.loaded_segments (0x30ae8 : word) = Some W_26970.
Proof. vm_refl. Qed.
Lemma D_26970 : decode_any W_26970 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26974 : bv 32 := 0x0af66c63.
Lemma F_26974 : fetch_word Ubsan.M.loaded_segments (0x30aec : word) = Some W_26974.
Proof. vm_refl. Qed.
Lemma D_26974 : decode_any W_26974 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26978 : bv 32 := 0x40a006bb.
Lemma F_26978 : fetch_word Ubsan.M.loaded_segments (0x30af0 : word) = Some W_26978.
Proof. vm_refl. Qed.
Lemma D_26978 : decode_any W_26978 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2697c : bv 32 := 0x03859813.
Lemma F_2697c : fetch_word Ubsan.M.loaded_segments (0x30af4 : word) = Some W_2697c.
Proof. vm_refl. Qed.
Lemma D_2697c : decode_any W_2697c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26980 : bv 32 := 0x101015b7.
Lemma F_26980 : fetch_word Ubsan.M.loaded_segments (0x30af8 : word) = Some W_26980.
Proof. vm_refl. Qed.
Lemma D_26980 : decode_any W_26980 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26984 : bv 32 := 0x0036f693.
Lemma F_26984 : fetch_word Ubsan.M.loaded_segments (0x30afc : word) = Some W_26984.
Proof. vm_refl. Qed.
Lemma D_26984 : decode_any W_26984 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26988 : bv 32 := 0x00459713.
Lemma F_26988 : fetch_word Ubsan.M.loaded_segments (0x30b00 : word) = Some W_26988.
Proof. vm_refl. Qed.
Lemma D_26988 : decode_any W_26988 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2698c : bv 32 := 0x40d60633.
Lemma F_2698c : fetch_word Ubsan.M.loaded_segments (0x30b04 : word) = Some W_2698c.
Proof. vm_refl. Qed.
Lemma D_2698c : decode_any W_2698c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26990 : bv 32 := 0x00d505b3.
Lemma F_26990 : fetch_word Ubsan.M.loaded_segments (0x30b08 : word) = Some W_26990.
Proof. vm_refl. Qed.
Lemma D_26990 : decode_any W_26990 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26994 : bv 32 := 0x10070693.
Lemma F_26994 : fetch_word Ubsan.M.loaded_segments (0x30b0c : word) = Some W_26994.
Proof. vm_refl. Qed.
Lemma D_26994 : decode_any W_26994 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26998 : bv 32 := 0xffc67713.
Lemma F_26998 : fetch_word Ubsan.M.loaded_segments (0x30b10 : word) = Some W_26998.
Proof. vm_refl. Qed.
Lemma D_26998 : decode_any W_26998 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2699c : bv 32 := 0x02d83633.
Lemma F_2699c : fetch_word Ubsan.M.loaded_segments (0x30b14 : word) = Some W_2699c.
Proof. vm_refl. Qed.
Lemma D_2699c : decode_any W_2699c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269a0 : bv 32 := 0x00c5a023.
Lemma F_269a0 : fetch_word Ubsan.M.loaded_segments (0x30b18 : word) = Some W_269a0.
Proof. vm_refl. Qed.
Lemma D_269a0 : decode_any W_269a0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269a4 : bv 32 := 0x00e586b3.
Lemma F_269a4 : fetch_word Ubsan.M.loaded_segments (0x30b1c : word) = Some W_269a4.
Proof. vm_refl. Qed.
Lemma D_269a4 : decode_any W_269a4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269a8 : bv 32 := 0xfec6ae23.
Lemma F_269a8 : fetch_word Ubsan.M.loaded_segments (0x30b20 : word) = Some W_269a8.
Proof. vm_refl. Qed.
Lemma D_269a8 : decode_any W_269a8 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269ac : bv 32 := 0x08f76063.
Lemma F_269ac : fetch_word Ubsan.M.loaded_segments (0x30b24 : word) = Some W_269ac.
Proof. vm_refl. Qed.
Lemma D_269ac : decode_any W_269ac = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269b0 : bv 32 := 0x00c5a223.
Lemma F_269b0 : fetch_word Ubsan.M.loaded_segments (0x30b28 : word) = Some W_269b0.
Proof. vm_refl. Qed.
Lemma D_269b0 : decode_any W_269b0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269b4 : bv 32 := 0x00c5a423.
Lemma F_269b4 : fetch_word Ubsan.M.loaded_segments (0x30b2c : word) = Some W_269b4.
Proof. vm_refl. Qed.
Lemma D_269b4 : decode_any W_269b4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269b8 : bv 32 := 0x01900793.
Lemma F_269b8 : fetch_word Ubsan.M.loaded_segments (0x30b30 : word) = Some W_269b8.
Proof. vm_refl. Qed.
Lemma D_269b8 : decode_any W_269b8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269bc : bv 32 := 0xfec6aa23.
Lemma F_269bc : fetch_word Ubsan.M.loaded_segments (0x30b34 : word) = Some W_269bc.
Proof. vm_refl. Qed.
Lemma D_269bc : decode_any W_269bc = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269c0 : bv 32 := 0xfec6ac23.
Lemma F_269c0 : fetch_word Ubsan.M.loaded_segments (0x30b38 : word) = Some W_269c0.
Proof. vm_refl. Qed.
Lemma D_269c0 : decode_any W_269c0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269c4 : bv 32 := 0x06f76463.
Lemma F_269c4 : fetch_word Ubsan.M.loaded_segments (0x30b3c : word) = Some W_269c4.
Proof. vm_refl. Qed.
Lemma D_269c4 : decode_any W_269c4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269c8 : bv 32 := 0x00c5a623.
Lemma F_269c8 : fetch_word Ubsan.M.loaded_segments (0x30b40 : word) = Some W_269c8.
Proof. vm_refl. Qed.
Lemma D_269c8 : decode_any W_269c8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269cc : bv 32 := 0x00c5a823.
Lemma F_269cc : fetch_word Ubsan.M.loaded_segments (0x30b44 : word) = Some W_269cc.
Proof. vm_refl. Qed.
Lemma D_269cc : decode_any W_269cc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269d0 : bv 32 := 0x00c5aa23.
Lemma F_269d0 : fetch_word Ubsan.M.loaded_segments (0x30b48 : word) = Some W_269d0.
Proof. vm_refl. Qed.
Lemma D_269d0 : decode_any W_269d0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269d4 : bv 32 := 0x00c5ac23.
Lemma F_269d4 : fetch_word Ubsan.M.loaded_segments (0x30b4c : word) = Some W_269d4.
Proof. vm_refl. Qed.
Lemma D_269d4 : decode_any W_269d4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269d8 : bv 32 := 0x0045f793.
Lemma F_269d8 : fetch_word Ubsan.M.loaded_segments (0x30b50 : word) = Some W_269d8.
Proof. vm_refl. Qed.
Lemma D_269d8 : decode_any W_269d8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269dc : bv 32 := 0x02000813.
Lemma F_269dc : fetch_word Ubsan.M.loaded_segments (0x30b54 : word) = Some W_269dc.
Proof. vm_refl. Qed.
Lemma D_269dc : decode_any W_269dc = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269e0 : bv 32 := 0x01878793.
Lemma F_269e0 : fetch_word Ubsan.M.loaded_segments (0x30b58 : word) = Some W_269e0.
Proof. vm_refl. Qed.
Lemma D_269e0 : decode_any W_269e0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269e4 : bv 32 := 0x40f70733.
Lemma F_269e4 : fetch_word Ubsan.M.loaded_segments (0x30b5c : word) = Some W_269e4.
Proof. vm_refl. Qed.
Lemma D_269e4 : decode_any W_269e4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269e8 : bv 32 := 0xfec6a223.
Lemma F_269e8 : fetch_word Ubsan.M.loaded_segments (0x30b60 : word) = Some W_269e8.
Proof. vm_refl. Qed.
Lemma D_269e8 : decode_any W_269e8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269ec : bv 32 := 0xfec6a423.
Lemma F_269ec : fetch_word Ubsan.M.loaded_segments (0x30b64 : word) = Some W_269ec.
Proof. vm_refl. Qed.
Lemma D_269ec : decode_any W_269ec = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269f0 : bv 32 := 0xfec6a623.
Lemma F_269f0 : fetch_word Ubsan.M.loaded_segments (0x30b68 : word) = Some W_269f0.
Proof. vm_refl. Qed.
Lemma D_269f0 : decode_any W_269f0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269f4 : bv 32 := 0xfec6a823.
Lemma F_269f4 : fetch_word Ubsan.M.loaded_segments (0x30b6c : word) = Some W_269f4.
Proof. vm_refl. Qed.
Lemma D_269f4 : decode_any W_269f4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269f8 : bv 32 := 0x03076a63.
Lemma F_269f8 : fetch_word Ubsan.M.loaded_segments (0x30b70 : word) = Some W_269f8.
Proof. vm_refl. Qed.
Lemma D_269f8 : decode_any W_269f8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_269fc : bv 32 := 0x02061613.
Lemma F_269fc : fetch_word Ubsan.M.loaded_segments (0x30b74 : word) = Some W_269fc.
Proof. vm_refl. Qed.
Lemma D_269fc : decode_any W_269fc = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a00 : bv 32 := 0x00f585b3.
Lemma F_26a00 : fetch_word Ubsan.M.loaded_segments (0x30b78 : word) = Some W_26a00.
Proof. vm_refl. Qed.
Lemma D_26a00 : decode_any W_26a00 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a04 : bv 32 := 0x02065693.
Lemma F_26a04 : fetch_word Ubsan.M.loaded_segments (0x30b7c : word) = Some W_26a04.
Proof. vm_refl. Qed.
Lemma D_26a04 : decode_any W_26a04 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a08 : bv 32 := 0x00d66633.
Lemma F_26a08 : fetch_word Ubsan.M.loaded_segments (0x30b80 : word) = Some W_26a08.
Proof. vm_refl. Qed.
Lemma D_26a08 : decode_any W_26a08 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a0c : bv 32 := 0x01f00693.
Lemma F_26a0c : fetch_word Ubsan.M.loaded_segments (0x30b84 : word) = Some W_26a0c.
Proof. vm_refl. Qed.
Lemma D_26a0c : decode_any W_26a0c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a10 : bv 32 := 0x00c5b023.
Lemma F_26a10 : fetch_word Ubsan.M.loaded_segments (0x30b88 : word) = Some W_26a10.
Proof. vm_refl. Qed.
Lemma D_26a10 : decode_any W_26a10 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a14 : bv 32 := 0x00c5b423.
Lemma F_26a14 : fetch_word Ubsan.M.loaded_segments (0x30b8c : word) = Some W_26a14.
Proof. vm_refl. Qed.
Lemma D_26a14 : decode_any W_26a14 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a18 : bv 32 := 0x00c5b823.
Lemma F_26a18 : fetch_word Ubsan.M.loaded_segments (0x30b90 : word) = Some W_26a18.
Proof. vm_refl. Qed.
Lemma D_26a18 : decode_any W_26a18 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a1c : bv 32 := 0x00c5bc23.
Lemma F_26a1c : fetch_word Ubsan.M.loaded_segments (0x30b94 : word) = Some W_26a1c.
Proof. vm_refl. Qed.
Lemma D_26a1c : decode_any W_26a1c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a20 : bv 32 := 0xfe070713.
Lemma F_26a20 : fetch_word Ubsan.M.loaded_segments (0x30b98 : word) = Some W_26a20.
Proof. vm_refl. Qed.
Lemma D_26a20 : decode_any W_26a20 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a24 : bv 32 := 0x02058593.
Lemma F_26a24 : fetch_word Ubsan.M.loaded_segments (0x30b9c : word) = Some W_26a24.
Proof. vm_refl. Qed.
Lemma D_26a24 : decode_any W_26a24 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a28 : bv 32 := 0xfee6e4e3.
Lemma F_26a28 : fetch_word Ubsan.M.loaded_segments (0x30ba0 : word) = Some W_26a28.
Proof. vm_refl. Qed.
Lemma D_26a28 : decode_any W_26a28 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a2c : bv 32 := 0x00008067.
Lemma F_26a2c : fetch_word Ubsan.M.loaded_segments (0x30ba4 : word) = Some W_26a2c.
Proof. vm_refl. Qed.
Lemma D_26a2c : decode_any W_26a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a30 : bv 32 := 0xfe010113.
Lemma F_26a30 : fetch_word Ubsan.M.loaded_segments (0x30ba8 : word) = Some W_26a30.
Proof. vm_refl. Qed.
Lemma D_26a30 : decode_any W_26a30 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a34 : bv 32 := 0x00113c23.
Lemma F_26a34 : fetch_word Ubsan.M.loaded_segments (0x30bac : word) = Some W_26a34.
Proof. vm_refl. Qed.
Lemma D_26a34 : decode_any W_26a34 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a38 : bv 32 := 0x00813823.
Lemma F_26a38 : fetch_word Ubsan.M.loaded_segments (0x30bb0 : word) = Some W_26a38.
Proof. vm_refl. Qed.
Lemma D_26a38 : decode_any W_26a38 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a3c : bv 32 := 0x00913423.
Lemma F_26a3c : fetch_word Ubsan.M.loaded_segments (0x30bb4 : word) = Some W_26a3c.
Proof. vm_refl. Qed.
Lemma D_26a3c : decode_any W_26a3c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a40 : bv 32 := 0x00058413.
Lemma F_26a40 : fetch_word Ubsan.M.loaded_segments (0x30bb8 : word) = Some W_26a40.
Proof. vm_refl. Qed.
Lemma D_26a40 : decode_any W_26a40 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a44 : bv 32 := 0x00050493.
Lemma F_26a44 : fetch_word Ubsan.M.loaded_segments (0x30bbc : word) = Some W_26a44.
Proof. vm_refl. Qed.
Lemma D_26a44 : decode_any W_26a44 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a48 : bv 32 := 0x00000593.
Lemma F_26a48 : fetch_word Ubsan.M.loaded_segments (0x30bc0 : word) = Some W_26a48.
Proof. vm_refl. Qed.
Lemma D_26a48 : decode_any W_26a48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a4c : bv 32 := 0x00040613.
Lemma F_26a4c : fetch_word Ubsan.M.loaded_segments (0x30bc4 : word) = Some W_26a4c.
Proof. vm_refl. Qed.
Lemma D_26a4c : decode_any W_26a4c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a50 : bv 32 := 0x024000ef.
Lemma F_26a50 : fetch_word Ubsan.M.loaded_segments (0x30bc8 : word) = Some W_26a50.
Proof. vm_refl. Qed.
Lemma D_26a50 : decode_any W_26a50 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a54 : bv 32 := 0x00050463.
Lemma F_26a54 : fetch_word Ubsan.M.loaded_segments (0x30bcc : word) = Some W_26a54.
Proof. vm_refl. Qed.
Lemma D_26a54 : decode_any W_26a54 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a58 : bv 32 := 0x40950433.
Lemma F_26a58 : fetch_word Ubsan.M.loaded_segments (0x30bd0 : word) = Some W_26a58.
Proof. vm_refl. Qed.
Lemma D_26a58 : decode_any W_26a58 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a5c : bv 32 := 0x00040513.
Lemma F_26a5c : fetch_word Ubsan.M.loaded_segments (0x30bd4 : word) = Some W_26a5c.
Proof. vm_refl. Qed.
Lemma D_26a5c : decode_any W_26a5c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a60 : bv 32 := 0x01813083.
Lemma F_26a60 : fetch_word Ubsan.M.loaded_segments (0x30bd8 : word) = Some W_26a60.
Proof. vm_refl. Qed.
Lemma D_26a60 : decode_any W_26a60 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a64 : bv 32 := 0x01013403.
Lemma F_26a64 : fetch_word Ubsan.M.loaded_segments (0x30bdc : word) = Some W_26a64.
Proof. vm_refl. Qed.
Lemma D_26a64 : decode_any W_26a64 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a68 : bv 32 := 0x00813483.
Lemma F_26a68 : fetch_word Ubsan.M.loaded_segments (0x30be0 : word) = Some W_26a68.
Proof. vm_refl. Qed.
Lemma D_26a68 : decode_any W_26a68 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a6c : bv 32 := 0x02010113.
Lemma F_26a6c : fetch_word Ubsan.M.loaded_segments (0x30be4 : word) = Some W_26a6c.
Proof. vm_refl. Qed.
Lemma D_26a6c : decode_any W_26a6c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a70 : bv 32 := 0x00008067.
Lemma F_26a70 : fetch_word Ubsan.M.loaded_segments (0x30be8 : word) = Some W_26a70.
Proof. vm_refl. Qed.
Lemma D_26a70 : decode_any W_26a70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a74 : bv 32 := 0x0ff5f593.
Lemma F_26a74 : fetch_word Ubsan.M.loaded_segments (0x30bec : word) = Some W_26a74.
Proof. vm_refl. Qed.
Lemma D_26a74 : decode_any W_26a74 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a78 : bv 32 := 0x00757693.
Lemma F_26a78 : fetch_word Ubsan.M.loaded_segments (0x30bf0 : word) = Some W_26a78.
Proof. vm_refl. Qed.
Lemma D_26a78 : decode_any W_26a78 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a7c : bv 32 := 0x00c03733.
Lemma F_26a7c : fetch_word Ubsan.M.loaded_segments (0x30bf4 : word) = Some W_26a7c.
Proof. vm_refl. Qed.
Lemma D_26a7c : decode_any W_26a7c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a80 : bv 32 := 0x02068c63.
Lemma F_26a80 : fetch_word Ubsan.M.loaded_segments (0x30bf8 : word) = Some W_26a80.
Proof. vm_refl. Qed.
Lemma D_26a80 : decode_any W_26a80 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a84 : bv 32 := 0x02060a63.
Lemma F_26a84 : fetch_word Ubsan.M.loaded_segments (0x30bfc : word) = Some W_26a84.
Proof. vm_refl. Qed.
Lemma D_26a84 : decode_any W_26a84 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a88 : bv 32 := 0x00150793.
Lemma F_26a88 : fetch_word Ubsan.M.loaded_segments (0x30c00 : word) = Some W_26a88.
Proof. vm_refl. Qed.
Lemma D_26a88 : decode_any W_26a88 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a8c : bv 32 := 0x00100813.
Lemma F_26a8c : fetch_word Ubsan.M.loaded_segments (0x30c04 : word) = Some W_26a8c.
Proof. vm_refl. Qed.
Lemma D_26a8c : decode_any W_26a8c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a90 : bv 32 := 0x00054703.
Lemma F_26a90 : fetch_word Ubsan.M.loaded_segments (0x30c08 : word) = Some W_26a90.
Proof. vm_refl. Qed.
Lemma D_26a90 : decode_any W_26a90 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a94 : bv 32 := 0x00060693.
Lemma F_26a94 : fetch_word Ubsan.M.loaded_segments (0x30c0c : word) = Some W_26a94.
Proof. vm_refl. Qed.
Lemma D_26a94 : decode_any W_26a94 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a98 : bv 32 := 0x06b70e63.
Lemma F_26a98 : fetch_word Ubsan.M.loaded_segments (0x30c10 : word) = Some W_26a98.
Proof. vm_refl. Qed.
Lemma D_26a98 : decode_any W_26a98 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26a9c : bv 32 := 0x00150513.
Lemma F_26a9c : fetch_word Ubsan.M.loaded_segments (0x30c14 : word) = Some W_26a9c.
Proof. vm_refl. Qed.
Lemma D_26a9c : decode_any W_26a9c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26aa0 : bv 32 := 0xfff68613.
Lemma F_26aa0 : fetch_word Ubsan.M.loaded_segments (0x30c18 : word) = Some W_26aa0.
Proof. vm_refl. Qed.
Lemma D_26aa0 : decode_any W_26aa0 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26aa4 : bv 32 := 0x0077f893.
Lemma F_26aa4 : fetch_word Ubsan.M.loaded_segments (0x30c1c : word) = Some W_26aa4.
Proof. vm_refl. Qed.
Lemma D_26aa4 : decode_any W_26aa4 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26aa8 : bv 32 := 0x00c03733.
Lemma F_26aa8 : fetch_word Ubsan.M.loaded_segments (0x30c20 : word) = Some W_26aa8.
Proof. vm_refl. Qed.
Lemma D_26aa8 : decode_any W_26aa8 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26aac : bv 32 := 0x00088663.
Lemma F_26aac : fetch_word Ubsan.M.loaded_segments (0x30c24 : word) = Some W_26aac.
Proof. vm_refl. Qed.
Lemma D_26aac : decode_any W_26aac = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ab0 : bv 32 := 0x00178793.
Lemma F_26ab0 : fetch_word Ubsan.M.loaded_segments (0x30c28 : word) = Some W_26ab0.
Proof. vm_refl. Qed.
Lemma D_26ab0 : decode_any W_26ab0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ab4 : bv 32 := 0xfd069ee3.
Lemma F_26ab4 : fetch_word Ubsan.M.loaded_segments (0x30c2c : word) = Some W_26ab4.
Proof. vm_refl. Qed.
Lemma D_26ab4 : decode_any W_26ab4 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ab8 : bv 32 := 0x06070863.
Lemma F_26ab8 : fetch_word Ubsan.M.loaded_segments (0x30c30 : word) = Some W_26ab8.
Proof. vm_refl. Qed.
Lemma D_26ab8 : decode_any W_26ab8 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26abc : bv 32 := 0x00054683.
Lemma F_26abc : fetch_word Ubsan.M.loaded_segments (0x30c34 : word) = Some W_26abc.
Proof. vm_refl. Qed.
Lemma D_26abc : decode_any W_26abc = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ac0 : bv 32 := 0x04b68663.
Lemma F_26ac0 : fetch_word Ubsan.M.loaded_segments (0x30c38 : word) = Some W_26ac0.
Proof. vm_refl. Qed.
Lemma D_26ac0 : decode_any W_26ac0 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ac4 : bv 32 := 0x00800693.
Lemma F_26ac4 : fetch_word Ubsan.M.loaded_segments (0x30c3c : word) = Some W_26ac4.
Proof. vm_refl. Qed.
Lemma D_26ac4 : decode_any W_26ac4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ac8 : bv 32 := 0x04d66263.
Lemma F_26ac8 : fetch_word Ubsan.M.loaded_segments (0x30c40 : word) = Some W_26ac8.
Proof. vm_refl. Qed.
Lemma D_26ac8 : decode_any W_26ac8 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26acc : bv 32 := 0xfffe0697.
Lemma F_26acc : fetch_word Ubsan.M.loaded_segments (0x30c44 : word) = Some W_26acc.
Proof. vm_refl. Qed.
Lemma D_26acc : decode_any W_26acc = Some (Auipc 13 1048544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ad0 : bv 32 := 0x0f46b683.
Lemma F_26ad0 : fetch_word Ubsan.M.loaded_segments (0x30c48 : word) = Some W_26ad0.
Proof. vm_refl. Qed.
Lemma D_26ad0 : decode_any W_26ad0 = Some (Load SZ8 true 13 13 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ad4 : bv 32 := 0xfffe0717.
Lemma F_26ad4 : fetch_word Ubsan.M.loaded_segments (0x30c4c : word) = Some W_26ad4.
Proof. vm_refl. Qed.
Lemma D_26ad4 : decode_any W_26ad4 = Some (Auipc 14 1048544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ad8 : bv 32 := 0x0d473703.
Lemma F_26ad8 : fetch_word Ubsan.M.loaded_segments (0x30c50 : word) = Some W_26ad8.
Proof. vm_refl. Qed.
Lemma D_26ad8 : decode_any W_26ad8 = Some (Load SZ8 true 14 14 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26adc : bv 32 := 0x00168793.
Lemma F_26adc : fetch_word Ubsan.M.loaded_segments (0x30c54 : word) = Some W_26adc.
Proof. vm_refl. Qed.
Lemma D_26adc : decode_any W_26adc = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ae0 : bv 32 := 0x02f587b3.
Lemma F_26ae0 : fetch_word Ubsan.M.loaded_segments (0x30c58 : word) = Some W_26ae0.
Proof. vm_refl. Qed.
Lemma D_26ae0 : decode_any W_26ae0 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ae4 : bv 32 := 0x00700813.
Lemma F_26ae4 : fetch_word Ubsan.M.loaded_segments (0x30c5c : word) = Some W_26ae4.
Proof. vm_refl. Qed.
Lemma D_26ae4 : decode_any W_26ae4 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ae8 : bv 32 := 0x00053883.
Lemma F_26ae8 : fetch_word Ubsan.M.loaded_segments (0x30c60 : word) = Some W_26ae8.
Proof. vm_refl. Qed.
Lemma D_26ae8 : decode_any W_26ae8 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26aec : bv 32 := 0x00f8c8b3.
Lemma F_26aec : fetch_word Ubsan.M.loaded_segments (0x30c64 : word) = Some W_26aec.
Proof. vm_refl. Qed.
Lemma D_26aec : decode_any W_26aec = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26af0 : bv 32 := 0x411682b3.
Lemma F_26af0 : fetch_word Ubsan.M.loaded_segments (0x30c68 : word) = Some W_26af0.
Proof. vm_refl. Qed.
Lemma D_26af0 : decode_any W_26af0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26af4 : bv 32 := 0x0112e8b3.
Lemma F_26af4 : fetch_word Ubsan.M.loaded_segments (0x30c6c : word) = Some W_26af4.
Proof. vm_refl. Qed.
Lemma D_26af4 : decode_any W_26af4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26af8 : bv 32 := 0x00e8f8b3.
Lemma F_26af8 : fetch_word Ubsan.M.loaded_segments (0x30c70 : word) = Some W_26af8.
Proof. vm_refl. Qed.
Lemma D_26af8 : decode_any W_26af8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26afc : bv 32 := 0x02e89a63.
Lemma F_26afc : fetch_word Ubsan.M.loaded_segments (0x30c74 : word) = Some W_26afc.
Proof. vm_refl. Qed.
Lemma D_26afc : decode_any W_26afc = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b00 : bv 32 := 0xff860613.
Lemma F_26b00 : fetch_word Ubsan.M.loaded_segments (0x30c78 : word) = Some W_26b00.
Proof. vm_refl. Qed.
Lemma D_26b00 : decode_any W_26b00 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b04 : bv 32 := 0x00850513.
Lemma F_26b04 : fetch_word Ubsan.M.loaded_segments (0x30c7c : word) = Some W_26b04.
Proof. vm_refl. Qed.
Lemma D_26b04 : decode_any W_26b04 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b08 : bv 32 := 0xfec860e3.
Lemma F_26b08 : fetch_word Ubsan.M.loaded_segments (0x30c80 : word) = Some W_26b08.
Proof. vm_refl. Qed.
Lemma D_26b08 : decode_any W_26b08 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b0c : bv 32 := 0x00060693.
Lemma F_26b0c : fetch_word Ubsan.M.loaded_segments (0x30c84 : word) = Some W_26b0c.
Proof. vm_refl. Qed.
Lemma D_26b0c : decode_any W_26b0c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b10 : bv 32 := 0x00060c63.
Lemma F_26b10 : fetch_word Ubsan.M.loaded_segments (0x30c88 : word) = Some W_26b10.
Proof. vm_refl. Qed.
Lemma D_26b10 : decode_any W_26b10 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b14 : bv 32 := 0x00054603.
Lemma F_26b14 : fetch_word Ubsan.M.loaded_segments (0x30c8c : word) = Some W_26b14.
Proof. vm_refl. Qed.
Lemma D_26b14 : decode_any W_26b14 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b18 : bv 32 := 0x00b60a63.
Lemma F_26b18 : fetch_word Ubsan.M.loaded_segments (0x30c90 : word) = Some W_26b18.
Proof. vm_refl. Qed.
Lemma D_26b18 : decode_any W_26b18 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b1c : bv 32 := 0xfff68693.
Lemma F_26b1c : fetch_word Ubsan.M.loaded_segments (0x30c94 : word) = Some W_26b1c.
Proof. vm_refl. Qed.
Lemma D_26b1c : decode_any W_26b1c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b20 : bv 32 := 0x00150513.
Lemma F_26b20 : fetch_word Ubsan.M.loaded_segments (0x30c98 : word) = Some W_26b20.
Proof. vm_refl. Qed.
Lemma D_26b20 : decode_any W_26b20 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b24 : bv 32 := 0xfe0698e3.
Lemma F_26b24 : fetch_word Ubsan.M.loaded_segments (0x30c9c : word) = Some W_26b24.
Proof. vm_refl. Qed.
Lemma D_26b24 : decode_any W_26b24 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b2c : bv 32 := 0x00008067.
Lemma F_26b2c : fetch_word Ubsan.M.loaded_segments (0x30ca4 : word) = Some W_26b2c.
Proof. vm_refl. Qed.
Lemma D_26b2c : decode_any W_26b2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b30 : bv 32 := 0x00060693.
Lemma F_26b30 : fetch_word Ubsan.M.loaded_segments (0x30ca8 : word) = Some W_26b30.
Proof. vm_refl. Qed.
Lemma D_26b30 : decode_any W_26b30 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b34 : bv 32 := 0x00054603.
Lemma F_26b34 : fetch_word Ubsan.M.loaded_segments (0x30cac : word) = Some W_26b34.
Proof. vm_refl. Qed.
Lemma D_26b34 : decode_any W_26b34 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b38 : bv 32 := 0xfeb612e3.
Lemma F_26b38 : fetch_word Ubsan.M.loaded_segments (0x30cb0 : word) = Some W_26b38.
Proof. vm_refl. Qed.
Lemma D_26b38 : decode_any W_26b38 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b3c : bv 32 := 0xff1ff06f.
Lemma F_26b3c : fetch_word Ubsan.M.loaded_segments (0x30cb4 : word) = Some W_26b3c.
Proof. vm_refl. Qed.
Lemma D_26b3c : decode_any W_26b3c = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b40 : bv 32 := 0x00033597.
Lemma F_26b40 : fetch_word Ubsan.M.loaded_segments (0x30cb8 : word) = Some W_26b40.
Proof. vm_refl. Qed.
Lemma D_26b40 : decode_any W_26b40 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b44 : bv 32 := 0x7bb58683.
Lemma F_26b44 : fetch_word Ubsan.M.loaded_segments (0x30cbc : word) = Some W_26b44.
Proof. vm_refl. Qed.
Lemma D_26b44 : decode_any W_26b44 = Some (Load SZ1 true 13 11 1979, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26b48 : bv 32 := 0x1e068863.
Lemma F_26b48 : fetch_word Ubsan.M.loaded_segments (0x30cc0 : word) = Some W_26b48.
Proof. vm_refl. Qed.
Lemma D_26b48 : decode_any W_26b48 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26d38 : bv 32 := 0x00008067.
Lemma F_26d38 : fetch_word Ubsan.M.loaded_segments (0x30eb0 : word) = Some W_26d38.
Proof. vm_refl. Qed.
Lemma D_26d38 : decode_any W_26d38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3c : bv 32 := 0x00050893.
Lemma F_26e3c : fetch_word Ubsan.M.loaded_segments (0x30fb4 : word) = Some W_26e3c.
Proof. vm_refl. Qed.
Lemma D_26e3c : decode_any W_26e3c = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e40 : bv 32 := 0x00058513.
Lemma F_26e40 : fetch_word Ubsan.M.loaded_segments (0x30fb8 : word) = Some W_26e40.
Proof. vm_refl. Qed.
Lemma D_26e40 : decode_any W_26e40 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e44 : bv 32 := 0x00060593.
Lemma F_26e44 : fetch_word Ubsan.M.loaded_segments (0x30fbc : word) = Some W_26e44.
Proof. vm_refl. Qed.
Lemma D_26e44 : decode_any W_26e44 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e48 : bv 32 := 0x00068613.
Lemma F_26e48 : fetch_word Ubsan.M.loaded_segments (0x30fc0 : word) = Some W_26e48.
Proof. vm_refl. Qed.
Lemma D_26e48 : decode_any W_26e48 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4c : bv 32 := 0x00070693.
Lemma F_26e4c : fetch_word Ubsan.M.loaded_segments (0x30fc4 : word) = Some W_26e4c.
Proof. vm_refl. Qed.
Lemma D_26e4c : decode_any W_26e4c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e50 : bv 32 := 0x00078713.
Lemma F_26e50 : fetch_word Ubsan.M.loaded_segments (0x30fc8 : word) = Some W_26e50.
Proof. vm_refl. Qed.
Lemma D_26e50 : decode_any W_26e50 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e54 : bv 32 := 0x00080793.
Lemma F_26e54 : fetch_word Ubsan.M.loaded_segments (0x30fcc : word) = Some W_26e54.
Proof. vm_refl. Qed.
Lemma D_26e54 : decode_any W_26e54 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e58 : bv 32 := 0x00000073.
Lemma F_26e58 : fetch_word Ubsan.M.loaded_segments (0x30fd0 : word) = Some W_26e58.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_26e58 : is_ecall W_26e58 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e5c : bv 32 := 0x00008067.
Lemma F_26e5c : fetch_word Ubsan.M.loaded_segments (0x30fd4 : word) = Some W_26e5c.
Proof. vm_refl. Qed.
Lemma D_26e5c : decode_any W_26e5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e60 : bv 32 := 0xfddff06f.
Lemma F_26e60 : fetch_word Ubsan.M.loaded_segments (0x30fd8 : word) = Some W_26e60.
Proof. vm_refl. Qed.
Lemma D_26e60 : decode_any W_26e60 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e64 : bv 32 := 0x00050213.
Lemma F_26e64 : fetch_word Ubsan.M.loaded_segments (0x30fdc : word) = Some W_26e64.
Proof. vm_refl. Qed.
Lemma D_26e64 : decode_any W_26e64 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e68 : bv 32 := 0x00000513.
Lemma F_26e68 : fetch_word Ubsan.M.loaded_segments (0x30fe0 : word) = Some W_26e68.
Proof. vm_refl. Qed.
Lemma D_26e68 : decode_any W_26e68 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c : bv 32 := 0x00008067.
Lemma F_26e6c : fetch_word Ubsan.M.loaded_segments (0x30fe4 : word) = Some W_26e6c.
Proof. vm_refl. Qed.
Lemma D_26e6c : decode_any W_26e6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e70 : bv 32 := 0xff010113.
Lemma F_26e70 : fetch_word Ubsan.M.loaded_segments (0x30ff4 : word) = Some W_26e70.
Proof. vm_refl. Qed.
Lemma D_26e70 : decode_any W_26e70 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e74 : bv 32 := 0x00113423.
Lemma F_26e74 : fetch_word Ubsan.M.loaded_segments (0x30ff8 : word) = Some W_26e74.
Proof. vm_refl. Qed.
Lemma D_26e74 : decode_any W_26e74 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e78 : bv 32 := 0xfc9f90ef.
Lemma F_26e78 : fetch_word Ubsan.M.loaded_segments (0x30ffc : word) = Some W_26e78.
Proof. vm_refl. Qed.
Lemma D_26e78 : decode_any W_26e78 = Some (Jal 1 2072520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7c : bv 32 := 0x00050593.
Lemma F_26e7c : fetch_word Ubsan.M.loaded_segments (0x31000 : word) = Some W_26e7c.
Proof. vm_refl. Qed.
Lemma D_26e7c : decode_any W_26e7c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e80 : bv 32 := 0x03900513.
Lemma F_26e80 : fetch_word Ubsan.M.loaded_segments (0x31004 : word) = Some W_26e80.
Proof. vm_refl. Qed.
Lemma D_26e80 : decode_any W_26e80 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e84 : bv 32 := 0x00000613.
Lemma F_26e84 : fetch_word Ubsan.M.loaded_segments (0x31008 : word) = Some W_26e84.
Proof. vm_refl. Qed.
Lemma D_26e84 : decode_any W_26e84 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e88 : bv 32 := 0x00000693.
Lemma F_26e88 : fetch_word Ubsan.M.loaded_segments (0x3100c : word) = Some W_26e88.
Proof. vm_refl. Qed.
Lemma D_26e88 : decode_any W_26e88 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8c : bv 32 := 0x00000713.
Lemma F_26e8c : fetch_word Ubsan.M.loaded_segments (0x31010 : word) = Some W_26e8c.
Proof. vm_refl. Qed.
Lemma D_26e8c : decode_any W_26e8c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e90 : bv 32 := 0x00000793.
Lemma F_26e90 : fetch_word Ubsan.M.loaded_segments (0x31014 : word) = Some W_26e90.
Proof. vm_refl. Qed.
Lemma D_26e90 : decode_any W_26e90 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e94 : bv 32 := 0x00000813.
Lemma F_26e94 : fetch_word Ubsan.M.loaded_segments (0x31018 : word) = Some W_26e94.
Proof. vm_refl. Qed.
Lemma D_26e94 : decode_any W_26e94 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e98 : bv 32 := 0xfbdff0ef.
Lemma F_26e98 : fetch_word Ubsan.M.loaded_segments (0x3101c : word) = Some W_26e98.
Proof. vm_refl. Qed.
Lemma D_26e98 : decode_any W_26e98 = Some (Jal 1 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9c : bv 32 := 0x0005051b.
Lemma F_26e9c : fetch_word Ubsan.M.loaded_segments (0x31020 : word) = Some W_26e9c.
Proof. vm_refl. Qed.
Lemma D_26e9c : decode_any W_26e9c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea0 : bv 32 := 0x00450593.
Lemma F_26ea0 : fetch_word Ubsan.M.loaded_segments (0x31024 : word) = Some W_26ea0.
Proof. vm_refl. Qed.
Lemma D_26ea0 : decode_any W_26ea0 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea4 : bv 32 := 0x0015b593.
Lemma F_26ea4 : fetch_word Ubsan.M.loaded_segments (0x31028 : word) = Some W_26ea4.
Proof. vm_refl. Qed.
Lemma D_26ea4 : decode_any W_26ea4 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea8 : bv 32 := 0xfff58593.
Lemma F_26ea8 : fetch_word Ubsan.M.loaded_segments (0x3102c : word) = Some W_26ea8.
Proof. vm_refl. Qed.
Lemma D_26ea8 : decode_any W_26ea8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eac : bv 32 := 0x00a5f533.
Lemma F_26eac : fetch_word Ubsan.M.loaded_segments (0x31030 : word) = Some W_26eac.
Proof. vm_refl. Qed.
Lemma D_26eac : decode_any W_26eac = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb0 : bv 32 := 0xb4cf80ef.
Lemma F_26eb0 : fetch_word Ubsan.M.loaded_segments (0x31034 : word) = Some W_26eb0.
Proof. vm_refl. Qed.
Lemma D_26eb0 : decode_any W_26eb0 = Some (Jal 1 2065228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb4 : bv 32 := 0x0005051b.
Lemma F_26eb4 : fetch_word Ubsan.M.loaded_segments (0x31038 : word) = Some W_26eb4.
Proof. vm_refl. Qed.
Lemma D_26eb4 : decode_any W_26eb4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb8 : bv 32 := 0x00813083.
Lemma F_26eb8 : fetch_word Ubsan.M.loaded_segments (0x3103c : word) = Some W_26eb8.
Proof. vm_refl. Qed.
Lemma D_26eb8 : decode_any W_26eb8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebc : bv 32 := 0x01010113.
Lemma F_26ebc : fetch_word Ubsan.M.loaded_segments (0x31040 : word) = Some W_26ebc.
Proof. vm_refl. Qed.
Lemma D_26ebc : decode_any W_26ebc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec0 : bv 32 := 0x00008067.
Lemma F_26ec0 : fetch_word Ubsan.M.loaded_segments (0x31044 : word) = Some W_26ec0.
Proof. vm_refl. Qed.
Lemma D_26ec0 : decode_any W_26ec0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed0 : bv 32 := 0xff010113.
Lemma F_26ed0 : fetch_word Ubsan.M.loaded_segments (0x31054 : word) = Some W_26ed0.
Proof. vm_refl. Qed.
Lemma D_26ed0 : decode_any W_26ed0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed4 : bv 32 := 0x00113423.
Lemma F_26ed4 : fetch_word Ubsan.M.loaded_segments (0x31058 : word) = Some W_26ed4.
Proof. vm_refl. Qed.
Lemma D_26ed4 : decode_any W_26ed4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed8 : bv 32 := 0x00060693.
Lemma F_26ed8 : fetch_word Ubsan.M.loaded_segments (0x3105c : word) = Some W_26ed8.
Proof. vm_refl. Qed.
Lemma D_26ed8 : decode_any W_26ed8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edc : bv 32 := 0x00058613.
Lemma F_26edc : fetch_word Ubsan.M.loaded_segments (0x31060 : word) = Some W_26edc.
Proof. vm_refl. Qed.
Lemma D_26edc : decode_any W_26edc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee0 : bv 32 := 0x00050593.
Lemma F_26ee0 : fetch_word Ubsan.M.loaded_segments (0x31064 : word) = Some W_26ee0.
Proof. vm_refl. Qed.
Lemma D_26ee0 : decode_any W_26ee0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee4 : bv 32 := 0x03f00513.
Lemma F_26ee4 : fetch_word Ubsan.M.loaded_segments (0x31068 : word) = Some W_26ee4.
Proof. vm_refl. Qed.
Lemma D_26ee4 : decode_any W_26ee4 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee8 : bv 32 := 0x00000713.
Lemma F_26ee8 : fetch_word Ubsan.M.loaded_segments (0x3106c : word) = Some W_26ee8.
Proof. vm_refl. Qed.
Lemma D_26ee8 : decode_any W_26ee8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec : bv 32 := 0x00000793.
Lemma F_26eec : fetch_word Ubsan.M.loaded_segments (0x31070 : word) = Some W_26eec.
Proof. vm_refl. Qed.
Lemma D_26eec : decode_any W_26eec = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef0 : bv 32 := 0x00000813.
Lemma F_26ef0 : fetch_word Ubsan.M.loaded_segments (0x31074 : word) = Some W_26ef0.
Proof. vm_refl. Qed.
Lemma D_26ef0 : decode_any W_26ef0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef4 : bv 32 := 0xf61ff0ef.
Lemma F_26ef4 : fetch_word Ubsan.M.loaded_segments (0x31078 : word) = Some W_26ef4.
Proof. vm_refl. Qed.
Lemma D_26ef4 : decode_any W_26ef4 = Some (Jal 1 2096992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef8 : bv 32 := 0x00813083.
Lemma F_26ef8 : fetch_word Ubsan.M.loaded_segments (0x3107c : word) = Some W_26ef8.
Proof. vm_refl. Qed.
Lemma D_26ef8 : decode_any W_26ef8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efc : bv 32 := 0x01010113.
Lemma F_26efc : fetch_word Ubsan.M.loaded_segments (0x31080 : word) = Some W_26efc.
Proof. vm_refl. Qed.
Lemma D_26efc : decode_any W_26efc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f00 : bv 32 := 0xafcf806f.
Lemma F_26f00 : fetch_word Ubsan.M.loaded_segments (0x31084 : word) = Some W_26f00.
Proof. vm_refl. Qed.
Lemma D_26f00 : decode_any W_26f00 = Some (Jal 0 2065148, 4%Z).
Proof. vm_refl. Qed.
