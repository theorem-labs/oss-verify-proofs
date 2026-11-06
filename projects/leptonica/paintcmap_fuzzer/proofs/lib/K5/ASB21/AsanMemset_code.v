(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)
Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof. intros segs a w. apply bool_decide_eq_true_1. Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof. intros w x. apply bool_decide_eq_true_1. Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

(* [comment removed for export] *)
Definition W_bec80 : bv 32 := 0x0e060a63.
Lemma F_bec80 : fetch_word AsanUbsan.M.loaded_segments (0xc4420 : word) = Some W_bec80.
Proof. vm_refl. Qed.
Lemma D_bec80 : decode_any W_bec80 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec84 : bv 32 := 0x00b50023.
Lemma F_bec84 : fetch_word AsanUbsan.M.loaded_segments (0xc4424 : word) = Some W_bec84.
Proof. vm_refl. Qed.
Lemma D_bec84 : decode_any W_bec84 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec88 : bv 32 := 0x00c506b3.
Lemma F_bec88 : fetch_word AsanUbsan.M.loaded_segments (0xc4428 : word) = Some W_bec88.
Proof. vm_refl. Qed.
Lemma D_bec88 : decode_any W_bec88 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec8c : bv 32 := 0x00300713.
Lemma F_bec8c : fetch_word AsanUbsan.M.loaded_segments (0xc442c : word) = Some W_bec8c.
Proof. vm_refl. Qed.
Lemma D_bec8c : decode_any W_bec8c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec90 : bv 32 := 0xfeb68fa3.
Lemma F_bec90 : fetch_word AsanUbsan.M.loaded_segments (0xc4430 : word) = Some W_bec90.
Proof. vm_refl. Qed.
Lemma D_bec90 : decode_any W_bec90 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec94 : bv 32 := 0x0ee66063.
Lemma F_bec94 : fetch_word AsanUbsan.M.loaded_segments (0xc4434 : word) = Some W_bec94.
Proof. vm_refl. Qed.
Lemma D_bec94 : decode_any W_bec94 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec98 : bv 32 := 0x00b500a3.
Lemma F_bec98 : fetch_word AsanUbsan.M.loaded_segments (0xc4438 : word) = Some W_bec98.
Proof. vm_refl. Qed.
Lemma D_bec98 : decode_any W_bec98 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec9c : bv 32 := 0x00b50123.
Lemma F_bec9c : fetch_word AsanUbsan.M.loaded_segments (0xc443c : word) = Some W_bec9c.
Proof. vm_refl. Qed.
Lemma D_bec9c : decode_any W_bec9c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beca0 : bv 32 := 0x00700713.
Lemma F_beca0 : fetch_word AsanUbsan.M.loaded_segments (0xc4440 : word) = Some W_beca0.
Proof. vm_refl. Qed.
Lemma D_beca0 : decode_any W_beca0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beca4 : bv 32 := 0xfeb68ea3.
Lemma F_beca4 : fetch_word AsanUbsan.M.loaded_segments (0xc4444 : word) = Some W_beca4.
Proof. vm_refl. Qed.
Lemma D_beca4 : decode_any W_beca4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beca8 : bv 32 := 0xfeb68f23.
Lemma F_beca8 : fetch_word AsanUbsan.M.loaded_segments (0xc4448 : word) = Some W_beca8.
Proof. vm_refl. Qed.
Lemma D_beca8 : decode_any W_beca8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becac : bv 32 := 0x0ce66463.
Lemma F_becac : fetch_word AsanUbsan.M.loaded_segments (0xc444c : word) = Some W_becac.
Proof. vm_refl. Qed.
Lemma D_becac : decode_any W_becac = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becb0 : bv 32 := 0x00b501a3.
Lemma F_becb0 : fetch_word AsanUbsan.M.loaded_segments (0xc4450 : word) = Some W_becb0.
Proof. vm_refl. Qed.
Lemma D_becb0 : decode_any W_becb0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becb4 : bv 32 := 0x00900793.
Lemma F_becb4 : fetch_word AsanUbsan.M.loaded_segments (0xc4454 : word) = Some W_becb4.
Proof. vm_refl. Qed.
Lemma D_becb4 : decode_any W_becb4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becb8 : bv 32 := 0xfeb68e23.
Lemma F_becb8 : fetch_word AsanUbsan.M.loaded_segments (0xc4458 : word) = Some W_becb8.
Proof. vm_refl. Qed.
Lemma D_becb8 : decode_any W_becb8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becbc : bv 32 := 0x0af66c63.
Lemma F_becbc : fetch_word AsanUbsan.M.loaded_segments (0xc445c : word) = Some W_becbc.
Proof. vm_refl. Qed.
Lemma D_becbc : decode_any W_becbc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becc0 : bv 32 := 0x40a006bb.
Lemma F_becc0 : fetch_word AsanUbsan.M.loaded_segments (0xc4460 : word) = Some W_becc0.
Proof. vm_refl. Qed.
Lemma D_becc0 : decode_any W_becc0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becc4 : bv 32 := 0x03859813.
Lemma F_becc4 : fetch_word AsanUbsan.M.loaded_segments (0xc4464 : word) = Some W_becc4.
Proof. vm_refl. Qed.
Lemma D_becc4 : decode_any W_becc4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becc8 : bv 32 := 0x101015b7.
Lemma F_becc8 : fetch_word AsanUbsan.M.loaded_segments (0xc4468 : word) = Some W_becc8.
Proof. vm_refl. Qed.
Lemma D_becc8 : decode_any W_becc8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beccc : bv 32 := 0x0036f693.
Lemma F_beccc : fetch_word AsanUbsan.M.loaded_segments (0xc446c : word) = Some W_beccc.
Proof. vm_refl. Qed.
Lemma D_beccc : decode_any W_beccc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becd0 : bv 32 := 0x00459713.
Lemma F_becd0 : fetch_word AsanUbsan.M.loaded_segments (0xc4470 : word) = Some W_becd0.
Proof. vm_refl. Qed.
Lemma D_becd0 : decode_any W_becd0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becd4 : bv 32 := 0x40d60633.
Lemma F_becd4 : fetch_word AsanUbsan.M.loaded_segments (0xc4474 : word) = Some W_becd4.
Proof. vm_refl. Qed.
Lemma D_becd4 : decode_any W_becd4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becd8 : bv 32 := 0x00d505b3.
Lemma F_becd8 : fetch_word AsanUbsan.M.loaded_segments (0xc4478 : word) = Some W_becd8.
Proof. vm_refl. Qed.
Lemma D_becd8 : decode_any W_becd8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becdc : bv 32 := 0x10070693.
Lemma F_becdc : fetch_word AsanUbsan.M.loaded_segments (0xc447c : word) = Some W_becdc.
Proof. vm_refl. Qed.
Lemma D_becdc : decode_any W_becdc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bece0 : bv 32 := 0xffc67713.
Lemma F_bece0 : fetch_word AsanUbsan.M.loaded_segments (0xc4480 : word) = Some W_bece0.
Proof. vm_refl. Qed.
Lemma D_bece0 : decode_any W_bece0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bece4 : bv 32 := 0x02d83633.
Lemma F_bece4 : fetch_word AsanUbsan.M.loaded_segments (0xc4484 : word) = Some W_bece4.
Proof. vm_refl. Qed.
Lemma D_bece4 : decode_any W_bece4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bece8 : bv 32 := 0x00c5a023.
Lemma F_bece8 : fetch_word AsanUbsan.M.loaded_segments (0xc4488 : word) = Some W_bece8.
Proof. vm_refl. Qed.
Lemma D_bece8 : decode_any W_bece8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becec : bv 32 := 0x00e586b3.
Lemma F_becec : fetch_word AsanUbsan.M.loaded_segments (0xc448c : word) = Some W_becec.
Proof. vm_refl. Qed.
Lemma D_becec : decode_any W_becec = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becf0 : bv 32 := 0xfec6ae23.
Lemma F_becf0 : fetch_word AsanUbsan.M.loaded_segments (0xc4490 : word) = Some W_becf0.
Proof. vm_refl. Qed.
Lemma D_becf0 : decode_any W_becf0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becf4 : bv 32 := 0x08f76063.
Lemma F_becf4 : fetch_word AsanUbsan.M.loaded_segments (0xc4494 : word) = Some W_becf4.
Proof. vm_refl. Qed.
Lemma D_becf4 : decode_any W_becf4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becf8 : bv 32 := 0x00c5a223.
Lemma F_becf8 : fetch_word AsanUbsan.M.loaded_segments (0xc4498 : word) = Some W_becf8.
Proof. vm_refl. Qed.
Lemma D_becf8 : decode_any W_becf8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_becfc : bv 32 := 0x00c5a423.
Lemma F_becfc : fetch_word AsanUbsan.M.loaded_segments (0xc449c : word) = Some W_becfc.
Proof. vm_refl. Qed.
Lemma D_becfc : decode_any W_becfc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed00 : bv 32 := 0x01900793.
Lemma F_bed00 : fetch_word AsanUbsan.M.loaded_segments (0xc44a0 : word) = Some W_bed00.
Proof. vm_refl. Qed.
Lemma D_bed00 : decode_any W_bed00 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed04 : bv 32 := 0xfec6aa23.
Lemma F_bed04 : fetch_word AsanUbsan.M.loaded_segments (0xc44a4 : word) = Some W_bed04.
Proof. vm_refl. Qed.
Lemma D_bed04 : decode_any W_bed04 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed08 : bv 32 := 0xfec6ac23.
Lemma F_bed08 : fetch_word AsanUbsan.M.loaded_segments (0xc44a8 : word) = Some W_bed08.
Proof. vm_refl. Qed.
Lemma D_bed08 : decode_any W_bed08 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed0c : bv 32 := 0x06f76463.
Lemma F_bed0c : fetch_word AsanUbsan.M.loaded_segments (0xc44ac : word) = Some W_bed0c.
Proof. vm_refl. Qed.
Lemma D_bed0c : decode_any W_bed0c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed10 : bv 32 := 0x00c5a623.
Lemma F_bed10 : fetch_word AsanUbsan.M.loaded_segments (0xc44b0 : word) = Some W_bed10.
Proof. vm_refl. Qed.
Lemma D_bed10 : decode_any W_bed10 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed14 : bv 32 := 0x00c5a823.
Lemma F_bed14 : fetch_word AsanUbsan.M.loaded_segments (0xc44b4 : word) = Some W_bed14.
Proof. vm_refl. Qed.
Lemma D_bed14 : decode_any W_bed14 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed18 : bv 32 := 0x00c5aa23.
Lemma F_bed18 : fetch_word AsanUbsan.M.loaded_segments (0xc44b8 : word) = Some W_bed18.
Proof. vm_refl. Qed.
Lemma D_bed18 : decode_any W_bed18 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed1c : bv 32 := 0x00c5ac23.
Lemma F_bed1c : fetch_word AsanUbsan.M.loaded_segments (0xc44bc : word) = Some W_bed1c.
Proof. vm_refl. Qed.
Lemma D_bed1c : decode_any W_bed1c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed20 : bv 32 := 0x0045f793.
Lemma F_bed20 : fetch_word AsanUbsan.M.loaded_segments (0xc44c0 : word) = Some W_bed20.
Proof. vm_refl. Qed.
Lemma D_bed20 : decode_any W_bed20 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed24 : bv 32 := 0x02000813.
Lemma F_bed24 : fetch_word AsanUbsan.M.loaded_segments (0xc44c4 : word) = Some W_bed24.
Proof. vm_refl. Qed.
Lemma D_bed24 : decode_any W_bed24 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed28 : bv 32 := 0x01878793.
Lemma F_bed28 : fetch_word AsanUbsan.M.loaded_segments (0xc44c8 : word) = Some W_bed28.
Proof. vm_refl. Qed.
Lemma D_bed28 : decode_any W_bed28 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed2c : bv 32 := 0x40f70733.
Lemma F_bed2c : fetch_word AsanUbsan.M.loaded_segments (0xc44cc : word) = Some W_bed2c.
Proof. vm_refl. Qed.
Lemma D_bed2c : decode_any W_bed2c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed30 : bv 32 := 0xfec6a223.
Lemma F_bed30 : fetch_word AsanUbsan.M.loaded_segments (0xc44d0 : word) = Some W_bed30.
Proof. vm_refl. Qed.
Lemma D_bed30 : decode_any W_bed30 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed34 : bv 32 := 0xfec6a423.
Lemma F_bed34 : fetch_word AsanUbsan.M.loaded_segments (0xc44d4 : word) = Some W_bed34.
Proof. vm_refl. Qed.
Lemma D_bed34 : decode_any W_bed34 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed38 : bv 32 := 0xfec6a623.
Lemma F_bed38 : fetch_word AsanUbsan.M.loaded_segments (0xc44d8 : word) = Some W_bed38.
Proof. vm_refl. Qed.
Lemma D_bed38 : decode_any W_bed38 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed3c : bv 32 := 0xfec6a823.
Lemma F_bed3c : fetch_word AsanUbsan.M.loaded_segments (0xc44dc : word) = Some W_bed3c.
Proof. vm_refl. Qed.
Lemma D_bed3c : decode_any W_bed3c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed40 : bv 32 := 0x03076a63.
Lemma F_bed40 : fetch_word AsanUbsan.M.loaded_segments (0xc44e0 : word) = Some W_bed40.
Proof. vm_refl. Qed.
Lemma D_bed40 : decode_any W_bed40 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed44 : bv 32 := 0x02061613.
Lemma F_bed44 : fetch_word AsanUbsan.M.loaded_segments (0xc44e4 : word) = Some W_bed44.
Proof. vm_refl. Qed.
Lemma D_bed44 : decode_any W_bed44 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed48 : bv 32 := 0x00f585b3.
Lemma F_bed48 : fetch_word AsanUbsan.M.loaded_segments (0xc44e8 : word) = Some W_bed48.
Proof. vm_refl. Qed.
Lemma D_bed48 : decode_any W_bed48 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed4c : bv 32 := 0x02065693.
Lemma F_bed4c : fetch_word AsanUbsan.M.loaded_segments (0xc44ec : word) = Some W_bed4c.
Proof. vm_refl. Qed.
Lemma D_bed4c : decode_any W_bed4c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed50 : bv 32 := 0x00d66633.
Lemma F_bed50 : fetch_word AsanUbsan.M.loaded_segments (0xc44f0 : word) = Some W_bed50.
Proof. vm_refl. Qed.
Lemma D_bed50 : decode_any W_bed50 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed54 : bv 32 := 0x01f00693.
Lemma F_bed54 : fetch_word AsanUbsan.M.loaded_segments (0xc44f4 : word) = Some W_bed54.
Proof. vm_refl. Qed.
Lemma D_bed54 : decode_any W_bed54 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed58 : bv 32 := 0x00c5b023.
Lemma F_bed58 : fetch_word AsanUbsan.M.loaded_segments (0xc44f8 : word) = Some W_bed58.
Proof. vm_refl. Qed.
Lemma D_bed58 : decode_any W_bed58 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed5c : bv 32 := 0x00c5b423.
Lemma F_bed5c : fetch_word AsanUbsan.M.loaded_segments (0xc44fc : word) = Some W_bed5c.
Proof. vm_refl. Qed.
Lemma D_bed5c : decode_any W_bed5c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed60 : bv 32 := 0x00c5b823.
Lemma F_bed60 : fetch_word AsanUbsan.M.loaded_segments (0xc4500 : word) = Some W_bed60.
Proof. vm_refl. Qed.
Lemma D_bed60 : decode_any W_bed60 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed64 : bv 32 := 0x00c5bc23.
Lemma F_bed64 : fetch_word AsanUbsan.M.loaded_segments (0xc4504 : word) = Some W_bed64.
Proof. vm_refl. Qed.
Lemma D_bed64 : decode_any W_bed64 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed68 : bv 32 := 0xfe070713.
Lemma F_bed68 : fetch_word AsanUbsan.M.loaded_segments (0xc4508 : word) = Some W_bed68.
Proof. vm_refl. Qed.
Lemma D_bed68 : decode_any W_bed68 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed6c : bv 32 := 0x02058593.
Lemma F_bed6c : fetch_word AsanUbsan.M.loaded_segments (0xc450c : word) = Some W_bed6c.
Proof. vm_refl. Qed.
Lemma D_bed6c : decode_any W_bed6c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed70 : bv 32 := 0xfee6e4e3.
Lemma F_bed70 : fetch_word AsanUbsan.M.loaded_segments (0xc4510 : word) = Some W_bed70.
Proof. vm_refl. Qed.
Lemma D_bed70 : decode_any W_bed70 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bed74 : bv 32 := 0x00008067.
Lemma F_bed74 : fetch_word AsanUbsan.M.loaded_segments (0xc4514 : word) = Some W_bed74.
Proof. vm_refl. Qed.
Lemma D_bed74 : decode_any W_bed74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xc4420%Z.
Definition Fo_000 := F_bec80.
Definition Do_000 := D_bec80.
Definition Fo_004 := F_bec84.
Definition Do_004 := D_bec84.
Definition Fo_008 := F_bec88.
Definition Do_008 := D_bec88.
Definition Fo_00c := F_bec8c.
Definition Do_00c := D_bec8c.
Definition Fo_010 := F_bec90.
Definition Do_010 := D_bec90.
Definition Fo_014 := F_bec94.
Definition Do_014 := D_bec94.
Definition Fo_018 := F_bec98.
Definition Do_018 := D_bec98.
Definition Fo_01c := F_bec9c.
Definition Do_01c := D_bec9c.
Definition Fo_020 := F_beca0.
Definition Do_020 := D_beca0.
Definition Fo_024 := F_beca4.
Definition Do_024 := D_beca4.
Definition Fo_028 := F_beca8.
Definition Do_028 := D_beca8.
Definition Fo_02c := F_becac.
Definition Do_02c := D_becac.
Definition Fo_030 := F_becb0.
Definition Do_030 := D_becb0.
Definition Fo_034 := F_becb4.
Definition Do_034 := D_becb4.
Definition Fo_038 := F_becb8.
Definition Do_038 := D_becb8.
Definition Fo_03c := F_becbc.
Definition Do_03c := D_becbc.
Definition Fo_040 := F_becc0.
Definition Do_040 := D_becc0.
Definition Fo_044 := F_becc4.
Definition Do_044 := D_becc4.
Definition Fo_048 := F_becc8.
Definition Do_048 := D_becc8.
Definition Fo_04c := F_beccc.
Definition Do_04c := D_beccc.
Definition Fo_050 := F_becd0.
Definition Do_050 := D_becd0.
Definition Fo_054 := F_becd4.
Definition Do_054 := D_becd4.
Definition Fo_058 := F_becd8.
Definition Do_058 := D_becd8.
Definition Fo_05c := F_becdc.
Definition Do_05c := D_becdc.
Definition Fo_060 := F_bece0.
Definition Do_060 := D_bece0.
Definition Fo_064 := F_bece4.
Definition Do_064 := D_bece4.
Definition Fo_068 := F_bece8.
Definition Do_068 := D_bece8.
Definition Fo_06c := F_becec.
Definition Do_06c := D_becec.
Definition Fo_070 := F_becf0.
Definition Do_070 := D_becf0.
Definition Fo_074 := F_becf4.
Definition Do_074 := D_becf4.
Definition Fo_078 := F_becf8.
Definition Do_078 := D_becf8.
Definition Fo_07c := F_becfc.
Definition Do_07c := D_becfc.
Definition Fo_080 := F_bed00.
Definition Do_080 := D_bed00.
Definition Fo_084 := F_bed04.
Definition Do_084 := D_bed04.
Definition Fo_088 := F_bed08.
Definition Do_088 := D_bed08.
Definition Fo_08c := F_bed0c.
Definition Do_08c := D_bed0c.
Definition Fo_090 := F_bed10.
Definition Do_090 := D_bed10.
Definition Fo_094 := F_bed14.
Definition Do_094 := D_bed14.
Definition Fo_098 := F_bed18.
Definition Do_098 := D_bed18.
Definition Fo_09c := F_bed1c.
Definition Do_09c := D_bed1c.
Definition Fo_0a0 := F_bed20.
Definition Do_0a0 := D_bed20.
Definition Fo_0a4 := F_bed24.
Definition Do_0a4 := D_bed24.
Definition Fo_0a8 := F_bed28.
Definition Do_0a8 := D_bed28.
Definition Fo_0ac := F_bed2c.
Definition Do_0ac := D_bed2c.
Definition Fo_0b0 := F_bed30.
Definition Do_0b0 := D_bed30.
Definition Fo_0b4 := F_bed34.
Definition Do_0b4 := D_bed34.
Definition Fo_0b8 := F_bed38.
Definition Do_0b8 := D_bed38.
Definition Fo_0bc := F_bed3c.
Definition Do_0bc := D_bed3c.
Definition Fo_0c0 := F_bed40.
Definition Do_0c0 := D_bed40.
Definition Fo_0c4 := F_bed44.
Definition Do_0c4 := D_bed44.
Definition Fo_0c8 := F_bed48.
Definition Do_0c8 := D_bed48.
Definition Fo_0cc := F_bed4c.
Definition Do_0cc := D_bed4c.
Definition Fo_0d0 := F_bed50.
Definition Do_0d0 := D_bed50.
Definition Fo_0d4 := F_bed54.
Definition Do_0d4 := D_bed54.
Definition Fo_0d8 := F_bed58.
Definition Do_0d8 := D_bed58.
Definition Fo_0dc := F_bed5c.
Definition Do_0dc := D_bed5c.
Definition Fo_0e0 := F_bed60.
Definition Do_0e0 := D_bed60.
Definition Fo_0e4 := F_bed64.
Definition Do_0e4 := D_bed64.
Definition Fo_0e8 := F_bed68.
Definition Do_0e8 := D_bed68.
Definition Fo_0ec := F_bed6c.
Definition Do_0ec := D_bed6c.
Definition Fo_0f0 := F_bed70.
Definition Do_0f0 := D_bed70.
Definition Fo_0f4 := F_bed74.
Definition Do_0f4 := D_bed74.
