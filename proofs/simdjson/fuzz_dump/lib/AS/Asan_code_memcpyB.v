(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof. intros segs a w. apply bool_decide_eq_true_1. Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof. intros w x. apply bool_decide_eq_true_1. Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

Definition W_93164 : bv 32 := 0x0035f693.
Lemma F_93164 : fetch_word AsanUbsan.M.loaded_segments (0x160884 : word) = Some W_93164.
Proof. vm_refl. Qed.
Lemma D_93164 : decode_any W_93164 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_93168 : bv 32 := 0x10068863.
Lemma F_93168 : fetch_word AsanUbsan.M.loaded_segments (0x160888 : word) = Some W_93168.
Proof. vm_refl. Qed.
Lemma D_93168 : decode_any W_93168 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_9316c : bv 32 := 0x02060e63.
Lemma F_9316c : fetch_word AsanUbsan.M.loaded_segments (0x16088c : word) = Some W_9316c.
Proof. vm_refl. Qed.
Lemma D_9316c : decode_any W_9316c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_93170 : bv 32 := 0x00158713.
Lemma F_93170 : fetch_word AsanUbsan.M.loaded_segments (0x160890 : word) = Some W_93170.
Proof. vm_refl. Qed.
Lemma D_93170 : decode_any W_93170 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93174 : bv 32 := 0x00100793.
Lemma F_93174 : fetch_word AsanUbsan.M.loaded_segments (0x160894 : word) = Some W_93174.
Proof. vm_refl. Qed.
Lemma D_93174 : decode_any W_93174 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93178 : bv 32 := 0x00050693.
Lemma F_93178 : fetch_word AsanUbsan.M.loaded_segments (0x160898 : word) = Some W_93178.
Proof. vm_refl. Qed.
Lemma D_93178 : decode_any W_93178 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9317c : bv 32 := 0x0005c883.
Lemma F_9317c : fetch_word AsanUbsan.M.loaded_segments (0x16089c : word) = Some W_9317c.
Proof. vm_refl. Qed.
Lemma D_9317c : decode_any W_9317c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93180 : bv 32 := 0x00060813.
Lemma F_93180 : fetch_word AsanUbsan.M.loaded_segments (0x1608a0 : word) = Some W_93180.
Proof. vm_refl. Qed.
Lemma D_93180 : decode_any W_93180 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93184 : bv 32 := 0x00158593.
Lemma F_93184 : fetch_word AsanUbsan.M.loaded_segments (0x1608a4 : word) = Some W_93184.
Proof. vm_refl. Qed.
Lemma D_93184 : decode_any W_93184 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93188 : bv 32 := 0x00377293.
Lemma F_93188 : fetch_word AsanUbsan.M.loaded_segments (0x1608a8 : word) = Some W_93188.
Proof. vm_refl. Qed.
Lemma D_93188 : decode_any W_93188 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9318c : bv 32 := 0x01168023.
Lemma F_9318c : fetch_word AsanUbsan.M.loaded_segments (0x1608ac : word) = Some W_9318c.
Proof. vm_refl. Qed.
Lemma D_9318c : decode_any W_9318c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93190 : bv 32 := 0x00168693.
Lemma F_93190 : fetch_word AsanUbsan.M.loaded_segments (0x1608b0 : word) = Some W_93190.
Proof. vm_refl. Qed.
Lemma D_93190 : decode_any W_93190 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93194 : bv 32 := 0xfff60613.
Lemma F_93194 : fetch_word AsanUbsan.M.loaded_segments (0x1608b4 : word) = Some W_93194.
Proof. vm_refl. Qed.
Lemma D_93194 : decode_any W_93194 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93198 : bv 32 := 0x00028a63.
Lemma F_93198 : fetch_word AsanUbsan.M.loaded_segments (0x1608b8 : word) = Some W_93198.
Proof. vm_refl. Qed.
Lemma D_93198 : decode_any W_93198 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9319c : bv 32 := 0x00170713.
Lemma F_9319c : fetch_word AsanUbsan.M.loaded_segments (0x1608bc : word) = Some W_9319c.
Proof. vm_refl. Qed.
Lemma D_9319c : decode_any W_9319c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_931a0 : bv 32 := 0xfcf81ee3.
Lemma F_931a0 : fetch_word AsanUbsan.M.loaded_segments (0x1608c0 : word) = Some W_931a0.
Proof. vm_refl. Qed.
Lemma D_931a0 : decode_any W_931a0 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_931a4 : bv 32 := 0x0080006f.
Lemma F_931a4 : fetch_word AsanUbsan.M.loaded_segments (0x1608c4 : word) = Some W_931a4.
Proof. vm_refl. Qed.
Lemma D_931a4 : decode_any W_931a4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_931a8 : bv 32 := 0x00050693.
Lemma F_931a8 : fetch_word AsanUbsan.M.loaded_segments (0x1608c8 : word) = Some W_931a8.
Proof. vm_refl. Qed.
Lemma D_931a8 : decode_any W_931a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_931ac : bv 32 := 0x0036f793.
Lemma F_931ac : fetch_word AsanUbsan.M.loaded_segments (0x1608cc : word) = Some W_931ac.
Proof. vm_refl. Qed.
Lemma D_931ac : decode_any W_931ac = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_931b0 : bv 32 := 0x0c078a63.
Lemma F_931b0 : fetch_word AsanUbsan.M.loaded_segments (0x1608d0 : word) = Some W_931b0.
Proof. vm_refl. Qed.
Lemma D_931b0 : decode_any W_931b0 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_931b4 : bv 32 := 0x02000713.
Lemma F_931b4 : fetch_word AsanUbsan.M.loaded_segments (0x1608d4 : word) = Some W_931b4.
Proof. vm_refl. Qed.
Lemma D_931b4 : decode_any W_931b4 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_931b8 : bv 32 := 0x02e67063.
Lemma F_931b8 : fetch_word AsanUbsan.M.loaded_segments (0x1608d8 : word) = Some W_931b8.
Proof. vm_refl. Qed.
Lemma D_931b8 : decode_any W_931b8 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_931bc : bv 32 := 0x01000713.
Lemma F_931bc : fetch_word AsanUbsan.M.loaded_segments (0x1608dc : word) = Some W_931bc.
Proof. vm_refl. Qed.
Lemma D_931bc : decode_any W_931bc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_931c0 : bv 32 := 0x24e67863.
Lemma F_931c0 : fetch_word AsanUbsan.M.loaded_segments (0x1608e0 : word) = Some W_931c0.
Proof. vm_refl. Qed.
Lemma D_931c0 : decode_any W_931c0 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_931c4 : bv 32 := 0x00867713.
Lemma F_931c4 : fetch_word AsanUbsan.M.loaded_segments (0x1608e4 : word) = Some W_931c4.
Proof. vm_refl. Qed.
Lemma D_931c4 : decode_any W_931c4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_931c8 : bv 32 := 0x2c071e63.
Lemma F_931c8 : fetch_word AsanUbsan.M.loaded_segments (0x1608e8 : word) = Some W_931c8.
Proof. vm_refl. Qed.
Lemma D_931c8 : decode_any W_931c8 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_931cc : bv 32 := 0x00467713.
Lemma F_931cc : fetch_word AsanUbsan.M.loaded_segments (0x1608ec : word) = Some W_931cc.
Proof. vm_refl. Qed.
Lemma D_931cc : decode_any W_931cc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_931d0 : bv 32 := 0x32071463.
Lemma F_931d0 : fetch_word AsanUbsan.M.loaded_segments (0x1608f0 : word) = Some W_931d0.
Proof. vm_refl. Qed.
Lemma D_931d0 : decode_any W_931d0 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_931d4 : bv 32 := 0x3500006f.
Lemma F_931d4 : fetch_word AsanUbsan.M.loaded_segments (0x1608f4 : word) = Some W_931d4.
Proof. vm_refl. Qed.
Lemma D_931d4 : decode_any W_931d4 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_931d8 : bv 32 := 0x0005a703.
Lemma F_931d8 : fetch_word AsanUbsan.M.loaded_segments (0x1608f8 : word) = Some W_931d8.
Proof. vm_refl. Qed.
Lemma D_931d8 : decode_any W_931d8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_931dc : bv 32 := 0x00300813.
Lemma F_931dc : fetch_word AsanUbsan.M.loaded_segments (0x1608fc : word) = Some W_931dc.
Proof. vm_refl. Qed.
Lemma D_931dc : decode_any W_931dc = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_931e0 : bv 32 := 0x11078e63.
Lemma F_931e0 : fetch_word AsanUbsan.M.loaded_segments (0x160900 : word) = Some W_931e0.
Proof. vm_refl. Qed.
Lemma D_931e0 : decode_any W_931e0 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_931e4 : bv 32 := 0x00200813.
Lemma F_931e4 : fetch_word AsanUbsan.M.loaded_segments (0x160904 : word) = Some W_931e4.
Proof. vm_refl. Qed.
Lemma D_931e4 : decode_any W_931e4 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_931e8 : bv 32 := 0x19079c63.
Lemma F_931e8 : fetch_word AsanUbsan.M.loaded_segments (0x160908 : word) = Some W_931e8.
Proof. vm_refl. Qed.
Lemma D_931e8 : decode_any W_931e8 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_931ec : bv 32 := 0x00875793.
Lemma F_931ec : fetch_word AsanUbsan.M.loaded_segments (0x16090c : word) = Some W_931ec.
Proof. vm_refl. Qed.
Lemma D_931ec : decode_any W_931ec = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_931f0 : bv 32 := 0xffe60613.
Lemma F_931f0 : fetch_word AsanUbsan.M.loaded_segments (0x160910 : word) = Some W_931f0.
Proof. vm_refl. Qed.
Lemma D_931f0 : decode_any W_931f0 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_931f4 : bv 32 := 0x00e68023.
Lemma F_931f4 : fetch_word AsanUbsan.M.loaded_segments (0x160914 : word) = Some W_931f4.
Proof. vm_refl. Qed.
Lemma D_931f4 : decode_any W_931f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_931f8 : bv 32 := 0x00f680a3.
Lemma F_931f8 : fetch_word AsanUbsan.M.loaded_segments (0x160918 : word) = Some W_931f8.
Proof. vm_refl. Qed.
Lemma D_931f8 : decode_any W_931f8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_931fc : bv 32 := 0x00268693.
Lemma F_931fc : fetch_word AsanUbsan.M.loaded_segments (0x16091c : word) = Some W_931fc.
Proof. vm_refl. Qed.
Lemma D_931fc : decode_any W_931fc = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93200 : bv 32 := 0x01058593.
Lemma F_93200 : fetch_word AsanUbsan.M.loaded_segments (0x160920 : word) = Some W_93200.
Proof. vm_refl. Qed.
Lemma D_93200 : decode_any W_93200 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93204 : bv 32 := 0x01100793.
Lemma F_93204 : fetch_word AsanUbsan.M.loaded_segments (0x160924 : word) = Some W_93204.
Proof. vm_refl. Qed.
Lemma D_93204 : decode_any W_93204 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_93208 : bv 32 := 0x0107581b.
Lemma F_93208 : fetch_word AsanUbsan.M.loaded_segments (0x160928 : word) = Some W_93208.
Proof. vm_refl. Qed.
Lemma D_93208 : decode_any W_93208 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9320c : bv 32 := 0xff45a883.
Lemma F_9320c : fetch_word AsanUbsan.M.loaded_segments (0x16092c : word) = Some W_9320c.
Proof. vm_refl. Qed.
Lemma D_9320c : decode_any W_9320c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_93210 : bv 32 := 0xff85a283.
Lemma F_93210 : fetch_word AsanUbsan.M.loaded_segments (0x160930 : word) = Some W_93210.
Proof. vm_refl. Qed.
Lemma D_93210 : decode_any W_93210 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_93214 : bv 32 := 0xffc5a303.
Lemma F_93214 : fetch_word AsanUbsan.M.loaded_segments (0x160934 : word) = Some W_93214.
Proof. vm_refl. Qed.
Lemma D_93214 : decode_any W_93214 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_93218 : bv 32 := 0x0005a703.
Lemma F_93218 : fetch_word AsanUbsan.M.loaded_segments (0x160938 : word) = Some W_93218.
Proof. vm_refl. Qed.
Lemma D_93218 : decode_any W_93218 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9321c : bv 32 := 0x01089393.
Lemma F_9321c : fetch_word AsanUbsan.M.loaded_segments (0x16093c : word) = Some W_9321c.
Proof. vm_refl. Qed.
Lemma D_9321c : decode_any W_9321c = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93220 : bv 32 := 0x0108d89b.
Lemma F_93220 : fetch_word AsanUbsan.M.loaded_segments (0x160940 : word) = Some W_93220.
Proof. vm_refl. Qed.
Lemma D_93220 : decode_any W_93220 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93224 : bv 32 := 0x0103e833.
Lemma F_93224 : fetch_word AsanUbsan.M.loaded_segments (0x160944 : word) = Some W_93224.
Proof. vm_refl. Qed.
Lemma D_93224 : decode_any W_93224 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93228 : bv 32 := 0x01029393.
Lemma F_93228 : fetch_word AsanUbsan.M.loaded_segments (0x160948 : word) = Some W_93228.
Proof. vm_refl. Qed.
Lemma D_93228 : decode_any W_93228 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9322c : bv 32 := 0x0102d29b.
Lemma F_9322c : fetch_word AsanUbsan.M.loaded_segments (0x16094c : word) = Some W_9322c.
Proof. vm_refl. Qed.
Lemma D_9322c : decode_any W_9322c = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93230 : bv 32 := 0x0113e8b3.
Lemma F_93230 : fetch_word AsanUbsan.M.loaded_segments (0x160950 : word) = Some W_93230.
Proof. vm_refl. Qed.
Lemma D_93230 : decode_any W_93230 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_93234 : bv 32 := 0x01031393.
Lemma F_93234 : fetch_word AsanUbsan.M.loaded_segments (0x160954 : word) = Some W_93234.
Proof. vm_refl. Qed.
Lemma D_93234 : decode_any W_93234 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93238 : bv 32 := 0x0103531b.
Lemma F_93238 : fetch_word AsanUbsan.M.loaded_segments (0x160958 : word) = Some W_93238.
Proof. vm_refl. Qed.
Lemma D_93238 : decode_any W_93238 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9323c : bv 32 := 0x0053e2b3.
Lemma F_9323c : fetch_word AsanUbsan.M.loaded_segments (0x16095c : word) = Some W_9323c.
Proof. vm_refl. Qed.
Lemma D_9323c : decode_any W_9323c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_93240 : bv 32 := 0x01071393.
Lemma F_93240 : fetch_word AsanUbsan.M.loaded_segments (0x160960 : word) = Some W_93240.
Proof. vm_refl. Qed.
Lemma D_93240 : decode_any W_93240 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93244 : bv 32 := 0x0063e333.
Lemma F_93244 : fetch_word AsanUbsan.M.loaded_segments (0x160964 : word) = Some W_93244.
Proof. vm_refl. Qed.
Lemma D_93244 : decode_any W_93244 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_93248 : bv 32 := 0xff060613.
Lemma F_93248 : fetch_word AsanUbsan.M.loaded_segments (0x160968 : word) = Some W_93248.
Proof. vm_refl. Qed.
Lemma D_93248 : decode_any W_93248 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9324c : bv 32 := 0x0106a023.
Lemma F_9324c : fetch_word AsanUbsan.M.loaded_segments (0x16096c : word) = Some W_9324c.
Proof. vm_refl. Qed.
Lemma D_9324c : decode_any W_9324c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93250 : bv 32 := 0x0116a223.
Lemma F_93250 : fetch_word AsanUbsan.M.loaded_segments (0x160970 : word) = Some W_93250.
Proof. vm_refl. Qed.
Lemma D_93250 : decode_any W_93250 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93254 : bv 32 := 0x0056a423.
Lemma F_93254 : fetch_word AsanUbsan.M.loaded_segments (0x160974 : word) = Some W_93254.
Proof. vm_refl. Qed.
Lemma D_93254 : decode_any W_93254 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93258 : bv 32 := 0x0066a623.
Lemma F_93258 : fetch_word AsanUbsan.M.loaded_segments (0x160978 : word) = Some W_93258.
Proof. vm_refl. Qed.
Lemma D_93258 : decode_any W_93258 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9325c : bv 32 := 0x01068693.
Lemma F_9325c : fetch_word AsanUbsan.M.loaded_segments (0x16097c : word) = Some W_9325c.
Proof. vm_refl. Qed.
Lemma D_9325c : decode_any W_9325c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93260 : bv 32 := 0x01058593.
Lemma F_93260 : fetch_word AsanUbsan.M.loaded_segments (0x160980 : word) = Some W_93260.
Proof. vm_refl. Qed.
Lemma D_93260 : decode_any W_93260 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93264 : bv 32 := 0xfac7e2e3.
Lemma F_93264 : fetch_word AsanUbsan.M.loaded_segments (0x160984 : word) = Some W_93264.
Proof. vm_refl. Qed.
Lemma D_93264 : decode_any W_93264 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_93268 : bv 32 := 0xff258593.
Lemma F_93268 : fetch_word AsanUbsan.M.loaded_segments (0x160988 : word) = Some W_93268.
Proof. vm_refl. Qed.
Lemma D_93268 : decode_any W_93268 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_9326c : bv 32 := 0x01000713.
Lemma F_9326c : fetch_word AsanUbsan.M.loaded_segments (0x16098c : word) = Some W_9326c.
Proof. vm_refl. Qed.
Lemma D_9326c : decode_any W_9326c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93270 : bv 32 := 0xf4e66ae3.
Lemma F_93270 : fetch_word AsanUbsan.M.loaded_segments (0x160990 : word) = Some W_93270.
Proof. vm_refl. Qed.
Lemma D_93270 : decode_any W_93270 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_93274 : bv 32 := 0x19c0006f.
Lemma F_93274 : fetch_word AsanUbsan.M.loaded_segments (0x160994 : word) = Some W_93274.
Proof. vm_refl. Qed.
Lemma D_93274 : decode_any W_93274 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_93278 : bv 32 := 0x00050693.
Lemma F_93278 : fetch_word AsanUbsan.M.loaded_segments (0x160998 : word) = Some W_93278.
Proof. vm_refl. Qed.
Lemma D_93278 : decode_any W_93278 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9327c : bv 32 := 0x00357793.
Lemma F_9327c : fetch_word AsanUbsan.M.loaded_segments (0x16099c : word) = Some W_9327c.
Proof. vm_refl. Qed.
Lemma D_9327c : decode_any W_9327c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_93280 : bv 32 := 0xf2079ae3.
Lemma F_93280 : fetch_word AsanUbsan.M.loaded_segments (0x1609a0 : word) = Some W_93280.
Proof. vm_refl. Qed.
Lemma D_93280 : decode_any W_93280 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_93284 : bv 32 := 0x01000713.
Lemma F_93284 : fetch_word AsanUbsan.M.loaded_segments (0x1609a4 : word) = Some W_93284.
Proof. vm_refl. Qed.
Lemma D_93284 : decode_any W_93284 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93288 : bv 32 := 0x02e66c63.
Lemma F_93288 : fetch_word AsanUbsan.M.loaded_segments (0x1609a8 : word) = Some W_93288.
Proof. vm_refl. Qed.
Lemma D_93288 : decode_any W_93288 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9328c : bv 32 := 0x00f00713.
Lemma F_9328c : fetch_word AsanUbsan.M.loaded_segments (0x1609ac : word) = Some W_9328c.
Proof. vm_refl. Qed.
Lemma D_9328c : decode_any W_9328c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93290 : bv 32 := 0x0005a783.
Lemma F_93290 : fetch_word AsanUbsan.M.loaded_segments (0x1609b0 : word) = Some W_93290.
Proof. vm_refl. Qed.
Lemma D_93290 : decode_any W_93290 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93294 : bv 32 := 0x0045a803.
Lemma F_93294 : fetch_word AsanUbsan.M.loaded_segments (0x1609b4 : word) = Some W_93294.
Proof. vm_refl. Qed.
Lemma D_93294 : decode_any W_93294 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93298 : bv 32 := 0x0085a883.
Lemma F_93298 : fetch_word AsanUbsan.M.loaded_segments (0x1609b8 : word) = Some W_93298.
Proof. vm_refl. Qed.
Lemma D_93298 : decode_any W_93298 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9329c : bv 32 := 0x00c5a283.
Lemma F_9329c : fetch_word AsanUbsan.M.loaded_segments (0x1609bc : word) = Some W_9329c.
Proof. vm_refl. Qed.
Lemma D_9329c : decode_any W_9329c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_932a0 : bv 32 := 0x01058593.
Lemma F_932a0 : fetch_word AsanUbsan.M.loaded_segments (0x1609c0 : word) = Some W_932a0.
Proof. vm_refl. Qed.
Lemma D_932a0 : decode_any W_932a0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_932a4 : bv 32 := 0xff060613.
Lemma F_932a4 : fetch_word AsanUbsan.M.loaded_segments (0x1609c4 : word) = Some W_932a4.
Proof. vm_refl. Qed.
Lemma D_932a4 : decode_any W_932a4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_932a8 : bv 32 := 0x00f6a023.
Lemma F_932a8 : fetch_word AsanUbsan.M.loaded_segments (0x1609c8 : word) = Some W_932a8.
Proof. vm_refl. Qed.
Lemma D_932a8 : decode_any W_932a8 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_932ac : bv 32 := 0x0106a223.
Lemma F_932ac : fetch_word AsanUbsan.M.loaded_segments (0x1609cc : word) = Some W_932ac.
Proof. vm_refl. Qed.
Lemma D_932ac : decode_any W_932ac = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_932b0 : bv 32 := 0x0116a423.
Lemma F_932b0 : fetch_word AsanUbsan.M.loaded_segments (0x1609d0 : word) = Some W_932b0.
Proof. vm_refl. Qed.
Lemma D_932b0 : decode_any W_932b0 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_932b4 : bv 32 := 0x0056a623.
Lemma F_932b4 : fetch_word AsanUbsan.M.loaded_segments (0x1609d4 : word) = Some W_932b4.
Proof. vm_refl. Qed.
Lemma D_932b4 : decode_any W_932b4 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_932b8 : bv 32 := 0x01068693.
Lemma F_932b8 : fetch_word AsanUbsan.M.loaded_segments (0x1609d8 : word) = Some W_932b8.
Proof. vm_refl. Qed.
Lemma D_932b8 : decode_any W_932b8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_932bc : bv 32 := 0xfcc76ae3.
Lemma F_932bc : fetch_word AsanUbsan.M.loaded_segments (0x1609dc : word) = Some W_932bc.
Proof. vm_refl. Qed.
Lemma D_932bc : decode_any W_932bc = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_932c0 : bv 32 := 0x00800713.
Lemma F_932c0 : fetch_word AsanUbsan.M.loaded_segments (0x1609e0 : word) = Some W_932c0.
Proof. vm_refl. Qed.
Lemma D_932c0 : decode_any W_932c0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_932c4 : bv 32 := 0x00e66e63.
Lemma F_932c4 : fetch_word AsanUbsan.M.loaded_segments (0x1609e4 : word) = Some W_932c4.
Proof. vm_refl. Qed.
Lemma D_932c4 : decode_any W_932c4 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_932c8 : bv 32 := 0x0005a703.
Lemma F_932c8 : fetch_word AsanUbsan.M.loaded_segments (0x1609e8 : word) = Some W_932c8.
Proof. vm_refl. Qed.
Lemma D_932c8 : decode_any W_932c8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_932cc : bv 32 := 0x0045a783.
Lemma F_932cc : fetch_word AsanUbsan.M.loaded_segments (0x1609ec : word) = Some W_932cc.
Proof. vm_refl. Qed.
Lemma D_932cc : decode_any W_932cc = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_932d0 : bv 32 := 0x00e6a023.
Lemma F_932d0 : fetch_word AsanUbsan.M.loaded_segments (0x1609f0 : word) = Some W_932d0.
Proof. vm_refl. Qed.
Lemma D_932d0 : decode_any W_932d0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_932d4 : bv 32 := 0x00f6a223.
Lemma F_932d4 : fetch_word AsanUbsan.M.loaded_segments (0x1609f4 : word) = Some W_932d4.
Proof. vm_refl. Qed.
Lemma D_932d4 : decode_any W_932d4 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_932d8 : bv 32 := 0x00868693.
Lemma F_932d8 : fetch_word AsanUbsan.M.loaded_segments (0x1609f8 : word) = Some W_932d8.
Proof. vm_refl. Qed.
Lemma D_932d8 : decode_any W_932d8 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_932dc : bv 32 := 0x00858593.
Lemma F_932dc : fetch_word AsanUbsan.M.loaded_segments (0x1609fc : word) = Some W_932dc.
Proof. vm_refl. Qed.
Lemma D_932dc : decode_any W_932dc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_932e0 : bv 32 := 0x00467713.
Lemma F_932e0 : fetch_word AsanUbsan.M.loaded_segments (0x160a00 : word) = Some W_932e0.
Proof. vm_refl. Qed.
Lemma D_932e0 : decode_any W_932e0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_932e4 : bv 32 := 0x24070063.
Lemma F_932e4 : fetch_word AsanUbsan.M.loaded_segments (0x160a04 : word) = Some W_932e4.
Proof. vm_refl. Qed.
Lemma D_932e4 : decode_any W_932e4 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_932e8 : bv 32 := 0x0005a703.
Lemma F_932e8 : fetch_word AsanUbsan.M.loaded_segments (0x160a08 : word) = Some W_932e8.
Proof. vm_refl. Qed.
Lemma D_932e8 : decode_any W_932e8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_932ec : bv 32 := 0x00458593.
Lemma F_932ec : fetch_word AsanUbsan.M.loaded_segments (0x160a0c : word) = Some W_932ec.
Proof. vm_refl. Qed.
Lemma D_932ec : decode_any W_932ec = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_932f0 : bv 32 := 0x00e6a023.
Lemma F_932f0 : fetch_word AsanUbsan.M.loaded_segments (0x160a10 : word) = Some W_932f0.
Proof. vm_refl. Qed.
Lemma D_932f0 : decode_any W_932f0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_932f4 : bv 32 := 0x00468693.
Lemma F_932f4 : fetch_word AsanUbsan.M.loaded_segments (0x160a14 : word) = Some W_932f4.
Proof. vm_refl. Qed.
Lemma D_932f4 : decode_any W_932f4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_932f8 : bv 32 := 0x22c0006f.
Lemma F_932f8 : fetch_word AsanUbsan.M.loaded_segments (0x160a18 : word) = Some W_932f8.
Proof. vm_refl. Qed.
Lemma D_932f8 : decode_any W_932f8 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_932fc : bv 32 := 0x00e68023.
Lemma F_932fc : fetch_word AsanUbsan.M.loaded_segments (0x160a1c : word) = Some W_932fc.
Proof. vm_refl. Qed.
Lemma D_932fc : decode_any W_932fc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93300 : bv 32 := 0x00168693.
Lemma F_93300 : fetch_word AsanUbsan.M.loaded_segments (0x160a20 : word) = Some W_93300.
Proof. vm_refl. Qed.
Lemma D_93300 : decode_any W_93300 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93304 : bv 32 := 0xfff60613.
Lemma F_93304 : fetch_word AsanUbsan.M.loaded_segments (0x160a24 : word) = Some W_93304.
Proof. vm_refl. Qed.
Lemma D_93304 : decode_any W_93304 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93308 : bv 32 := 0x01058593.
Lemma F_93308 : fetch_word AsanUbsan.M.loaded_segments (0x160a28 : word) = Some W_93308.
Proof. vm_refl. Qed.
Lemma D_93308 : decode_any W_93308 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9330c : bv 32 := 0x01200793.
Lemma F_9330c : fetch_word AsanUbsan.M.loaded_segments (0x160a2c : word) = Some W_9330c.
Proof. vm_refl. Qed.
Lemma D_9330c : decode_any W_9330c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_93310 : bv 32 := 0x0087581b.
Lemma F_93310 : fetch_word AsanUbsan.M.loaded_segments (0x160a30 : word) = Some W_93310.
Proof. vm_refl. Qed.
Lemma D_93310 : decode_any W_93310 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93314 : bv 32 := 0xff45a883.
Lemma F_93314 : fetch_word AsanUbsan.M.loaded_segments (0x160a34 : word) = Some W_93314.
Proof. vm_refl. Qed.
Lemma D_93314 : decode_any W_93314 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_93318 : bv 32 := 0xff85a283.
Lemma F_93318 : fetch_word AsanUbsan.M.loaded_segments (0x160a38 : word) = Some W_93318.
Proof. vm_refl. Qed.
Lemma D_93318 : decode_any W_93318 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9331c : bv 32 := 0xffc5a303.
Lemma F_9331c : fetch_word AsanUbsan.M.loaded_segments (0x160a3c : word) = Some W_9331c.
Proof. vm_refl. Qed.
Lemma D_9331c : decode_any W_9331c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_93320 : bv 32 := 0x0005a703.
Lemma F_93320 : fetch_word AsanUbsan.M.loaded_segments (0x160a40 : word) = Some W_93320.
Proof. vm_refl. Qed.
Lemma D_93320 : decode_any W_93320 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93324 : bv 32 := 0x01889393.
Lemma F_93324 : fetch_word AsanUbsan.M.loaded_segments (0x160a44 : word) = Some W_93324.
Proof. vm_refl. Qed.
Lemma D_93324 : decode_any W_93324 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_93328 : bv 32 := 0x0088d89b.
Lemma F_93328 : fetch_word AsanUbsan.M.loaded_segments (0x160a48 : word) = Some W_93328.
Proof. vm_refl. Qed.
Lemma D_93328 : decode_any W_93328 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9332c : bv 32 := 0x0103e833.
Lemma F_9332c : fetch_word AsanUbsan.M.loaded_segments (0x160a4c : word) = Some W_9332c.
Proof. vm_refl. Qed.
Lemma D_9332c : decode_any W_9332c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93330 : bv 32 := 0x01829393.
Lemma F_93330 : fetch_word AsanUbsan.M.loaded_segments (0x160a50 : word) = Some W_93330.
Proof. vm_refl. Qed.
Lemma D_93330 : decode_any W_93330 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_93334 : bv 32 := 0x0082d29b.
Lemma F_93334 : fetch_word AsanUbsan.M.loaded_segments (0x160a54 : word) = Some W_93334.
Proof. vm_refl. Qed.
Lemma D_93334 : decode_any W_93334 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93338 : bv 32 := 0x0113e8b3.
Lemma F_93338 : fetch_word AsanUbsan.M.loaded_segments (0x160a58 : word) = Some W_93338.
Proof. vm_refl. Qed.
Lemma D_93338 : decode_any W_93338 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_9333c : bv 32 := 0x01831393.
Lemma F_9333c : fetch_word AsanUbsan.M.loaded_segments (0x160a5c : word) = Some W_9333c.
Proof. vm_refl. Qed.
Lemma D_9333c : decode_any W_9333c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_93340 : bv 32 := 0x0083531b.
Lemma F_93340 : fetch_word AsanUbsan.M.loaded_segments (0x160a60 : word) = Some W_93340.
Proof. vm_refl. Qed.
Lemma D_93340 : decode_any W_93340 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93344 : bv 32 := 0x0053e2b3.
Lemma F_93344 : fetch_word AsanUbsan.M.loaded_segments (0x160a64 : word) = Some W_93344.
Proof. vm_refl. Qed.
Lemma D_93344 : decode_any W_93344 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_93348 : bv 32 := 0x01871393.
Lemma F_93348 : fetch_word AsanUbsan.M.loaded_segments (0x160a68 : word) = Some W_93348.
Proof. vm_refl. Qed.
Lemma D_93348 : decode_any W_93348 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9334c : bv 32 := 0x0063e333.
Lemma F_9334c : fetch_word AsanUbsan.M.loaded_segments (0x160a6c : word) = Some W_9334c.
Proof. vm_refl. Qed.
Lemma D_9334c : decode_any W_9334c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_93350 : bv 32 := 0xff060613.
Lemma F_93350 : fetch_word AsanUbsan.M.loaded_segments (0x160a70 : word) = Some W_93350.
Proof. vm_refl. Qed.
Lemma D_93350 : decode_any W_93350 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_93354 : bv 32 := 0x0106a023.
Lemma F_93354 : fetch_word AsanUbsan.M.loaded_segments (0x160a74 : word) = Some W_93354.
Proof. vm_refl. Qed.
Lemma D_93354 : decode_any W_93354 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93358 : bv 32 := 0x0116a223.
Lemma F_93358 : fetch_word AsanUbsan.M.loaded_segments (0x160a78 : word) = Some W_93358.
Proof. vm_refl. Qed.
Lemma D_93358 : decode_any W_93358 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9335c : bv 32 := 0x0056a423.
Lemma F_9335c : fetch_word AsanUbsan.M.loaded_segments (0x160a7c : word) = Some W_9335c.
Proof. vm_refl. Qed.
Lemma D_9335c : decode_any W_9335c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93360 : bv 32 := 0x0066a623.
Lemma F_93360 : fetch_word AsanUbsan.M.loaded_segments (0x160a80 : word) = Some W_93360.
Proof. vm_refl. Qed.
Lemma D_93360 : decode_any W_93360 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93364 : bv 32 := 0x01068693.
Lemma F_93364 : fetch_word AsanUbsan.M.loaded_segments (0x160a84 : word) = Some W_93364.
Proof. vm_refl. Qed.
Lemma D_93364 : decode_any W_93364 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93368 : bv 32 := 0x01058593.
Lemma F_93368 : fetch_word AsanUbsan.M.loaded_segments (0x160a88 : word) = Some W_93368.
Proof. vm_refl. Qed.
Lemma D_93368 : decode_any W_93368 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9336c : bv 32 := 0xfac7e2e3.
Lemma F_9336c : fetch_word AsanUbsan.M.loaded_segments (0x160a8c : word) = Some W_9336c.
Proof. vm_refl. Qed.
Lemma D_9336c : decode_any W_9336c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_93370 : bv 32 := 0xff158593.
Lemma F_93370 : fetch_word AsanUbsan.M.loaded_segments (0x160a90 : word) = Some W_93370.
Proof. vm_refl. Qed.
Lemma D_93370 : decode_any W_93370 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_93374 : bv 32 := 0x01000713.
Lemma F_93374 : fetch_word AsanUbsan.M.loaded_segments (0x160a94 : word) = Some W_93374.
Proof. vm_refl. Qed.
Lemma D_93374 : decode_any W_93374 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93378 : bv 32 := 0xe4e666e3.
Lemma F_93378 : fetch_word AsanUbsan.M.loaded_segments (0x160a98 : word) = Some W_93378.
Proof. vm_refl. Qed.
Lemma D_93378 : decode_any W_93378 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_9337c : bv 32 := 0x0940006f.
Lemma F_9337c : fetch_word AsanUbsan.M.loaded_segments (0x160a9c : word) = Some W_9337c.
Proof. vm_refl. Qed.
Lemma D_9337c : decode_any W_9337c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_93380 : bv 32 := 0x00875793.
Lemma F_93380 : fetch_word AsanUbsan.M.loaded_segments (0x160aa0 : word) = Some W_93380.
Proof. vm_refl. Qed.
Lemma D_93380 : decode_any W_93380 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93384 : bv 32 := 0x01075813.
Lemma F_93384 : fetch_word AsanUbsan.M.loaded_segments (0x160aa4 : word) = Some W_93384.
Proof. vm_refl. Qed.
Lemma D_93384 : decode_any W_93384 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93388 : bv 32 := 0xffd60613.
Lemma F_93388 : fetch_word AsanUbsan.M.loaded_segments (0x160aa8 : word) = Some W_93388.
Proof. vm_refl. Qed.
Lemma D_93388 : decode_any W_93388 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_9338c : bv 32 := 0x00e68023.
Lemma F_9338c : fetch_word AsanUbsan.M.loaded_segments (0x160aac : word) = Some W_9338c.
Proof. vm_refl. Qed.
Lemma D_9338c : decode_any W_9338c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93390 : bv 32 := 0x00f680a3.
Lemma F_93390 : fetch_word AsanUbsan.M.loaded_segments (0x160ab0 : word) = Some W_93390.
Proof. vm_refl. Qed.
Lemma D_93390 : decode_any W_93390 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93394 : bv 32 := 0x01068123.
Lemma F_93394 : fetch_word AsanUbsan.M.loaded_segments (0x160ab4 : word) = Some W_93394.
Proof. vm_refl. Qed.
Lemma D_93394 : decode_any W_93394 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93398 : bv 32 := 0x00368693.
Lemma F_93398 : fetch_word AsanUbsan.M.loaded_segments (0x160ab8 : word) = Some W_93398.
Proof. vm_refl. Qed.
Lemma D_93398 : decode_any W_93398 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9339c : bv 32 := 0x01058593.
Lemma F_9339c : fetch_word AsanUbsan.M.loaded_segments (0x160abc : word) = Some W_9339c.
Proof. vm_refl. Qed.
Lemma D_9339c : decode_any W_9339c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_933a0 : bv 32 := 0x01000793.
Lemma F_933a0 : fetch_word AsanUbsan.M.loaded_segments (0x160ac0 : word) = Some W_933a0.
Proof. vm_refl. Qed.
Lemma D_933a0 : decode_any W_933a0 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_933a4 : bv 32 := 0x0187581b.
Lemma F_933a4 : fetch_word AsanUbsan.M.loaded_segments (0x160ac4 : word) = Some W_933a4.
Proof. vm_refl. Qed.
Lemma D_933a4 : decode_any W_933a4 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_933a8 : bv 32 := 0xff45a883.
Lemma F_933a8 : fetch_word AsanUbsan.M.loaded_segments (0x160ac8 : word) = Some W_933a8.
Proof. vm_refl. Qed.
Lemma D_933a8 : decode_any W_933a8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_933ac : bv 32 := 0xff85a283.
Lemma F_933ac : fetch_word AsanUbsan.M.loaded_segments (0x160acc : word) = Some W_933ac.
Proof. vm_refl. Qed.
Lemma D_933ac : decode_any W_933ac = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_933b0 : bv 32 := 0xffc5a303.
Lemma F_933b0 : fetch_word AsanUbsan.M.loaded_segments (0x160ad0 : word) = Some W_933b0.
Proof. vm_refl. Qed.
Lemma D_933b0 : decode_any W_933b0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_933b4 : bv 32 := 0x0005a703.
Lemma F_933b4 : fetch_word AsanUbsan.M.loaded_segments (0x160ad4 : word) = Some W_933b4.
Proof. vm_refl. Qed.
Lemma D_933b4 : decode_any W_933b4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_933b8 : bv 32 := 0x00889393.
Lemma F_933b8 : fetch_word AsanUbsan.M.loaded_segments (0x160ad8 : word) = Some W_933b8.
Proof. vm_refl. Qed.
Lemma D_933b8 : decode_any W_933b8 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_933bc : bv 32 := 0x0188d89b.
Lemma F_933bc : fetch_word AsanUbsan.M.loaded_segments (0x160adc : word) = Some W_933bc.
Proof. vm_refl. Qed.
Lemma D_933bc : decode_any W_933bc = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_933c0 : bv 32 := 0x0103e833.
Lemma F_933c0 : fetch_word AsanUbsan.M.loaded_segments (0x160ae0 : word) = Some W_933c0.
Proof. vm_refl. Qed.
Lemma D_933c0 : decode_any W_933c0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_933c4 : bv 32 := 0x00829393.
Lemma F_933c4 : fetch_word AsanUbsan.M.loaded_segments (0x160ae4 : word) = Some W_933c4.
Proof. vm_refl. Qed.
Lemma D_933c4 : decode_any W_933c4 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_933c8 : bv 32 := 0x0182d29b.
Lemma F_933c8 : fetch_word AsanUbsan.M.loaded_segments (0x160ae8 : word) = Some W_933c8.
Proof. vm_refl. Qed.
Lemma D_933c8 : decode_any W_933c8 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_933cc : bv 32 := 0x0113e8b3.
Lemma F_933cc : fetch_word AsanUbsan.M.loaded_segments (0x160aec : word) = Some W_933cc.
Proof. vm_refl. Qed.
Lemma D_933cc : decode_any W_933cc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_933d0 : bv 32 := 0x00831393.
Lemma F_933d0 : fetch_word AsanUbsan.M.loaded_segments (0x160af0 : word) = Some W_933d0.
Proof. vm_refl. Qed.
Lemma D_933d0 : decode_any W_933d0 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_933d4 : bv 32 := 0x0183531b.
Lemma F_933d4 : fetch_word AsanUbsan.M.loaded_segments (0x160af4 : word) = Some W_933d4.
Proof. vm_refl. Qed.
Lemma D_933d4 : decode_any W_933d4 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_933d8 : bv 32 := 0x0053e2b3.
Lemma F_933d8 : fetch_word AsanUbsan.M.loaded_segments (0x160af8 : word) = Some W_933d8.
Proof. vm_refl. Qed.
Lemma D_933d8 : decode_any W_933d8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_933dc : bv 32 := 0x00871393.
Lemma F_933dc : fetch_word AsanUbsan.M.loaded_segments (0x160afc : word) = Some W_933dc.
Proof. vm_refl. Qed.
Lemma D_933dc : decode_any W_933dc = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_933e0 : bv 32 := 0x0063e333.
Lemma F_933e0 : fetch_word AsanUbsan.M.loaded_segments (0x160b00 : word) = Some W_933e0.
Proof. vm_refl. Qed.
Lemma D_933e0 : decode_any W_933e0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_933e4 : bv 32 := 0xff060613.
Lemma F_933e4 : fetch_word AsanUbsan.M.loaded_segments (0x160b04 : word) = Some W_933e4.
Proof. vm_refl. Qed.
Lemma D_933e4 : decode_any W_933e4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_933e8 : bv 32 := 0x0106a023.
Lemma F_933e8 : fetch_word AsanUbsan.M.loaded_segments (0x160b08 : word) = Some W_933e8.
Proof. vm_refl. Qed.
Lemma D_933e8 : decode_any W_933e8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_933ec : bv 32 := 0x0116a223.
Lemma F_933ec : fetch_word AsanUbsan.M.loaded_segments (0x160b0c : word) = Some W_933ec.
Proof. vm_refl. Qed.
Lemma D_933ec : decode_any W_933ec = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_933f0 : bv 32 := 0x0056a423.
Lemma F_933f0 : fetch_word AsanUbsan.M.loaded_segments (0x160b10 : word) = Some W_933f0.
Proof. vm_refl. Qed.
Lemma D_933f0 : decode_any W_933f0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_933f4 : bv 32 := 0x0066a623.
Lemma F_933f4 : fetch_word AsanUbsan.M.loaded_segments (0x160b14 : word) = Some W_933f4.
Proof. vm_refl. Qed.
Lemma D_933f4 : decode_any W_933f4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_933f8 : bv 32 := 0x01068693.
Lemma F_933f8 : fetch_word AsanUbsan.M.loaded_segments (0x160b18 : word) = Some W_933f8.
Proof. vm_refl. Qed.
Lemma D_933f8 : decode_any W_933f8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_933fc : bv 32 := 0x01058593.
Lemma F_933fc : fetch_word AsanUbsan.M.loaded_segments (0x160b1c : word) = Some W_933fc.
Proof. vm_refl. Qed.
Lemma D_933fc : decode_any W_933fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93400 : bv 32 := 0xfac7e2e3.
Lemma F_93400 : fetch_word AsanUbsan.M.loaded_segments (0x160b20 : word) = Some W_93400.
Proof. vm_refl. Qed.
Lemma D_93400 : decode_any W_93400 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_93404 : bv 32 := 0xff358593.
Lemma F_93404 : fetch_word AsanUbsan.M.loaded_segments (0x160b24 : word) = Some W_93404.
Proof. vm_refl. Qed.
Lemma D_93404 : decode_any W_93404 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_93408 : bv 32 := 0x01000713.
Lemma F_93408 : fetch_word AsanUbsan.M.loaded_segments (0x160b28 : word) = Some W_93408.
Proof. vm_refl. Qed.
Lemma D_93408 : decode_any W_93408 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9340c : bv 32 := 0xdae66ce3.
Lemma F_9340c : fetch_word AsanUbsan.M.loaded_segments (0x160b2c : word) = Some W_9340c.
Proof. vm_refl. Qed.
Lemma D_9340c : decode_any W_9340c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_93410 : bv 32 := 0x0005c703.
Lemma F_93410 : fetch_word AsanUbsan.M.loaded_segments (0x160b30 : word) = Some W_93410.
Proof. vm_refl. Qed.
Lemma D_93410 : decode_any W_93410 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93414 : bv 32 := 0x0015c783.
Lemma F_93414 : fetch_word AsanUbsan.M.loaded_segments (0x160b34 : word) = Some W_93414.
Proof. vm_refl. Qed.
Lemma D_93414 : decode_any W_93414 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93418 : bv 32 := 0x0025c803.
Lemma F_93418 : fetch_word AsanUbsan.M.loaded_segments (0x160b38 : word) = Some W_93418.
Proof. vm_refl. Qed.
Lemma D_93418 : decode_any W_93418 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9341c : bv 32 := 0x0035c883.
Lemma F_9341c : fetch_word AsanUbsan.M.loaded_segments (0x160b3c : word) = Some W_9341c.
Proof. vm_refl. Qed.
Lemma D_9341c : decode_any W_9341c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_93420 : bv 32 := 0x0045c283.
Lemma F_93420 : fetch_word AsanUbsan.M.loaded_segments (0x160b40 : word) = Some W_93420.
Proof. vm_refl. Qed.
Lemma D_93420 : decode_any W_93420 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93424 : bv 32 := 0x0055c303.
Lemma F_93424 : fetch_word AsanUbsan.M.loaded_segments (0x160b44 : word) = Some W_93424.
Proof. vm_refl. Qed.
Lemma D_93424 : decode_any W_93424 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_93428 : bv 32 := 0x0065c383.
Lemma F_93428 : fetch_word AsanUbsan.M.loaded_segments (0x160b48 : word) = Some W_93428.
Proof. vm_refl. Qed.
Lemma D_93428 : decode_any W_93428 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_9342c : bv 32 := 0x0075ce03.
Lemma F_9342c : fetch_word AsanUbsan.M.loaded_segments (0x160b4c : word) = Some W_9342c.
Proof. vm_refl. Qed.
Lemma D_9342c : decode_any W_9342c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_93430 : bv 32 := 0x00e68023.
Lemma F_93430 : fetch_word AsanUbsan.M.loaded_segments (0x160b50 : word) = Some W_93430.
Proof. vm_refl. Qed.
Lemma D_93430 : decode_any W_93430 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93434 : bv 32 := 0x00f680a3.
Lemma F_93434 : fetch_word AsanUbsan.M.loaded_segments (0x160b54 : word) = Some W_93434.
Proof. vm_refl. Qed.
Lemma D_93434 : decode_any W_93434 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93438 : bv 32 := 0x01068123.
Lemma F_93438 : fetch_word AsanUbsan.M.loaded_segments (0x160b58 : word) = Some W_93438.
Proof. vm_refl. Qed.
Lemma D_93438 : decode_any W_93438 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9343c : bv 32 := 0x011681a3.
Lemma F_9343c : fetch_word AsanUbsan.M.loaded_segments (0x160b5c : word) = Some W_9343c.
Proof. vm_refl. Qed.
Lemma D_9343c : decode_any W_9343c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_93440 : bv 32 := 0x0085c703.
Lemma F_93440 : fetch_word AsanUbsan.M.loaded_segments (0x160b60 : word) = Some W_93440.
Proof. vm_refl. Qed.
Lemma D_93440 : decode_any W_93440 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93444 : bv 32 := 0x0095c783.
Lemma F_93444 : fetch_word AsanUbsan.M.loaded_segments (0x160b64 : word) = Some W_93444.
Proof. vm_refl. Qed.
Lemma D_93444 : decode_any W_93444 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_93448 : bv 32 := 0x00a5c803.
Lemma F_93448 : fetch_word AsanUbsan.M.loaded_segments (0x160b68 : word) = Some W_93448.
Proof. vm_refl. Qed.
Lemma D_93448 : decode_any W_93448 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9344c : bv 32 := 0x00b5c883.
Lemma F_9344c : fetch_word AsanUbsan.M.loaded_segments (0x160b6c : word) = Some W_9344c.
Proof. vm_refl. Qed.
Lemma D_9344c : decode_any W_9344c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93450 : bv 32 := 0x00568223.
Lemma F_93450 : fetch_word AsanUbsan.M.loaded_segments (0x160b70 : word) = Some W_93450.
Proof. vm_refl. Qed.
Lemma D_93450 : decode_any W_93450 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93454 : bv 32 := 0x006682a3.
Lemma F_93454 : fetch_word AsanUbsan.M.loaded_segments (0x160b74 : word) = Some W_93454.
Proof. vm_refl. Qed.
Lemma D_93454 : decode_any W_93454 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_93458 : bv 32 := 0x00768323.
Lemma F_93458 : fetch_word AsanUbsan.M.loaded_segments (0x160b78 : word) = Some W_93458.
Proof. vm_refl. Qed.
Lemma D_93458 : decode_any W_93458 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_9345c : bv 32 := 0x01c683a3.
Lemma F_9345c : fetch_word AsanUbsan.M.loaded_segments (0x160b7c : word) = Some W_9345c.
Proof. vm_refl. Qed.
Lemma D_9345c : decode_any W_9345c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_93460 : bv 32 := 0x00c5c283.
Lemma F_93460 : fetch_word AsanUbsan.M.loaded_segments (0x160b80 : word) = Some W_93460.
Proof. vm_refl. Qed.
Lemma D_93460 : decode_any W_93460 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93464 : bv 32 := 0x00d5c303.
Lemma F_93464 : fetch_word AsanUbsan.M.loaded_segments (0x160b84 : word) = Some W_93464.
Proof. vm_refl. Qed.
Lemma D_93464 : decode_any W_93464 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_93468 : bv 32 := 0x00e5c383.
Lemma F_93468 : fetch_word AsanUbsan.M.loaded_segments (0x160b88 : word) = Some W_93468.
Proof. vm_refl. Qed.
Lemma D_93468 : decode_any W_93468 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_9346c : bv 32 := 0x00f5ce03.
Lemma F_9346c : fetch_word AsanUbsan.M.loaded_segments (0x160b8c : word) = Some W_9346c.
Proof. vm_refl. Qed.
Lemma D_9346c : decode_any W_9346c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93470 : bv 32 := 0x01058593.
Lemma F_93470 : fetch_word AsanUbsan.M.loaded_segments (0x160b90 : word) = Some W_93470.
Proof. vm_refl. Qed.
Lemma D_93470 : decode_any W_93470 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93474 : bv 32 := 0x00e68423.
Lemma F_93474 : fetch_word AsanUbsan.M.loaded_segments (0x160b94 : word) = Some W_93474.
Proof. vm_refl. Qed.
Lemma D_93474 : decode_any W_93474 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93478 : bv 32 := 0x00f684a3.
Lemma F_93478 : fetch_word AsanUbsan.M.loaded_segments (0x160b98 : word) = Some W_93478.
Proof. vm_refl. Qed.
Lemma D_93478 : decode_any W_93478 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9347c : bv 32 := 0x01068523.
Lemma F_9347c : fetch_word AsanUbsan.M.loaded_segments (0x160b9c : word) = Some W_9347c.
Proof. vm_refl. Qed.
Lemma D_9347c : decode_any W_9347c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93480 : bv 32 := 0x011685a3.
Lemma F_93480 : fetch_word AsanUbsan.M.loaded_segments (0x160ba0 : word) = Some W_93480.
Proof. vm_refl. Qed.
Lemma D_93480 : decode_any W_93480 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93484 : bv 32 := 0x01068713.
Lemma F_93484 : fetch_word AsanUbsan.M.loaded_segments (0x160ba4 : word) = Some W_93484.
Proof. vm_refl. Qed.
Lemma D_93484 : decode_any W_93484 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93488 : bv 32 := 0x00568623.
Lemma F_93488 : fetch_word AsanUbsan.M.loaded_segments (0x160ba8 : word) = Some W_93488.
Proof. vm_refl. Qed.
Lemma D_93488 : decode_any W_93488 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9348c : bv 32 := 0x006686a3.
Lemma F_9348c : fetch_word AsanUbsan.M.loaded_segments (0x160bac : word) = Some W_9348c.
Proof. vm_refl. Qed.
Lemma D_9348c : decode_any W_9348c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_93490 : bv 32 := 0x00768723.
Lemma F_93490 : fetch_word AsanUbsan.M.loaded_segments (0x160bb0 : word) = Some W_93490.
Proof. vm_refl. Qed.
Lemma D_93490 : decode_any W_93490 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_93494 : bv 32 := 0x01c687a3.
Lemma F_93494 : fetch_word AsanUbsan.M.loaded_segments (0x160bb4 : word) = Some W_93494.
Proof. vm_refl. Qed.
Lemma D_93494 : decode_any W_93494 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93498 : bv 32 := 0x00070693.
Lemma F_93498 : fetch_word AsanUbsan.M.loaded_segments (0x160bb8 : word) = Some W_93498.
Proof. vm_refl. Qed.
Lemma D_93498 : decode_any W_93498 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9349c : bv 32 := 0x00867713.
Lemma F_9349c : fetch_word AsanUbsan.M.loaded_segments (0x160bbc : word) = Some W_9349c.
Proof. vm_refl. Qed.
Lemma D_9349c : decode_any W_9349c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_934a0 : bv 32 := 0xd20706e3.
Lemma F_934a0 : fetch_word AsanUbsan.M.loaded_segments (0x160bc0 : word) = Some W_934a0.
Proof. vm_refl. Qed.
Lemma D_934a0 : decode_any W_934a0 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_934a4 : bv 32 := 0x0005c703.
Lemma F_934a4 : fetch_word AsanUbsan.M.loaded_segments (0x160bc4 : word) = Some W_934a4.
Proof. vm_refl. Qed.
Lemma D_934a4 : decode_any W_934a4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_934a8 : bv 32 := 0x0015c783.
Lemma F_934a8 : fetch_word AsanUbsan.M.loaded_segments (0x160bc8 : word) = Some W_934a8.
Proof. vm_refl. Qed.
Lemma D_934a8 : decode_any W_934a8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_934ac : bv 32 := 0x0025c803.
Lemma F_934ac : fetch_word AsanUbsan.M.loaded_segments (0x160bcc : word) = Some W_934ac.
Proof. vm_refl. Qed.
Lemma D_934ac : decode_any W_934ac = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_934b0 : bv 32 := 0x0035c883.
Lemma F_934b0 : fetch_word AsanUbsan.M.loaded_segments (0x160bd0 : word) = Some W_934b0.
Proof. vm_refl. Qed.
Lemma D_934b0 : decode_any W_934b0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_934b4 : bv 32 := 0x0045c283.
Lemma F_934b4 : fetch_word AsanUbsan.M.loaded_segments (0x160bd4 : word) = Some W_934b4.
Proof. vm_refl. Qed.
Lemma D_934b4 : decode_any W_934b4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_934b8 : bv 32 := 0x0055c303.
Lemma F_934b8 : fetch_word AsanUbsan.M.loaded_segments (0x160bd8 : word) = Some W_934b8.
Proof. vm_refl. Qed.
Lemma D_934b8 : decode_any W_934b8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_934bc : bv 32 := 0x0065c383.
Lemma F_934bc : fetch_word AsanUbsan.M.loaded_segments (0x160bdc : word) = Some W_934bc.
Proof. vm_refl. Qed.
Lemma D_934bc : decode_any W_934bc = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_934c0 : bv 32 := 0x0075ce03.
Lemma F_934c0 : fetch_word AsanUbsan.M.loaded_segments (0x160be0 : word) = Some W_934c0.
Proof. vm_refl. Qed.
Lemma D_934c0 : decode_any W_934c0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_934c4 : bv 32 := 0x00858593.
Lemma F_934c4 : fetch_word AsanUbsan.M.loaded_segments (0x160be4 : word) = Some W_934c4.
Proof. vm_refl. Qed.
Lemma D_934c4 : decode_any W_934c4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_934c8 : bv 32 := 0x00e68023.
Lemma F_934c8 : fetch_word AsanUbsan.M.loaded_segments (0x160be8 : word) = Some W_934c8.
Proof. vm_refl. Qed.
Lemma D_934c8 : decode_any W_934c8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_934cc : bv 32 := 0x00f680a3.
Lemma F_934cc : fetch_word AsanUbsan.M.loaded_segments (0x160bec : word) = Some W_934cc.
Proof. vm_refl. Qed.
Lemma D_934cc : decode_any W_934cc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_934d0 : bv 32 := 0x01068123.
Lemma F_934d0 : fetch_word AsanUbsan.M.loaded_segments (0x160bf0 : word) = Some W_934d0.
Proof. vm_refl. Qed.
Lemma D_934d0 : decode_any W_934d0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_934d4 : bv 32 := 0x011681a3.
Lemma F_934d4 : fetch_word AsanUbsan.M.loaded_segments (0x160bf4 : word) = Some W_934d4.
Proof. vm_refl. Qed.
Lemma D_934d4 : decode_any W_934d4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_934d8 : bv 32 := 0x00868713.
Lemma F_934d8 : fetch_word AsanUbsan.M.loaded_segments (0x160bf8 : word) = Some W_934d8.
Proof. vm_refl. Qed.
Lemma D_934d8 : decode_any W_934d8 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_934dc : bv 32 := 0x00568223.
Lemma F_934dc : fetch_word AsanUbsan.M.loaded_segments (0x160bfc : word) = Some W_934dc.
Proof. vm_refl. Qed.
Lemma D_934dc : decode_any W_934dc = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_934e0 : bv 32 := 0x006682a3.
Lemma F_934e0 : fetch_word AsanUbsan.M.loaded_segments (0x160c00 : word) = Some W_934e0.
Proof. vm_refl. Qed.
Lemma D_934e0 : decode_any W_934e0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_934e4 : bv 32 := 0x00768323.
Lemma F_934e4 : fetch_word AsanUbsan.M.loaded_segments (0x160c04 : word) = Some W_934e4.
Proof. vm_refl. Qed.
Lemma D_934e4 : decode_any W_934e4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_934e8 : bv 32 := 0x01c683a3.
Lemma F_934e8 : fetch_word AsanUbsan.M.loaded_segments (0x160c08 : word) = Some W_934e8.
Proof. vm_refl. Qed.
Lemma D_934e8 : decode_any W_934e8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_934ec : bv 32 := 0x00070693.
Lemma F_934ec : fetch_word AsanUbsan.M.loaded_segments (0x160c0c : word) = Some W_934ec.
Proof. vm_refl. Qed.
Lemma D_934ec : decode_any W_934ec = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_934f0 : bv 32 := 0x00467713.
Lemma F_934f0 : fetch_word AsanUbsan.M.loaded_segments (0x160c10 : word) = Some W_934f0.
Proof. vm_refl. Qed.
Lemma D_934f0 : decode_any W_934f0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_934f4 : bv 32 := 0x02070863.
Lemma F_934f4 : fetch_word AsanUbsan.M.loaded_segments (0x160c14 : word) = Some W_934f4.
Proof. vm_refl. Qed.
Lemma D_934f4 : decode_any W_934f4 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_934f8 : bv 32 := 0x0005c703.
Lemma F_934f8 : fetch_word AsanUbsan.M.loaded_segments (0x160c18 : word) = Some W_934f8.
Proof. vm_refl. Qed.
Lemma D_934f8 : decode_any W_934f8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_934fc : bv 32 := 0x0015c783.
Lemma F_934fc : fetch_word AsanUbsan.M.loaded_segments (0x160c1c : word) = Some W_934fc.
Proof. vm_refl. Qed.
Lemma D_934fc : decode_any W_934fc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93500 : bv 32 := 0x0025c803.
Lemma F_93500 : fetch_word AsanUbsan.M.loaded_segments (0x160c20 : word) = Some W_93500.
Proof. vm_refl. Qed.
Lemma D_93500 : decode_any W_93500 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93504 : bv 32 := 0x0035c883.
Lemma F_93504 : fetch_word AsanUbsan.M.loaded_segments (0x160c24 : word) = Some W_93504.
Proof. vm_refl. Qed.
Lemma D_93504 : decode_any W_93504 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_93508 : bv 32 := 0x00458593.
Lemma F_93508 : fetch_word AsanUbsan.M.loaded_segments (0x160c28 : word) = Some W_93508.
Proof. vm_refl. Qed.
Lemma D_93508 : decode_any W_93508 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9350c : bv 32 := 0x00468293.
Lemma F_9350c : fetch_word AsanUbsan.M.loaded_segments (0x160c2c : word) = Some W_9350c.
Proof. vm_refl. Qed.
Lemma D_9350c : decode_any W_9350c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93510 : bv 32 := 0x00e68023.
Lemma F_93510 : fetch_word AsanUbsan.M.loaded_segments (0x160c30 : word) = Some W_93510.
Proof. vm_refl. Qed.
Lemma D_93510 : decode_any W_93510 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93514 : bv 32 := 0x00f680a3.
Lemma F_93514 : fetch_word AsanUbsan.M.loaded_segments (0x160c34 : word) = Some W_93514.
Proof. vm_refl. Qed.
Lemma D_93514 : decode_any W_93514 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93518 : bv 32 := 0x01068123.
Lemma F_93518 : fetch_word AsanUbsan.M.loaded_segments (0x160c38 : word) = Some W_93518.
Proof. vm_refl. Qed.
Lemma D_93518 : decode_any W_93518 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9351c : bv 32 := 0x011681a3.
Lemma F_9351c : fetch_word AsanUbsan.M.loaded_segments (0x160c3c : word) = Some W_9351c.
Proof. vm_refl. Qed.
Lemma D_9351c : decode_any W_9351c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_93520 : bv 32 := 0x00028693.
Lemma F_93520 : fetch_word AsanUbsan.M.loaded_segments (0x160c40 : word) = Some W_93520.
Proof. vm_refl. Qed.
Lemma D_93520 : decode_any W_93520 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93524 : bv 32 := 0x00267713.
Lemma F_93524 : fetch_word AsanUbsan.M.loaded_segments (0x160c44 : word) = Some W_93524.
Proof. vm_refl. Qed.
Lemma D_93524 : decode_any W_93524 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93528 : bv 32 := 0x00071863.
Lemma F_93528 : fetch_word AsanUbsan.M.loaded_segments (0x160c48 : word) = Some W_93528.
Proof. vm_refl. Qed.
Lemma D_93528 : decode_any W_93528 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9352c : bv 32 := 0x00167613.
Lemma F_9352c : fetch_word AsanUbsan.M.loaded_segments (0x160c4c : word) = Some W_9352c.
Proof. vm_refl. Qed.
Lemma D_9352c : decode_any W_9352c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93530 : bv 32 := 0x02061663.
Lemma F_93530 : fetch_word AsanUbsan.M.loaded_segments (0x160c50 : word) = Some W_93530.
Proof. vm_refl. Qed.
Lemma D_93530 : decode_any W_93530 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_93534 : bv 32 := 0x00008067.
Lemma F_93534 : fetch_word AsanUbsan.M.loaded_segments (0x160c54 : word) = Some W_93534.
Proof. vm_refl. Qed.
Lemma D_93534 : decode_any W_93534 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93538 : bv 32 := 0x0005c703.
Lemma F_93538 : fetch_word AsanUbsan.M.loaded_segments (0x160c58 : word) = Some W_93538.
Proof. vm_refl. Qed.
Lemma D_93538 : decode_any W_93538 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9353c : bv 32 := 0x0015c783.
Lemma F_9353c : fetch_word AsanUbsan.M.loaded_segments (0x160c5c : word) = Some W_9353c.
Proof. vm_refl. Qed.
Lemma D_9353c : decode_any W_9353c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93540 : bv 32 := 0x00258593.
Lemma F_93540 : fetch_word AsanUbsan.M.loaded_segments (0x160c60 : word) = Some W_93540.
Proof. vm_refl. Qed.
Lemma D_93540 : decode_any W_93540 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93544 : bv 32 := 0x00268813.
Lemma F_93544 : fetch_word AsanUbsan.M.loaded_segments (0x160c64 : word) = Some W_93544.
Proof. vm_refl. Qed.
Lemma D_93544 : decode_any W_93544 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93548 : bv 32 := 0x00e68023.
Lemma F_93548 : fetch_word AsanUbsan.M.loaded_segments (0x160c68 : word) = Some W_93548.
Proof. vm_refl. Qed.
Lemma D_93548 : decode_any W_93548 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9354c : bv 32 := 0x00f680a3.
Lemma F_9354c : fetch_word AsanUbsan.M.loaded_segments (0x160c6c : word) = Some W_9354c.
Proof. vm_refl. Qed.
Lemma D_9354c : decode_any W_9354c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93550 : bv 32 := 0x00080693.
Lemma F_93550 : fetch_word AsanUbsan.M.loaded_segments (0x160c70 : word) = Some W_93550.
Proof. vm_refl. Qed.
Lemma D_93550 : decode_any W_93550 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93554 : bv 32 := 0x00167613.
Lemma F_93554 : fetch_word AsanUbsan.M.loaded_segments (0x160c74 : word) = Some W_93554.
Proof. vm_refl. Qed.
Lemma D_93554 : decode_any W_93554 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93558 : bv 32 := 0xfc060ee3.
Lemma F_93558 : fetch_word AsanUbsan.M.loaded_segments (0x160c78 : word) = Some W_93558.
Proof. vm_refl. Qed.
Lemma D_93558 : decode_any W_93558 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_9355c : bv 32 := 0x0005c583.
Lemma F_9355c : fetch_word AsanUbsan.M.loaded_segments (0x160c7c : word) = Some W_9355c.
Proof. vm_refl. Qed.
Lemma D_9355c : decode_any W_9355c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93560 : bv 32 := 0x00b68023.
Lemma F_93560 : fetch_word AsanUbsan.M.loaded_segments (0x160c80 : word) = Some W_93560.
Proof. vm_refl. Qed.
Lemma D_93560 : decode_any W_93560 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93564 : bv 32 := 0x00008067.
Lemma F_93564 : fetch_word AsanUbsan.M.loaded_segments (0x160c84 : word) = Some W_93564.
Proof. vm_refl. Qed.
Lemma D_93564 : decode_any W_93564 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
