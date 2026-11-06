(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_78138 : bv 32 := 0x02913423.
Lemma F_78138 : fetch_word BSEGS_I (0x78138 : word) = Some W_78138.
Proof. vm_refl. Qed.
Lemma D_78138 : decode_any W_78138 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7813c : bv 32 := 0x03213023.
Lemma F_7813c : fetch_word BSEGS_I (0x7813c : word) = Some W_7813c.
Proof. vm_refl. Qed.
Lemma D_7813c : decode_any W_7813c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78140 : bv 32 := 0x01313c23.
Lemma F_78140 : fetch_word BSEGS_I (0x78140 : word) = Some W_78140.
Proof. vm_refl. Qed.
Lemma D_78140 : decode_any W_78140 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78144 : bv 32 := 0x01413823.
Lemma F_78144 : fetch_word BSEGS_I (0x78144 : word) = Some W_78144.
Proof. vm_refl. Qed.
Lemma D_78144 : decode_any W_78144 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78148 : bv 32 := 0x01513423.
Lemma F_78148 : fetch_word BSEGS_I (0x78148 : word) = Some W_78148.
Proof. vm_refl. Qed.
Lemma D_78148 : decode_any W_78148 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7814c : bv 32 := 0x14058c63.
Lemma F_7814c : fetch_word BSEGS_I (0x7814c : word) = Some W_7814c.
Proof. vm_refl. Qed.
Lemma D_7814c : decode_any W_7814c = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78150 : bv 32 := 0x00058493.
Lemma F_78150 : fetch_word BSEGS_I (0x78150 : word) = Some W_78150.
Proof. vm_refl. Qed.
Lemma D_78150 : decode_any W_78150 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78154 : bv 32 := 0x00050413.
Lemma F_78154 : fetch_word BSEGS_I (0x78154 : word) = Some W_78154.
Proof. vm_refl. Qed.
Lemma D_78154 : decode_any W_78154 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78158 : bv 32 := 0x000b2517.
Lemma F_78158 : fetch_word BSEGS_I (0x78158 : word) = Some W_78158.
Proof. vm_refl. Qed.
Lemma D_78158 : decode_any W_78158 = Some (Auipc 10 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7815c : bv 32 := 0x22853a83.
Lemma F_7815c : fetch_word BSEGS_I (0x7815c : word) = Some W_7815c.
Proof. vm_refl. Qed.
Lemma D_7815c : decode_any W_7815c = Some (Load SZ8 true 21 10 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78160 : bv 32 := 0x000ab583.
Lemma F_78160 : fetch_word BSEGS_I (0x78160 : word) = Some W_78160.
Proof. vm_refl. Qed.
Lemma D_78160 : decode_any W_78160 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78164 : bv 32 := 0xfff58513.
Lemma F_78164 : fetch_word BSEGS_I (0x78164 : word) = Some W_78164.
Proof. vm_refl. Qed.
Lemma D_78164 : decode_any W_78164 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78168 : bv 32 := 0x00a5b633.
Lemma F_78168 : fetch_word BSEGS_I (0x78168 : word) = Some W_78168.
Proof. vm_refl. Qed.
Lemma D_78168 : decode_any W_78168 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7816c : bv 32 := 0xfff60613.
Lemma F_7816c : fetch_word BSEGS_I (0x7816c : word) = Some W_7816c.
Proof. vm_refl. Qed.
Lemma D_7816c : decode_any W_7816c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78170 : bv 32 := 0x00a67633.
Lemma F_78170 : fetch_word BSEGS_I (0x78170 : word) = Some W_78170.
Proof. vm_refl. Qed.
Lemma D_78170 : decode_any W_78170 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78174 : bv 32 := 0x04867263.
Lemma F_78174 : fetch_word BSEGS_I (0x78174 : word) = Some W_78174.
Proof. vm_refl. Qed.
Lemma D_78174 : decode_any W_78174 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78178 : bv 32 := 0x000b2697.
Lemma F_78178 : fetch_word BSEGS_I (0x78178 : word) = Some W_78178.
Proof. vm_refl. Qed.
Lemma D_78178 : decode_any W_78178 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7817c : bv 32 := 0x2106b683.
Lemma F_7817c : fetch_word BSEGS_I (0x7817c : word) = Some W_7817c.
Proof. vm_refl. Qed.
Lemma D_7817c : decode_any W_7817c = Some (Load SZ8 true 13 13 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78180 : bv 32 := 0x000b2717.
Lemma F_78180 : fetch_word BSEGS_I (0x78180 : word) = Some W_78180.
Proof. vm_refl. Qed.
Lemma D_78180 : decode_any W_78180 = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78184 : bv 32 := 0x21073703.
Lemma F_78184 : fetch_word BSEGS_I (0x78184 : word) = Some W_78184.
Proof. vm_refl. Qed.
Lemma D_78184 : decode_any W_78184 = Some (Load SZ8 true 14 14 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78188 : bv 32 := 0x0006b803.
Lemma F_78188 : fetch_word BSEGS_I (0x78188 : word) = Some W_78188.
Proof. vm_refl. Qed.
Lemma D_78188 : decode_any W_78188 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7818c : bv 32 := 0x00073683.
Lemma F_7818c : fetch_word BSEGS_I (0x7818c : word) = Some W_7818c.
Proof. vm_refl. Qed.
Lemma D_7818c : decode_any W_7818c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78190 : bv 32 := 0xfff80793.
Lemma F_78190 : fetch_word BSEGS_I (0x78190 : word) = Some W_78190.
Proof. vm_refl. Qed.
Lemma D_78190 : decode_any W_78190 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78194 : bv 32 := 0x0087f463.
Lemma F_78194 : fetch_word BSEGS_I (0x78194 : word) = Some W_78194.
Proof. vm_refl. Qed.
Lemma D_78194 : decode_any W_78194 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78198 : bv 32 := 0x0286f063.
Lemma F_78198 : fetch_word BSEGS_I (0x78198 : word) = Some W_78198.
Proof. vm_refl. Qed.
Lemma D_78198 : decode_any W_78198 = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7819c : bv 32 := 0x000b2717.
Lemma F_7819c : fetch_word BSEGS_I (0x7819c : word) = Some W_7819c.
Proof. vm_refl. Qed.
Lemma D_7819c : decode_any W_7819c = Some (Auipc 14 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a0 : bv 32 := 0x1fc73703.
Lemma F_781a0 : fetch_word BSEGS_I (0x781a0 : word) = Some W_781a0.
Proof. vm_refl. Qed.
Lemma D_781a0 : decode_any W_781a0 = Some (Load SZ8 true 14 14 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a4 : bv 32 := 0x00073283.
Lemma F_781a4 : fetch_word BSEGS_I (0x781a4 : word) = Some W_781a4.
Proof. vm_refl. Qed.
Lemma D_781a4 : decode_any W_781a4 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a8 : bv 32 := 0x0032d713.
Lemma F_781a8 : fetch_word BSEGS_I (0x781a8 : word) = Some W_781a8.
Proof. vm_refl. Qed.
Lemma D_781a8 : decode_any W_781a8 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781ac : bv 32 := 0x00b708b3.
Lemma F_781ac : fetch_word BSEGS_I (0x781ac : word) = Some W_781ac.
Proof. vm_refl. Qed.
Lemma D_781ac : decode_any W_781ac = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b0 : bv 32 := 0x1282e063.
Lemma F_781b0 : fetch_word BSEGS_I (0x781b0 : word) = Some W_781b0.
Proof. vm_refl. Qed.
Lemma D_781b0 : decode_any W_781b0 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b4 : bv 32 := 0x1088fe63.
Lemma F_781b4 : fetch_word BSEGS_I (0x781b4 : word) = Some W_781b4.
Proof. vm_refl. Qed.
Lemma D_781b4 : decode_any W_781b4 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b8 : bv 32 := 0x00848933.
Lemma F_781b8 : fetch_word BSEGS_I (0x781b8 : word) = Some W_781b8.
Proof. vm_refl. Qed.
Lemma D_781b8 : decode_any W_781b8 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781bc : bv 32 := 0x05267263.
Lemma F_781bc : fetch_word BSEGS_I (0x781bc : word) = Some W_781bc.
Proof. vm_refl. Qed.
Lemma D_781bc : decode_any W_781bc = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c0 : bv 32 := 0x000b2617.
Lemma F_781c0 : fetch_word BSEGS_I (0x781c0 : word) = Some W_781c0.
Proof. vm_refl. Qed.
Lemma D_781c0 : decode_any W_781c0 = Some (Auipc 12 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c4 : bv 32 := 0x1c863603.
Lemma F_781c4 : fetch_word BSEGS_I (0x781c4 : word) = Some W_781c4.
Proof. vm_refl. Qed.
Lemma D_781c4 : decode_any W_781c4 = Some (Load SZ8 true 12 12 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c8 : bv 32 := 0x000b2697.
Lemma F_781c8 : fetch_word BSEGS_I (0x781c8 : word) = Some W_781c8.
Proof. vm_refl. Qed.
Lemma D_781c8 : decode_any W_781c8 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781cc : bv 32 := 0x1c86b683.
Lemma F_781cc : fetch_word BSEGS_I (0x781cc : word) = Some W_781cc.
Proof. vm_refl. Qed.
Lemma D_781cc : decode_any W_781cc = Some (Load SZ8 true 13 13 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d0 : bv 32 := 0x00063783.
Lemma F_781d0 : fetch_word BSEGS_I (0x781d0 : word) = Some W_781d0.
Proof. vm_refl. Qed.
Lemma D_781d0 : decode_any W_781d0 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d4 : bv 32 := 0x0006b603.
Lemma F_781d4 : fetch_word BSEGS_I (0x781d4 : word) = Some W_781d4.
Proof. vm_refl. Qed.
Lemma D_781d4 : decode_any W_781d4 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d8 : bv 32 := 0xfff78713.
Lemma F_781d8 : fetch_word BSEGS_I (0x781d8 : word) = Some W_781d8.
Proof. vm_refl. Qed.
Lemma D_781d8 : decode_any W_781d8 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781dc : bv 32 := 0x01277463.
Lemma F_781dc : fetch_word BSEGS_I (0x781dc : word) = Some W_781dc.
Proof. vm_refl. Qed.
Lemma D_781dc : decode_any W_781dc = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e0 : bv 32 := 0x03267063.
Lemma F_781e0 : fetch_word BSEGS_I (0x781e0 : word) = Some W_781e0.
Proof. vm_refl. Qed.
Lemma D_781e0 : decode_any W_781e0 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e4 : bv 32 := 0x000b2697.
Lemma F_781e4 : fetch_word BSEGS_I (0x781e4 : word) = Some W_781e4.
Proof. vm_refl. Qed.
Lemma D_781e4 : decode_any W_781e4 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e8 : bv 32 := 0x1b46b683.
Lemma F_781e8 : fetch_word BSEGS_I (0x781e8 : word) = Some W_781e8.
Proof. vm_refl. Qed.
Lemma D_781e8 : decode_any W_781e8 = Some (Load SZ8 true 13 13 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781ec : bv 32 := 0x0006b883.
Lemma F_781ec : fetch_word BSEGS_I (0x781ec : word) = Some W_781ec.
Proof. vm_refl. Qed.
Lemma D_781ec : decode_any W_781ec = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781f0 : bv 32 := 0x0038d693.
Lemma F_781f0 : fetch_word BSEGS_I (0x781f0 : word) = Some W_781f0.
Proof. vm_refl. Qed.
Lemma D_781f0 : decode_any W_781f0 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781f4 : bv 32 := 0x00b68833.
Lemma F_781f4 : fetch_word BSEGS_I (0x781f4 : word) = Some W_781f4.
Proof. vm_refl. Qed.
Lemma D_781f4 : decode_any W_781f4 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781f8 : bv 32 := 0x1328e463.
Lemma F_781f8 : fetch_word BSEGS_I (0x781f8 : word) = Some W_781f8.
Proof. vm_refl. Qed.
Lemma D_781f8 : decode_any W_781f8 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781fc : bv 32 := 0x13287263.
Lemma F_781fc : fetch_word BSEGS_I (0x781fc : word) = Some W_781fc.
Proof. vm_refl. Qed.
Lemma D_781fc : decode_any W_781fc = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78200 : bv 32 := 0x23247863.
Lemma F_78200 : fetch_word BSEGS_I (0x78200 : word) = Some W_78200.
Proof. vm_refl. Qed.
Lemma D_78200 : decode_any W_78200 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78204 : bv 32 := 0x00740513.
Lemma F_78204 : fetch_word BSEGS_I (0x78204 : word) = Some W_78204.
Proof. vm_refl. Qed.
Lemma D_78204 : decode_any W_78204 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78208 : bv 32 := 0xff857513.
Lemma F_78208 : fetch_word BSEGS_I (0x78208 : word) = Some W_78208.
Proof. vm_refl. Qed.
Lemma D_78208 : decode_any W_78208 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7820c : bv 32 := 0xff897a13.
Lemma F_7820c : fetch_word BSEGS_I (0x7820c : word) = Some W_7820c.
Proof. vm_refl. Qed.
Lemma D_7820c : decode_any W_7820c = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78210 : bv 32 := 0xa91ff0ef.
Lemma F_78210 : fetch_word BSEGS_I (0x78210 : word) = Some W_78210.
Proof. vm_refl. Qed.
Lemma D_78210 : decode_any W_78210 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78214 : bv 32 := 0x00050993.
Lemma F_78214 : fetch_word BSEGS_I (0x78214 : word) = Some W_78214.
Proof. vm_refl. Qed.
Lemma D_78214 : decode_any W_78214 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78218 : bv 32 := 0x000a0513.
Lemma F_78218 : fetch_word BSEGS_I (0x78218 : word) = Some W_78218.
Proof. vm_refl. Qed.
Lemma D_78218 : decode_any W_78218 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7821c : bv 32 := 0xa85ff0ef.
Lemma F_7821c : fetch_word BSEGS_I (0x7821c : word) = Some W_7821c.
Proof. vm_refl. Qed.
Lemma D_7821c : decode_any W_7821c = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78220 : bv 32 := 0x000ab583.
Lemma F_78220 : fetch_word BSEGS_I (0x78220 : word) = Some W_78220.
Proof. vm_refl. Qed.
Lemma D_78220 : decode_any W_78220 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78224 : bv 32 := 0x00345613.
Lemma F_78224 : fetch_word BSEGS_I (0x78224 : word) = Some W_78224.
Proof. vm_refl. Qed.
Lemma D_78224 : decode_any W_78224 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78228 : bv 32 := 0x00c58633.
Lemma F_78228 : fetch_word BSEGS_I (0x78228 : word) = Some W_78228.
Proof. vm_refl. Qed.
Lemma D_78228 : decode_any W_78228 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7822c : bv 32 := 0x00060603.
Lemma F_7822c : fetch_word BSEGS_I (0x7822c : word) = Some W_7822c.
Proof. vm_refl. Qed.
Lemma D_7822c : decode_any W_7822c = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78230 : bv 32 := 0x00060663.
Lemma F_78230 : fetch_word BSEGS_I (0x78230 : word) = Some W_78230.
Proof. vm_refl. Qed.
Lemma D_78230 : decode_any W_78230 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78234 : bv 32 := 0x00747693.
Lemma F_78234 : fetch_word BSEGS_I (0x78234 : word) = Some W_78234.
Proof. vm_refl. Qed.
Lemma D_78234 : decode_any W_78234 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78238 : bv 32 := 0x02c6d063.
Lemma F_78238 : fetch_word BSEGS_I (0x78238 : word) = Some W_78238.
Proof. vm_refl. Qed.
Lemma D_78238 : decode_any W_78238 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7823c : bv 32 := 0xfff90913.
Lemma F_7823c : fetch_word BSEGS_I (0x7823c : word) = Some W_7823c.
Proof. vm_refl. Qed.
Lemma D_7823c : decode_any W_7823c = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78240 : bv 32 := 0x00395613.
Lemma F_78240 : fetch_word BSEGS_I (0x78240 : word) = Some W_78240.
Proof. vm_refl. Qed.
Lemma D_78240 : decode_any W_78240 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78244 : bv 32 := 0x00c585b3.
Lemma F_78244 : fetch_word BSEGS_I (0x78244 : word) = Some W_78244.
Proof. vm_refl. Qed.
Lemma D_78244 : decode_any W_78244 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78248 : bv 32 := 0x00058583.
Lemma F_78248 : fetch_word BSEGS_I (0x78248 : word) = Some W_78248.
Proof. vm_refl. Qed.
Lemma D_78248 : decode_any W_78248 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7824c : bv 32 := 0x04058263.
Lemma F_7824c : fetch_word BSEGS_I (0x7824c : word) = Some W_7824c.
Proof. vm_refl. Qed.
Lemma D_7824c : decode_any W_7824c = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78250 : bv 32 := 0x00797613.
Lemma F_78250 : fetch_word BSEGS_I (0x78250 : word) = Some W_78250.
Proof. vm_refl. Qed.
Lemma D_78250 : decode_any W_78250 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78254 : bv 32 := 0x02b64e63.
Lemma F_78254 : fetch_word BSEGS_I (0x78254 : word) = Some W_78254.
Proof. vm_refl. Qed.
Lemma D_78254 : decode_any W_78254 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78258 : bv 32 := 0x000ab503.
Lemma F_78258 : fetch_word BSEGS_I (0x78258 : word) = Some W_78258.
Proof. vm_refl. Qed.
Lemma D_78258 : decode_any W_78258 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7825c : bv 32 := 0x00040593.
Lemma F_7825c : fetch_word BSEGS_I (0x7825c : word) = Some W_7825c.
Proof. vm_refl. Qed.
Lemma D_7825c : decode_any W_7825c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78260 : bv 32 := 0x0140006f.
Lemma F_78260 : fetch_word BSEGS_I (0x78260 : word) = Some W_78260.
Proof. vm_refl. Qed.
Lemma D_78260 : decode_any W_78260 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78264 : bv 32 := 0x00140413.
Lemma F_78264 : fetch_word BSEGS_I (0x78264 : word) = Some W_78264.
Proof. vm_refl. Qed.
Lemma D_78264 : decode_any W_78264 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78268 : bv 32 := 0xfff48493.
Lemma F_78268 : fetch_word BSEGS_I (0x78268 : word) = Some W_78268.
Proof. vm_refl. Qed.
Lemma D_78268 : decode_any W_78268 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7826c : bv 32 := 0x00158593.
Lemma F_7826c : fetch_word BSEGS_I (0x7826c : word) = Some W_7826c.
Proof. vm_refl. Qed.
Lemma D_7826c : decode_any W_7826c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78270 : bv 32 := 0x1e048063.
Lemma F_78270 : fetch_word BSEGS_I (0x78270 : word) = Some W_78270.
Proof. vm_refl. Qed.
Lemma D_78270 : decode_any W_78270 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78274 : bv 32 := 0x00345613.
Lemma F_78274 : fetch_word BSEGS_I (0x78274 : word) = Some W_78274.
Proof. vm_refl. Qed.
Lemma D_78274 : decode_any W_78274 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78278 : bv 32 := 0x00c50633.
Lemma F_78278 : fetch_word BSEGS_I (0x78278 : word) = Some W_78278.
Proof. vm_refl. Qed.
Lemma D_78278 : decode_any W_78278 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7827c : bv 32 := 0x00060603.
Lemma F_7827c : fetch_word BSEGS_I (0x7827c : word) = Some W_7827c.
Proof. vm_refl. Qed.
Lemma D_7827c : decode_any W_7827c = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78280 : bv 32 := 0xfe0602e3.
Lemma F_78280 : fetch_word BSEGS_I (0x78280 : word) = Some W_78280.
Proof. vm_refl. Qed.
Lemma D_78280 : decode_any W_78280 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78284 : bv 32 := 0x0075f693.
Lemma F_78284 : fetch_word BSEGS_I (0x78284 : word) = Some W_78284.
Proof. vm_refl. Qed.
Lemma D_78284 : decode_any W_78284 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78288 : bv 32 := 0xfcc6cee3.
Lemma F_78288 : fetch_word BSEGS_I (0x78288 : word) = Some W_78288.
Proof. vm_refl. Qed.
Lemma D_78288 : decode_any W_78288 = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7828c : bv 32 := 0x01c0006f.
Lemma F_7828c : fetch_word BSEGS_I (0x7828c : word) = Some W_7828c.
Proof. vm_refl. Qed.
Lemma D_7828c : decode_any W_7828c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78290 : bv 32 := 0x00a9fa63.
Lemma F_78290 : fetch_word BSEGS_I (0x78290 : word) = Some W_78290.
Proof. vm_refl. Qed.
Lemma D_78290 : decode_any W_78290 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78294 : bv 32 := 0x413505b3.
Lemma F_78294 : fetch_word BSEGS_I (0x78294 : word) = Some W_78294.
Proof. vm_refl. Qed.
Lemma D_78294 : decode_any W_78294 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78298 : bv 32 := 0x00098513.
Lemma F_78298 : fetch_word BSEGS_I (0x78298 : word) = Some W_78298.
Proof. vm_refl. Qed.
Lemma D_78298 : decode_any W_78298 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7829c : bv 32 := 0x63d0f0ef.
Lemma F_7829c : fetch_word BSEGS_I (0x7829c : word) = Some W_7829c.
Proof. vm_refl. Qed.
Lemma D_7829c : decode_any W_7829c = Some (Jal 1 65084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782a0 : bv 32 := 0xfa050ce3.
Lemma F_782a0 : fetch_word BSEGS_I (0x782a0 : word) = Some W_782a0.
Proof. vm_refl. Qed.
Lemma D_782a0 : decode_any W_782a0 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782a4 : bv 32 := 0x00000413.
Lemma F_782a4 : fetch_word BSEGS_I (0x782a4 : word) = Some W_782a4.
Proof. vm_refl. Qed.
Lemma D_782a4 : decode_any W_782a4 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782a8 : bv 32 := 0x00040513.
Lemma F_782a8 : fetch_word BSEGS_I (0x782a8 : word) = Some W_782a8.
Proof. vm_refl. Qed.
Lemma D_782a8 : decode_any W_782a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782ac : bv 32 := 0x03813083.
Lemma F_782ac : fetch_word BSEGS_I (0x782ac : word) = Some W_782ac.
Proof. vm_refl. Qed.
Lemma D_782ac : decode_any W_782ac = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782b0 : bv 32 := 0x03013403.
Lemma F_782b0 : fetch_word BSEGS_I (0x782b0 : word) = Some W_782b0.
Proof. vm_refl. Qed.
Lemma D_782b0 : decode_any W_782b0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782b4 : bv 32 := 0x02813483.
Lemma F_782b4 : fetch_word BSEGS_I (0x782b4 : word) = Some W_782b4.
Proof. vm_refl. Qed.
Lemma D_782b4 : decode_any W_782b4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782b8 : bv 32 := 0x02013903.
Lemma F_782b8 : fetch_word BSEGS_I (0x782b8 : word) = Some W_782b8.
Proof. vm_refl. Qed.
Lemma D_782b8 : decode_any W_782b8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782bc : bv 32 := 0x01813983.
Lemma F_782bc : fetch_word BSEGS_I (0x782bc : word) = Some W_782bc.
Proof. vm_refl. Qed.
Lemma D_782bc : decode_any W_782bc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782c0 : bv 32 := 0x01013a03.
Lemma F_782c0 : fetch_word BSEGS_I (0x782c0 : word) = Some W_782c0.
Proof. vm_refl. Qed.
Lemma D_782c0 : decode_any W_782c0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782c4 : bv 32 := 0x00813a83.
Lemma F_782c4 : fetch_word BSEGS_I (0x782c4 : word) = Some W_782c4.
Proof. vm_refl. Qed.
Lemma D_782c4 : decode_any W_782c4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782c8 : bv 32 := 0x04010113.
Lemma F_782c8 : fetch_word BSEGS_I (0x782c8 : word) = Some W_782c8.
Proof. vm_refl. Qed.
Lemma D_782c8 : decode_any W_782c8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782cc : bv 32 := 0x00008067.
Lemma F_782cc : fetch_word BSEGS_I (0x782cc : word) = Some W_782cc.
Proof. vm_refl. Qed.
Lemma D_782cc : decode_any W_782cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_782d0 : bv 32 := 0x000b2297.
Lemma F_782d0 : fetch_word BSEGS_I (0x782d0 : word) = Some W_782d0.
Proof. vm_refl. Qed.
Lemma D_782d0 : decode_any W_782d0 = Some (Auipc 5 178, 4%Z).
Proof. vm_refl. Qed.
